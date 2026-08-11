//! Property-based laws over the real crate — including the Lean-compiled
//! replay kernel called through FFI (`Uwueave/Exec.lean` via `shim.c`).
//!
//! Discipline: no property re-implements the replay *decision* (timestamp
//! ordering, cycle-skip). Every property is a law — an equality between two
//! calls into the crate, or an invariant walk over the crate's own output.
//! The only reconstruction here is the acyclicity *walk* (follow the override
//! chain, falling back to the first weave parent when no override exists),
//! which is the reading direction the kernel's output contract defines.

use uwueave::{CausalWeave, EraEvent, EraGroup, EraRole, MoveLog, MoveOp, NodeId, OpOutcome, SeqCrdt};
use proptest::prelude::*;
use std::collections::BTreeSet;

type Weave = CausalWeave<Vec<u8>>;

// ---------------------------------------------------------------------------
// Generators
// ---------------------------------------------------------------------------

/// One planned insert. Parent picks are resolved modulo the number of nodes
/// present at apply time, so parents always exist — the API's invariant.
/// While the weave is empty the insert is necessarily a root.
#[derive(Debug, Clone)]
struct InsertPlan {
    parent_picks: Vec<usize>,
    contents: Vec<u8>,
}

fn insert_plan() -> impl Strategy<Value = InsertPlan> {
    (prop::collection::vec(any::<usize>(), 0..=3), prop::collection::vec(any::<u8>(), 0..6))
        .prop_map(|(parent_picks, contents)| InsertPlan { parent_picks, contents })
}

fn plan_seq(max: usize) -> impl Strategy<Value = Vec<InsertPlan>> {
    prop::collection::vec(insert_plan(), 0..=max)
}

fn apply_plans(w: &mut Weave, ids: &mut Vec<NodeId>, plans: &[InsertPlan]) {
    for p in plans {
        let parents: Vec<NodeId> = if ids.is_empty() {
            vec![]
        } else {
            p.parent_picks.iter().map(|k| ids[k % ids.len()]).collect()
        };
        let id = w.insert(parents, p.contents.clone()).expect("parents exist by construction");
        ids.push(id);
    }
}

/// Build a weave from a shared prefix plus a divergent suffix; two weaves
/// built from the same prefix overlap non-trivially, so merges are real work.
fn build_weave(prefix: &[InsertPlan], suffix: &[InsertPlan]) -> (Weave, Vec<NodeId>) {
    let mut w = Weave::new();
    let mut ids = Vec::new();
    apply_plans(&mut w, &mut ids, prefix);
    apply_plans(&mut w, &mut ids, suffix);
    (w, ids)
}

fn merged(a: &Weave, b: &Weave) -> Weave {
    let mut m = a.clone();
    m.merge(b).expect("API-built weaves are causally closed and collision-free");
    m
}

/// A node reference for a move op: usually a node of the weave, occasionally
/// an id this replica has never seen (replay must omit such ops).
#[derive(Debug, Clone)]
enum NodeSel {
    Known(usize),
    Unknown([u8; 32]),
}

fn node_sel() -> impl Strategy<Value = NodeSel> {
    prop_oneof![
        8 => any::<usize>().prop_map(NodeSel::Known),
        1 => any::<[u8; 32]>().prop_map(NodeSel::Unknown),
    ]
}

/// Small lamport/replica ranges force timestamp collisions, so the total
/// order's tie-breakers (replica, child, dest) actually arbitrate.
#[derive(Debug, Clone)]
struct OpSpec {
    lamport: u64,
    replica: u64,
    child: NodeSel,
    dest: Option<NodeSel>,
}

fn op_spec() -> impl Strategy<Value = OpSpec> {
    (0u64..6, 0u64..3, node_sel(), prop::option::of(node_sel()))
        .prop_map(|(lamport, replica, child, dest)| OpSpec { lamport, replica, child, dest })
}

fn resolve_sel(sel: &NodeSel, ids: &[NodeId]) -> NodeId {
    match sel {
        NodeSel::Known(k) if !ids.is_empty() => ids[k % ids.len()],
        NodeSel::Known(_) => [0xEE; 32], // empty weave: degrade to an unseen id
        NodeSel::Unknown(b) => *b,
    }
}

fn resolve_op(spec: &OpSpec, ids: &[NodeId]) -> MoveOp {
    MoveOp {
        lamport: spec.lamport,
        replica: spec.replica,
        child: resolve_sel(&spec.child, ids),
        dest: spec.dest.as_ref().map(|d| resolve_sel(d, ids)),
    }
}

// ---------------------------------------------------------------------------
// (a) CausalWeave merge laws
// ---------------------------------------------------------------------------

proptest! {
    /// merge is commutative on the full structure (nodes + derived indexes).
    #[test]
    fn merge_commutative(prefix in plan_seq(5), sa in plan_seq(5), sb in plan_seq(5)) {
        let (a, _) = build_weave(&prefix, &sa);
        let (b, _) = build_weave(&prefix, &sb);
        prop_assert_eq!(merged(&a, &b), merged(&b, &a));
    }

    /// merge is associative.
    #[test]
    fn merge_associative(
        prefix in plan_seq(4),
        sa in plan_seq(4),
        sb in plan_seq(4),
        sc in plan_seq(4),
    ) {
        let (a, _) = build_weave(&prefix, &sa);
        let (b, _) = build_weave(&prefix, &sb);
        let (c, _) = build_weave(&prefix, &sc);
        prop_assert_eq!(merged(&merged(&a, &b), &c), merged(&a, &merged(&b, &c)));
    }

    /// merge is idempotent: a ∪ a = a, and joining an already-joined delta
    /// changes nothing.
    #[test]
    fn merge_idempotent(prefix in plan_seq(5), sa in plan_seq(5), sb in plan_seq(5)) {
        let (a, _) = build_weave(&prefix, &sa);
        let (b, _) = build_weave(&prefix, &sb);
        prop_assert_eq!(merged(&a, &a), a.clone());
        let ab = merged(&a, &b);
        prop_assert_eq!(merged(&ab, &b), ab.clone());
        prop_assert_eq!(merged(&ab, &a), ab);
    }
}

// ---------------------------------------------------------------------------
// (b) groundedness under arbitrary merge sequences
// ---------------------------------------------------------------------------

proptest! {
    /// `grounded()` (every edge strictly descends in rank) holds after every
    /// step of an arbitrary sequence of cross-merges among three replicas.
    #[test]
    fn grounded_after_merge_sequences(
        prefix in plan_seq(4),
        sa in plan_seq(4),
        sb in plan_seq(4),
        sc in plan_seq(4),
        seq in prop::collection::vec((0usize..3, 0usize..3), 0..12),
    ) {
        let mut pool =
            vec![build_weave(&prefix, &sa).0, build_weave(&prefix, &sb).0, build_weave(&prefix, &sc).0];
        for w in &pool {
            prop_assert!(w.grounded());
        }
        for (t, s) in seq {
            let src = pool[s].clone();
            let before = pool[t].len();
            let stats = pool[t].merge(&src).expect("pool merges never refuse");
            prop_assert_eq!(stats.inserted + stats.already_present, src.len());
            prop_assert_eq!(pool[t].len(), before + stats.inserted);
            prop_assert!(pool[t].grounded(), "grounded broken after merge {} <- {}", t, s);
        }
    }
}

// ---------------------------------------------------------------------------
// (c) replay determinism & delivery-independence (Lean kernel, via FFI)
// ---------------------------------------------------------------------------

fn specs_orders(
    max: usize,
) -> impl Strategy<Value = (Vec<OpSpec>, Vec<OpSpec>, Vec<prop::sample::Index>)> {
    prop::collection::vec(op_spec(), 0..max).prop_flat_map(|specs| {
        (
            Just(specs.clone()),
            Just(specs).prop_shuffle(),
            prop::collection::vec(any::<prop::sample::Index>(), 0..4),
        )
    })
}

proptest! {
    /// The same op-set recorded in a different order, with redeliveries,
    /// yields the same log and the same Lean-kernel replay; and replaying
    /// twice yields the same bytes (no state leaks across FFI calls).
    #[test]
    fn replay_delivery_independent(
        plans in plan_seq(8),
        (specs, shuffled, dups) in specs_orders(12),
    ) {
        let (w, ids) = build_weave(&plans, &[]);
        let mut log_a = MoveLog::new();
        for s in &specs {
            log_a.record(resolve_op(s, &ids));
        }
        let mut log_b = MoveLog::new();
        for s in &shuffled {
            log_b.record(resolve_op(s, &ids));
        }
        if !specs.is_empty() {
            for d in &dups {
                log_b.record(resolve_op(&specs[d.index(specs.len())], &ids)); // redelivery
            }
        }
        prop_assert_eq!(&log_a, &log_b);
        let view = log_a.replay(&w);
        prop_assert_eq!(&view, &log_b.replay(&w));
        prop_assert_eq!(&view, &log_a.replay(&w), "replay must be deterministic call-to-call");
    }
}

// ---------------------------------------------------------------------------
// (d) replay view acyclicity (Lean kernel, via FFI)
// ---------------------------------------------------------------------------

proptest! {
    /// Following each node's effective-parent chain — the override from the
    /// kernel's view when present, the first weave parent otherwise — always
    /// terminates at a root without revisiting a node. This walks the
    /// kernel's *output*; the decision of which ops applied stays in Lean.
    #[test]
    fn replay_view_acyclic(
        plans in plan_seq(8),
        specs in prop::collection::vec(op_spec(), 0..16),
    ) {
        let (w, ids) = build_weave(&plans, &[]);
        let mut log = MoveLog::new();
        for s in &specs {
            log.record(resolve_op(s, &ids));
        }
        let view = log.replay(&w);
        for id in view.keys() {
            prop_assert!(w.contains(id), "view names a node outside the weave");
        }
        for node in w.nodes() {
            let mut seen = BTreeSet::new();
            let mut cur = node.id();
            loop {
                prop_assert!(seen.insert(cur), "cycle in the effective-parent view at {:?}", cur);
                cur = match view.get(&cur) {
                    Some(None) => break, // overridden to root
                    Some(Some(d)) => *d, // overridden under d
                    None => match w.get(&cur).and_then(|n| n.parents().first()) {
                        None => break, // structural root, no override
                        Some(p) => *p,
                    },
                };
            }
        }
    }
}

// ---------------------------------------------------------------------------
// (d2) trace completeness (Lean kernel v2 status block, via FFI)
// ---------------------------------------------------------------------------

proptest! {
    /// Format v2's per-op trace is total: `replay_traced` reports exactly one
    /// outcome for every op in the log — applied, or a named skip — its view
    /// agrees with `replay`, and the ops naming nodes this replica has not
    /// seen are exactly the omitted ones. (The *decision* of which sent ops
    /// applied stays in Lean; this walks only the report's coverage.)
    #[test]
    fn replay_trace_complete(
        plans in plan_seq(8),
        specs in prop::collection::vec(op_spec(), 0..16),
    ) {
        let (w, ids) = build_weave(&plans, &[]);
        let mut log = MoveLog::new();
        for s in &specs {
            log.record(resolve_op(s, &ids));
        }
        let traced = log.replay_traced(&w);
        prop_assert_eq!(&traced.view, &log.replay(&w));
        prop_assert_eq!(traced.outcomes.len(), log.len());
        let mut seen = BTreeSet::new();
        for (op, outcome) in &traced.outcomes {
            prop_assert!(seen.insert(*op), "one outcome per op, no duplicates");
            let resolvable = w.contains(&op.child)
                && op.dest.map(|d| w.contains(&d)).unwrap_or(true);
            match outcome {
                OpOutcome::OmittedUnknownNode =>
                    prop_assert!(!resolvable, "omitted ops are exactly the unresolvable ones"),
                _ => prop_assert!(resolvable, "sent ops name known nodes"),
            }
        }
    }
}

// ---------------------------------------------------------------------------
// (e) cross-replica convergence (weave + log + Lean kernel)
// ---------------------------------------------------------------------------

proptest! {
    /// Two replicas with divergent weaves and different (overlapping) op
    /// subsets exchange state both directions: the weaves converge, the logs
    /// converge, and the Lean-kernel replay of the converged pair agrees.
    #[test]
    fn cross_replica_convergence(
        prefix in plan_seq(4),
        sa in plan_seq(4),
        sb in plan_seq(4),
        specs in prop::collection::vec((op_spec(), 0usize..3), 0..14),
    ) {
        let (mut wa, ids_a) = build_weave(&prefix, &sa);
        let (mut wb, ids_b) = build_weave(&prefix, &sb);
        let mut la = MoveLog::new();
        let mut lb = MoveLog::new();
        for (s, side) in &specs {
            // Each replica records ops naming its own nodes; `2` = an op both
            // already saw (each resolving against its own view of the ids).
            match side {
                0 => la.record(resolve_op(s, &ids_a)),
                1 => lb.record(resolve_op(s, &ids_b)),
                _ => {
                    la.record(resolve_op(s, &ids_a));
                    lb.record(resolve_op(s, &ids_b));
                }
            }
        }
        // Exchange, both directions.
        wa.merge(&wb).expect("weave exchange a<-b");
        wb.merge(&wa).expect("weave exchange b<-a");
        let la_snapshot = la.clone();
        la.merge(&lb);
        lb.merge(&la_snapshot);
        prop_assert_eq!(&wa, &wb);
        prop_assert_eq!(&la, &lb);
        prop_assert_eq!(la.replay(&wa), lb.replay(&wb));
    }
}

// ---------------------------------------------------------------------------
// (f) sequence CRDT: merge laws + linearization determinism (Lean kernel)
// ---------------------------------------------------------------------------

/// One planned sequence edit. Anchor/delete picks are resolved modulo the ids
/// present at apply time, so anchors always exist — the API's invariant; an
/// insert with no pick (or an empty state) lands at the root.
#[derive(Debug, Clone)]
enum SeqEdit {
    Insert { anchor_pick: Option<usize>, contents: Vec<u8> },
    Delete { pick: usize },
}

fn seq_edit() -> impl Strategy<Value = SeqEdit> {
    prop_oneof![
        4 => (prop::option::of(any::<usize>()), prop::collection::vec(any::<u8>(), 0..4))
            .prop_map(|(anchor_pick, contents)| SeqEdit::Insert { anchor_pick, contents }),
        1 => any::<usize>().prop_map(|pick| SeqEdit::Delete { pick }),
    ]
}

fn apply_seq_edits(s: &mut SeqCrdt, ids: &mut Vec<NodeId>, edits: &[SeqEdit]) {
    for e in edits {
        match e {
            SeqEdit::Insert { anchor_pick, contents } => {
                let anchor = if ids.is_empty() {
                    None
                } else {
                    anchor_pick.map(|k| ids[k % ids.len()])
                };
                let id = s.insert(anchor, contents).expect("anchors exist by construction");
                ids.push(id);
            }
            SeqEdit::Delete { pick } => {
                if !ids.is_empty() {
                    s.delete(&ids[pick % ids.len()]).expect("ids exist by construction");
                }
            }
        }
    }
}

proptest! {
    /// Sequence-CRDT laws through the Lean kernel: merge of divergent
    /// replicas (shared prefix, concurrent suffixes with deletes) is
    /// commutative and idempotent on the full structure, the converged
    /// linearizations agree, and the linearization is deterministic
    /// call-to-call. (The *order decision* stays in Lean; this asserts only
    /// equalities between calls into the crate.)
    #[test]
    fn seq_merge_laws_and_linearization_determinism(
        prefix in prop::collection::vec(seq_edit(), 0..6),
        sa in prop::collection::vec(seq_edit(), 0..6),
        sb in prop::collection::vec(seq_edit(), 0..6),
    ) {
        let mut a = SeqCrdt::new();
        let mut ids_a = Vec::new();
        apply_seq_edits(&mut a, &mut ids_a, &prefix);
        let mut b = a.clone();
        let mut ids_b = ids_a.clone();
        apply_seq_edits(&mut a, &mut ids_a, &sa);
        apply_seq_edits(&mut b, &mut ids_b, &sb);

        let mut ab = a.clone();
        ab.merge(&b).expect("API-built states are anchor-closed and collision-free");
        let mut ba = b.clone();
        ba.merge(&a).expect("API-built states are anchor-closed and collision-free");
        prop_assert_eq!(&ab, &ba); // comm, full structure (incl. tombstones)
        prop_assert_eq!(ab.visible(), ba.visible()); // converged documents agree

        let mut aa = a.clone();
        aa.merge(&a).expect("self-merge never refuses");
        prop_assert_eq!(&aa, &a); // idem
        let mut abb = ab.clone();
        abb.merge(&b).expect("re-merge never refuses");
        prop_assert_eq!(&abb, &ab); // idem, delta-shaped

        prop_assert_eq!(a.visible(), a.visible()); // deterministic call-to-call
        prop_assert_eq!(ab.text(), ba.text()); // and the bytes agree too
    }
}

// ---------------------------------------------------------------------------
// (g) ERA: delivery-order independence of resolve (Lean kernel, via FFI)
// ---------------------------------------------------------------------------

/// Build one ERA event from a generated spec. Eids are the spec's position,
/// so they are distinct by construction — the eid-uniqueness premise
/// `era.rs` documents and enforces, satisfied the way a content address
/// would satisfy it. Small user/epoch ranges force real interaction (joins,
/// promotions of the same targets, duels); cut eids may name absent events
/// (they stay pending — the kernel totalizes).
fn era_event(eid: u64, kind: u64, actor: u64, target: u64, role_sel: u64) -> EraEvent {
    let role = match role_sel {
        0 => EraRole::Outsider,
        1 => EraRole::Reader,
        2 => EraRole::Writer,
        _ => EraRole::Admin,
    };
    match kind {
        0 => EraEvent::join(eid, actor),
        1 => EraEvent::write(eid, actor),
        2 => EraEvent::promote(eid, actor, target, role),
        _ => EraEvent::demote(eid, actor, target, role),
    }
}

#[allow(clippy::type_complexity)]
fn era_inputs() -> impl Strategy<
    Value = (Vec<EraEvent>, Vec<EraEvent>, Vec<(u64, u64)>, Vec<(u64, u64)>, Vec<prop::sample::Index>),
> {
    let events = prop::collection::vec((0u64..4, 0u64..4, 0u64..4, 0u64..4), 0..12).prop_map(
        |specs| {
            specs
                .into_iter()
                .enumerate()
                .map(|(i, (kind, actor, target, role_sel))| {
                    era_event(i as u64, kind, actor, target, role_sel)
                })
                .collect::<Vec<_>>()
        },
    );
    let cuts = prop::collection::vec((0u64..4, 0u64..16), 0..8);
    (events, cuts).prop_flat_map(|(evs, cuts)| {
        (
            Just(evs.clone()),
            Just(evs).prop_shuffle(),
            Just(cuts.clone()),
            Just(cuts).prop_shuffle(),
            prop::collection::vec(any::<prop::sample::Index>(), 0..4),
        )
    })
}

proptest! {
    /// The same event set and cut set, recorded in different orders with
    /// redeliveries, resolve identically through the Lean kernel — the two
    /// replicas' wire bytes really differ (arrival order is the transport),
    /// so the agreement is `EraKernel.eraReplay_same_sets` (riding
    /// `Era.resolve_same_sets` / `execOrder_same_sets` / `usersOf_same_sets`)
    /// exercised end-to-end through the FFI, view, roster and ✗ trace alike.
    #[test]
    fn era_resolve_delivery_order_independent(
        (evs, shuffled, cuts, cuts_shuffled, dups) in era_inputs(),
    ) {
        let mut a = EraGroup::new();
        for e in &evs {
            a.record(*e).expect("eids are distinct by construction");
        }
        for &(epoch, eid) in &cuts {
            a.record_cut(epoch, eid);
        }
        let mut b = EraGroup::new();
        for e in &shuffled {
            b.record(*e).expect("eids are distinct by construction");
        }
        if !evs.is_empty() {
            for d in &dups {
                // Redelivery of an identical event: idempotent by contract.
                b.record(evs[d.index(evs.len())]).expect("identical redelivery is Ok");
            }
        }
        for &(epoch, eid) in &cuts_shuffled {
            b.record_cut(epoch, eid);
            b.record_cut(epoch, eid); // cut redelivery is idempotent too
        }
        prop_assert_eq!(a.resolve(), b.resolve());
    }
}
