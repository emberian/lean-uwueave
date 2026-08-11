//! ERA group management — epoch-resolved arbitration for duelling admins —
//! with the arbitration **authored in Lean and called through FFI**, not
//! re-implemented here.
//!
//! `Uwueave/Era.lean` in one paragraph: group-management operations (join /
//! write / promote / demote) genuinely do not commute — authorisation is
//! judged at the point of execution, so two admins demoting each other is a
//! conflict no coordination-free merge can resolve (`Authority.lean` proves
//! the fail-closed answer annihilates both). ERA's answer (Dougal, PaPoC
//! 2026): a trusted *finality arbiter* announces epoch cuts that only ORDER
//! events; every replica executes the canonicalised order, skipping
//! unauthorised events (the paper's ✗ marks), and the survivor is *derived*.
//! `resolve_same_sets` makes the outcome a function of the two SETS (events,
//! cuts) — delivery order, duplication and batching invisible — and
//! `duelling_admins_resolved` is the theorem the feature exists for: one
//! deterministic surviving admin at every replica.
//!
//! What this Rust file actually does is deliberately dumb: it keeps the two
//! grow-only substrates (events value-keyed by eid, the arbiter's cut
//! records), unions them at merge, encodes ERA FORMAT v1 request words, and
//! hands them to `Uwueave/EraKernel.lean`'s `uwueave_era_resolve` (compiled
//! to C by lake, linked by `build.rs`). The decisions — epoch assignment,
//! the execution order, authorisation, who survives — live in Lean, in one
//! place, next to their theorems. The kernel's decision layer is *literally*
//! `Era.resolve`; no second copy of the semantics exists on this side.
//!
//! ## Identity: the eid-uniqueness premise, and where it is enforced
//!
//! In the paper an event's id is its hash; in the miniature the caller
//! supplies the eid, and *uniqueness is the caller's contract* — the
//! content-addressing stand-in. `Era.lean` itself needs no uniqueness
//! premise (distinct events sharing an eid are still totally ordered), and
//! neither does the kernel; but this module keys events by eid and reads
//! the kernel's `(eid, status)` trace back by eid, so a duplicate eid with
//! *different content* would make attribution ambiguous and convergence
//! statements vacuous. It is therefore treated exactly like `causal.rs`'s
//! same-id-different-bytes encounter: **corruption, refused loudly** at
//! both [`EraGroup::record`] and [`EraGroup::merge`]
//! ([`EraRecordError::IdCollision`] / [`EraMergeError::IdCollision`]),
//! never deduplicated silently. Re-delivery of the *identical* event is
//! idempotent, as a CRDT substrate must be.
//!
//! ## Transport shape
//!
//! Both substrates are kept in **arrival order** (dup-free), matching
//! `Era.lean`'s list transport: `EraState` is a pair of grow-only sets, and
//! `encode_merge` shows list append IS the lattice join. Struct equality is
//! therefore transport-level (order-sensitive); the convergence claim is at
//! [`EraGroup::resolve`], where `resolve_same_sets` guarantees replicas
//! holding the same sets — in any order — get identical resolutions. The
//! property suite exercises exactly that through the FFI (the wire bytes
//! really differ between the two replicas; the Lean theorem is what makes
//! the answers agree). Unlike `movelog.rs`/`seq.rs` there is **no
//! groundedness assert** here: `Era.resolve` is total and its
//! delivery-independence theorems carry no precondition on the input sets.

use crate::ffi;
use std::collections::{BTreeMap, BTreeSet};

/// Role codes, `Era.lean` §1: `outsider` (not a member) plus the paper's
/// Reader < Writer < Admin.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum EraRole {
    Outsider,
    Reader,
    Writer,
    Admin,
}

impl EraRole {
    fn code(self) -> u64 {
        match self {
            EraRole::Outsider => 0,
            EraRole::Reader => 1,
            EraRole::Writer => 2,
            EraRole::Admin => 3,
        }
    }

    fn from_word(w: u64) -> Option<EraRole> {
        match w {
            0 => Some(EraRole::Outsider),
            1 => Some(EraRole::Reader),
            2 => Some(EraRole::Writer),
            3 => Some(EraRole::Admin),
            _ => None,
        }
    }
}

/// One group-management event — the wire quintuple of ERA FORMAT v1, built
/// only through the four constructors (`Era.lean`'s `joinEv`/`writeEv`/
/// `promoteEv`/`demoteEv` verbatim: join/write set `target = actor`,
/// `role = 0`).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub struct EraEvent {
    pub eid: u64,
    pub kind: u64,
    pub actor: u64,
    pub target: u64,
    pub role: u64,
}

impl EraEvent {
    /// `join(actor)` — any user may join; the first joiner becomes Admin,
    /// later joiners Readers (Era §1, op 1).
    pub fn join(eid: u64, actor: u64) -> Self {
        Self { eid, kind: 0, actor, target: actor, role: 0 }
    }

    /// `write(actor)` — requires Writer or Admin; no effect on roles.
    pub fn write(eid: u64, actor: u64) -> Self {
        Self { eid, kind: 1, actor, target: actor, role: 0 }
    }

    /// `promote(actor, target, role)` — actor must be Admin and the move
    /// must strictly raise the target.
    pub fn promote(eid: u64, actor: u64, target: u64, role: EraRole) -> Self {
        Self { eid, kind: 2, actor, target, role: role.code() }
    }

    /// `demote(actor, target, role)` — actor must be Admin and the move must
    /// strictly lower the target (self-demotion is valid; demotion to
    /// Outsider is expulsion).
    pub fn demote(eid: u64, actor: u64, target: u64, role: EraRole) -> Self {
        Self { eid, kind: 3, actor, target, role: role.code() }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EraRecordError {
    /// The eid is already recorded with different content — the
    /// eid-uniqueness premise (module docs) violated locally. Refused;
    /// re-recording the identical event is idempotent.
    IdCollision(u64),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EraMergeError {
    /// The same eid resolves to different events in the two states — the
    /// `causal.rs` `IdCollision` shape: after this no convergence statement
    /// holds, so the whole merge is refused rather than half-applied.
    IdCollision(u64),
}

/// Statistics from a merge, mostly for tests and telemetry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct EraMergeStats {
    pub events_inserted: usize,
    pub cuts_inserted: usize,
    pub already_present: usize,
}

/// The fate of one event in a resolution — the kernel's status words,
/// decoded (`EraKernel.lean` §3).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EraEventStatus {
    /// Authorised at its point of execution; it acted on the view.
    Applied,
    /// The paper's ✗ mark: a well-formed event refused at its point of
    /// execution (e.g. the second demote of a duel).
    SkippedUnauthorised,
    /// Unknown kind. The four constructors cannot produce one, so seeing
    /// this indicates an encoder bug — it is decoded, not hidden.
    SkippedInvalid,
}

/// A resolved group: `Era.resolve`'s view plus the kernel's trace.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct EraResolution {
    /// Has any join executed? (`GroupView.started`.)
    pub started: bool,
    /// The resolved role of every user named (as actor or target) by any
    /// recorded event — outsiders included: a user the group never admitted
    /// appears here as [`EraRole::Outsider`].
    pub roles: BTreeMap<u64, EraRole>,
    /// One `(eid, status)` per distinct event, in EXECUTION order — the
    /// arbitration order itself, observable.
    pub statuses: Vec<(u64, EraEventStatus)>,
}

/// The replicated ERA state: two grow-only substrates — the event set
/// (value-keyed by eid) and the arbiter's cut records — held in arrival
/// order, merged by union. `Era.lean`'s `EraState = GSet Cut × GSet Event`,
/// list-transported.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EraGroup {
    events: Vec<EraEvent>,
    by_eid: BTreeMap<u64, usize>,
    cuts: Vec<(u64, u64)>,
    cut_set: BTreeSet<(u64, u64)>,
}

impl EraGroup {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn events_len(&self) -> usize {
        self.events.len()
    }
    pub fn cuts_len(&self) -> usize {
        self.cuts.len()
    }
    pub fn is_empty(&self) -> bool {
        self.events.is_empty() && self.cuts.is_empty()
    }
    pub fn contains_event(&self, eid: u64) -> bool {
        self.by_eid.contains_key(&eid)
    }

    /// Record one event. Idempotent on the identical event; a known eid with
    /// different content is the eid-uniqueness premise violated — refused
    /// (module docs).
    pub fn record(&mut self, ev: EraEvent) -> Result<(), EraRecordError> {
        match self.by_eid.get(&ev.eid) {
            Some(&i) => {
                if self.events[i] == ev {
                    Ok(()) // identical redelivery: the substrate is a set
                } else {
                    Err(EraRecordError::IdCollision(ev.eid))
                }
            }
            None => {
                self.by_eid.insert(ev.eid, self.events.len());
                self.events.push(ev);
                Ok(())
            }
        }
    }

    /// Record one arbiter announcement: "event `eid` lies in epoch `epoch`'s
    /// closed past" (`Era.lean` §2's `Cut`). Idempotent and infallible —
    /// cuts are value-keyed pairs, so no collision is possible; even an
    /// equivocating arbiter (the same eid in two epochs) only re-orders
    /// deterministically, never diverges (`Era.lean`'s least-epoch rule).
    pub fn record_cut(&mut self, epoch: u64, eid: u64) {
        if self.cut_set.insert((epoch, eid)) {
            self.cuts.push((epoch, eid));
        }
    }

    /// The CRDT join: union both substrates (skip-if-present,
    /// verify-on-collision — the `causal.rs` shape). Validates before
    /// mutating: refuses wholesale rather than half-applying.
    pub fn merge(&mut self, other: &Self) -> Result<EraMergeStats, EraMergeError> {
        for ev in &other.events {
            if let Some(&i) = self.by_eid.get(&ev.eid) {
                if self.events[i] != *ev {
                    return Err(EraMergeError::IdCollision(ev.eid));
                }
            }
        }
        let mut stats = EraMergeStats::default();
        for ev in &other.events {
            if self.by_eid.contains_key(&ev.eid) {
                stats.already_present += 1;
            } else {
                self.by_eid.insert(ev.eid, self.events.len());
                self.events.push(*ev);
                stats.events_inserted += 1;
            }
        }
        for &(epoch, eid) in &other.cuts {
            if self.cut_set.insert((epoch, eid)) {
                self.cuts.push((epoch, eid));
                stats.cuts_inserted += 1;
            } else {
                stats.already_present += 1;
            }
        }
        Ok(stats)
    }

    /// Resolve the group via the Lean kernel (`Uwueave/EraKernel.lean`, ERA
    /// FORMAT v1): the resolved view (started flag + every named user's
    /// role) and one status per distinct event in execution order. The
    /// request carries both substrates in arrival order — the kernel's
    /// `resolve_same_sets` is what makes replicas with the same sets (any
    /// order) agree, and `eraReplay_same_sets` lifts that to the bytes.
    pub fn resolve(&self) -> EraResolution {
        let nc = self.cuts.len();
        let ne = self.events.len();
        let mut words: Vec<u64> = Vec::with_capacity(2 + 2 * nc + 5 * ne);
        words.push(nc as u64);
        words.push(ne as u64);
        for &(epoch, eid) in &self.cuts {
            words.push(epoch);
            words.push(eid);
        }
        for e in &self.events {
            words.extend_from_slice(&[e.eid, e.kind, e.actor, e.target, e.role]);
        }
        let bytes: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();

        let out = ffi::era_kernel(&bytes);

        // ERA FORMAT v1 response: three header words, then 2·nu role words,
        // then 2·ns status words — sizes proved Lean-side (`size_eraReplay`).
        // Anything else means the two sides disagree about the wire format —
        // refuse rather than reinterpret.
        assert!(
            out.len() >= 24 && out.len() % 8 == 0,
            "kernel response is not ERA format v1 (short or ragged)"
        );
        let resp: Vec<u64> =
            out.chunks_exact(8).map(|c| u64::from_le_bytes(c.try_into().unwrap())).collect();
        let started = match resp[0] {
            0 => false,
            1 => true,
            w => panic!("started word {w} — kernel speaks a newer format"),
        };
        let nu = resp[1] as usize;
        let ns = resp[2] as usize;
        assert_eq!(
            resp.len(),
            3 + 2 * nu + 2 * ns,
            "kernel response is not ERA format v1 (expected 3 + 2*nu + 2*ns words)"
        );
        let mut roles = BTreeMap::new();
        for i in 0..nu {
            let user = resp[3 + 2 * i];
            let role = resp[3 + 2 * i + 1];
            let role = EraRole::from_word(role)
                .unwrap_or_else(|| panic!("role word {role} — kernel speaks a newer format"));
            roles.insert(user, role);
        }
        let mut statuses = Vec::with_capacity(ns);
        for j in 0..ns {
            let eid = resp[3 + 2 * nu + 2 * j];
            let status = match resp[3 + 2 * nu + 2 * j + 1] {
                0 => EraEventStatus::Applied,
                1 => EraEventStatus::SkippedUnauthorised,
                2 => EraEventStatus::SkippedInvalid,
                v => panic!("unknown status word {v} — kernel speaks a newer format"),
            };
            statuses.push((eid, status));
        }
        EraResolution { started, roles, statuses }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    const ALICE: u64 = 1;
    const BOB: u64 = 2;

    /// `Era.lean`'s Fig. 2 history: both join, Alice promotes Bob to Admin,
    /// then the concurrent mutual demotes (eids 1..5, as in `Era.duelLog`).
    fn duel_events() -> [EraEvent; 5] {
        [
            EraEvent::join(1, ALICE),
            EraEvent::join(2, BOB),
            EraEvent::promote(3, ALICE, BOB, EraRole::Admin),
            EraEvent::demote(4, ALICE, BOB, EraRole::Reader),
            EraEvent::demote(5, BOB, ALICE, EraRole::Reader),
        ]
    }

    /// `Era.setupCuts`: epoch 1 holds the settled setup; the duel is pending.
    fn record_setup_cuts(g: &mut EraGroup) {
        g.record_cut(1, 1);
        g.record_cut(1, 2);
        g.record_cut(1, 3);
    }

    /// `Era.duelling_admins_resolved`, through the real kernel: two replicas
    /// each see the shared history plus *their own* demote, in different
    /// record orders; after both merge directions the wire bytes still
    /// differ (arrival order is transport, not meaning), yet both resolve to
    /// the SAME view — one deterministic survivor, Alice Admin, Bob demoted
    /// to Reader.
    #[test]
    fn duelling_admins_one_survivor_both_directions() {
        let [e1, e2, e3, e4, e5] = duel_events();
        let mut a = EraGroup::new();
        for e in [e1, e2, e3, e4] {
            a.record(e).unwrap();
        }
        record_setup_cuts(&mut a);
        let mut b = EraGroup::new();
        for e in [e2, e1, e3, e5] {
            b.record(e).unwrap();
        }

        let mut ab = a.clone();
        ab.merge(&b).unwrap();
        let mut ba = b.clone();
        ba.merge(&a).unwrap();
        assert_ne!(ab, ba, "transport orders differ — the agreement below is the theorem");
        let rab = ab.resolve();
        let rba = ba.resolve();
        assert_eq!(rab, rba, "both merge directions resolve identically");

        assert!(rab.started);
        assert_eq!(rab.roles.get(&ALICE), Some(&EraRole::Admin), "one survivor");
        assert_eq!(rab.roles.get(&BOB), Some(&EraRole::Reader), "the other demoted");
    }

    /// `Era.duel_finalised_verdict` and the epoch-3 example: the arbiter
    /// never names a winner — one more cut record flips the survivor, and
    /// finalising the loser's demote into a LATER epoch does not flip it
    /// back (earlier epoch executes first).
    #[test]
    fn epoch_advance_flips_the_survivor() {
        let mut g = EraGroup::new();
        for e in duel_events() {
            g.record(e).unwrap();
        }
        record_setup_cuts(&mut g);
        let pending = g.resolve();
        assert_eq!(pending.roles.get(&ALICE), Some(&EraRole::Admin));
        assert_eq!(pending.roles.get(&BOB), Some(&EraRole::Reader));

        // `Era.laterCuts`: e5 finalised into epoch 2 while e4 stays pending —
        // e5 executes first, and the verdict flips.
        g.record_cut(2, 5);
        let flipped = g.resolve();
        assert_eq!(flipped.roles.get(&ALICE), Some(&EraRole::Reader), "survivor flipped");
        assert_eq!(flipped.roles.get(&BOB), Some(&EraRole::Admin));

        // The epoch-3 example: e4 finalised too, but later — epoch order
        // outranks everything the events carry, so the verdict stands.
        g.record_cut(3, 4);
        let still = g.resolve();
        assert_eq!(still.roles.get(&ALICE), Some(&EraRole::Reader));
        assert_eq!(still.roles.get(&BOB), Some(&EraRole::Admin));
    }

    /// The ✗ marks are observable: in the pending duel the second demote is
    /// skipped-unauthorised at its point of execution, and a write by a
    /// never-joined user is refused too — while the roster still names the
    /// outsider. The statuses arrive in execution order (epoch 1 first,
    /// pending by eid after).
    #[test]
    fn unauthorised_event_shows_its_cross() {
        const CAROL: u64 = 3;
        let mut g = EraGroup::new();
        for e in duel_events() {
            g.record(e).unwrap();
        }
        g.record(EraEvent::write(9, CAROL)).unwrap();
        record_setup_cuts(&mut g);
        let r = g.resolve();
        use EraEventStatus::*;
        assert_eq!(
            r.statuses,
            vec![
                (1, Applied),
                (2, Applied),
                (3, Applied),
                (4, Applied),
                (5, SkippedUnauthorised),
                (9, SkippedUnauthorised),
            ],
            "execution order with the two ✗ marks named"
        );
        assert_eq!(r.roles.get(&CAROL), Some(&EraRole::Outsider), "named, never admitted");
    }

    /// Merge laws at the two honest levels: idempotence is structural
    /// (skip-if-present appends nothing), commutativity is at `resolve`
    /// (arrival orders differ; `resolve_same_sets` makes the answers agree).
    #[test]
    fn merge_idempotent_and_resolve_commutative() {
        let [e1, e2, e3, e4, e5] = duel_events();
        let mut a = EraGroup::new();
        for e in [e1, e3, e4] {
            a.record(e).unwrap();
        }
        a.record_cut(1, 1);
        let mut b = EraGroup::new();
        for e in [e5, e2, e1] {
            b.record(e).unwrap();
        }
        b.record_cut(1, 2);
        b.record_cut(1, 1);

        let mut aa = a.clone();
        let stats = aa.merge(&a).unwrap();
        assert_eq!(aa, a, "self-merge is a no-op");
        assert_eq!(stats.events_inserted + stats.cuts_inserted, 0);

        let mut ab = a.clone();
        ab.merge(&b).unwrap();
        let mut ba = b.clone();
        ba.merge(&a).unwrap();
        assert_eq!(ab.resolve(), ba.resolve(), "merge commutes at the resolution");

        let mut abb = ab.clone();
        abb.merge(&b).unwrap();
        assert_eq!(abb, ab, "re-merging a joined delta is a no-op");
    }

    /// The eid-uniqueness premise, enforced: the same eid with different
    /// content refuses at record and at merge (`IdCollision`, `causal.rs`
    /// shape); the identical event re-records idempotently.
    #[test]
    fn eid_collision_refused() {
        let mut a = EraGroup::new();
        a.record(EraEvent::join(7, ALICE)).unwrap();
        a.record(EraEvent::join(7, ALICE)).unwrap(); // identical: idempotent
        assert_eq!(a.events_len(), 1);
        assert_eq!(
            a.record(EraEvent::write(7, BOB)),
            Err(EraRecordError::IdCollision(7))
        );

        let mut b = EraGroup::new();
        b.record(EraEvent::write(7, BOB)).unwrap();
        let mut target = a.clone();
        assert_eq!(target.merge(&b), Err(EraMergeError::IdCollision(7)));
        assert_eq!(target, a, "refused wholesale, nothing half-applied");
    }
}
