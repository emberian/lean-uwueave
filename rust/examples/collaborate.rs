//! **Two people building one document** — the composed [`Weave`], end to end.
//!
//! Ada and Grace share a research notebook. Both go offline; both add nodes,
//! both write prose into the *same* paragraph, both re-parent sections, and
//! one of them admits a third collaborator. Then they sync — in both
//! directions — and agree on every derived surface.
//!
//! ```sh
//! cargo run --example collaborate
//! ```
//!
//! The last section is the point of the example. Ada watches a move succeed
//! on her own screen; after the sync it has un-happened, because Grace's
//! *older* op won the replay order and Ada's would have closed a cycle. That
//! is `Move.view_not_stable` — a priced, documented anomaly of the op-log /
//! derived-view pattern, not a bug. It is priced because there is no cheaper
//! alternative: `Acyclicity.acyclicity_not_iconfluent` refutes replicated
//! mutable parents outright, so the choice is this anomaly or coordination.
//!
//! What makes it liveable is that it is *attributable*: the replay kernel
//! returns one [`OpOutcome`] per stored op, so the UI can say **which** edit
//! the sync retracted instead of silently redrawing the tree.

use uwueave::weave::{Capability, Weave, WeaveView};
use uwueave::{EraEvent, EraRole, MoveOp, NodeId, OpOutcome};

const ADA: u64 = 1;
const GRACE: u64 = 2;
const LIN: u64 = 3;
const HOPPER: u64 = 4;

type Doc = Weave<Vec<u8>>;

/// Six hex characters of a content address. Ids are `blake3(parents ‖
/// contents)`, so these are stable across runs and across machines — the
/// same node has the same short name on Ada's phone and Grace's laptop
/// without either of them agreeing to anything.
fn short(id: &NodeId) -> String {
    id[..3].iter().map(|b| format!("{b:02x}")).collect()
}

fn who(user: u64) -> &'static str {
    match user {
        ADA => "ada",
        GRACE => "grace",
        LIN => "lin",
        HOPPER => "hopper",
        _ => "?",
    }
}

fn rule(title: &str) {
    println!("\n━━ {title} ━━\n");
}

/// Render the document the way a tree widget would: depth-first from the
/// roots, siblings in id order.
///
/// Both of those are *arbitration*, not intention — the same choice
/// `SeqKernel` makes for text (`run_order_by_id`) — and the property that
/// earns them is that every replica holding the same state produces the same
/// walk.
fn print_tree(view: &WeaveView<'_, Vec<u8>>) {
    for node in &view.nodes {
        let indent = "  ".repeat(node.depth);
        let label = String::from_utf8_lossy(node.contents);
        let text = if node.text.is_empty() {
            String::new()
        } else {
            format!("   “{}”", String::from_utf8_lossy(&node.text))
        };
        println!("      {indent}{label}  [{}]{text}", short(&node.id));
    }
}

/// Print the replay kernel's verdict on every stored move op, in the order
/// the kernel sorted them: `(lamport, replica, child, dest, cite)`.
///
/// The arbitration is the timestamp, exactly and only — which is why an op
/// that arrives late can still be *early*.
fn print_replay(view: &WeaveView<'_, Vec<u8>>, name: impl Fn(&NodeId) -> String) {
    let mut ops: Vec<&(MoveOp, OpOutcome)> = view.replay.iter().collect();
    ops.sort_by_key(|(op, _)| (op.lamport, op.replica));
    for (op, outcome) in ops {
        let dest = match op.dest {
            None => "the root".to_string(),
            Some(d) => name(&d),
        };
        let verdict = match outcome {
            OpOutcome::Applied => "Applied",
            OpOutcome::SkippedCycle => "SkippedCycle   ← retroactively un-happened",
            OpOutcome::SkippedInvalid => "SkippedInvalid",
            OpOutcome::SkippedUnauthorised => "SkippedUnauthorised",
            OpOutcome::OmittedUnknownNode => "OmittedUnknownNode",
        };
        println!(
            "      t={:<3} {:<6} move {:<9} under {:<9}  {verdict}",
            op.lamport,
            who(op.replica),
            name(&op.child),
            dest
        );
    }
}

/// The document both replicas start from — including the genesis seam, which
/// is the zeroth coordination event: two replicas that disagree about it
/// cannot merge at all, and that is the correct answer rather than an
/// inconvenience.
fn genesis() -> (Doc, NodeId, NodeId, NodeId) {
    // 4096 bytes of storage each. The budget is the sum, and dividing it is
    // the seam (`Segmented.budget_segmented`) — see the two_phones example.
    let mut doc: Doc = Weave::new([(ADA, 4096), (GRACE, 4096)]);

    // Membership. `Era.lean` §1: any user may join, the first joiner becomes
    // Admin, later joiners are Readers, and an Admin may promote.
    for ev in [
        EraEvent::join(1, ADA),
        EraEvent::join(2, GRACE),
        EraEvent::promote(3, ADA, GRACE, EraRole::Writer),
    ] {
        doc.record_membership(ev).expect("fresh event ids, so no eid collision");
    }
    // The finality arbiter announces that events 1..3 lie in epoch 1's closed
    // past. Note what a cut is *not*: it does not decide anything. It only
    // orders, and every replica then executes the same canonical order
    // (`Era.resolve_same_sets`).
    for eid in 1..=3 {
        doc.record_cut(1, eid);
    }

    // Three nodes. Parents are fixed at creation — they are part of the id —
    // so this DAG cannot contain a cycle and no cycle check is ever run
    // (`Acyclicity.grounded_acyclic`).
    let notebook = doc.add_node(ADA, vec![], b"notebook".to_vec()).expect("ada is admin, 8 bytes");
    let intro =
        doc.add_node(ADA, vec![notebook], b"intro".to_vec()).expect("parent exists, 5 bytes");
    let method =
        doc.add_node(ADA, vec![notebook], b"method".to_vec()).expect("parent exists, 6 bytes");

    (doc, notebook, intro, method)
}

fn main() {
    println!("\nlean-uwueave — two people, one document");
    println!("══════════════════════════════════════");

    let (shared, notebook, intro, method) = genesis();

    // A naming table, so the output reads as prose rather than as hashes.
    let name = |id: &NodeId| -> String {
        for (candidate, label) in
            [(notebook, "notebook"), (intro, "intro"), (method, "method")]
        {
            if *id == candidate {
                return label.to_string();
            }
        }
        short(id)
    };

    rule("the shared starting point");
    println!("  membership, arbitrated by the ERA kernel:");
    for (user, role) in &shared.resolution().roles {
        println!("      {:<6} {:?}", who(*user), role);
    }
    println!("\n  the document:");
    print_tree(&shared.view());

    // -----------------------------------------------------------------
    // Both go offline.
    // -----------------------------------------------------------------

    let mut ada = shared.clone();
    let mut grace = shared.clone();

    rule("ada, on the train (offline)");

    let why = ada
        .add_node(ADA, vec![intro], b"why this matters".to_vec())
        .expect("intro exists here; 16 bytes fits her slice");
    println!("  + node  \"why this matters\"  under intro   [{}]", short(&why));

    // Text lives in a per-node sequence CRDT. `anchor = None` means "at the
    // start of this node's text"; chaining the second insert after the first
    // is how you write a run of prose that stays together.
    let first = ada
        .insert_text(ADA, intro, None, b"We set out to ")
        .expect("intro exists; 14 bytes fits");
    ada.insert_text(ADA, intro, Some(first), b"measure the thing.")
        .expect("anchor was just created; 18 bytes fits");
    println!("  + text  into intro: \"We set out to measure the thing.\"");

    // A move is *recorded*, not applied. The effective parent map is derived
    // at view time by the Lean replay kernel — which is the only shape that
    // survives, since replicated mutable parents are refuted outright.
    ada.move_node(ADA, 9, method, Some(intro)).expect("ada is a writer; both nodes exist");
    println!("  ~ move  method under intro                (lamport 9)");

    // Membership is grow-only like everything else; Ada can admit Lin without
    // asking Grace, and the arbitration will agree.
    ada.record_membership(EraEvent::join(10, LIN)).expect("eid 10 is fresh");
    println!("  + join  lin");

    println!("\n  On Ada's own screen, right now, her move is in effect:");
    let before = ada.view();
    println!(
        "      method's effective parent = {}",
        before.node(&method).map(|n| n.effective_parent.map(|p| name(&p)).unwrap_or_else(|| "the root".into())).unwrap_or_default()
    );

    rule("grace, in the lab (offline)");

    let apparatus = grace
        .add_node(GRACE, vec![method], b"apparatus".to_vec())
        .expect("method exists here; 9 bytes fits her slice");
    println!("  + node  \"apparatus\"  under method        [{}]", short(&apparatus));

    // The *same* anchor Ada used — `None`, the start of intro's text. Two
    // concurrent runs at one anchor is the case `Sequence.run_order_by_id`
    // prices: both survive, and their relative order is decided by content
    // address, which is nobody's intention and everybody's answer.
    grace.insert_text(GRACE, intro, None, b"Draft: ").expect("intro exists; 7 bytes fits");
    println!("  + text  into intro: \"Draft: \"          ← same anchor as ada's");

    // The older op. Grace's clock was behind; this is ordinary, not
    // pathological, and it is exactly what makes the next section happen.
    grace.move_node(GRACE, 4, intro, Some(method)).expect("grace is a writer; both nodes exist");
    println!("  ~ move  intro under method                (lamport 4)  ← OLDER than ada's");

    // Grace admits someone too. Ada admitted Lin; the two replicas therefore
    // learn their membership events in opposite orders, which is what makes
    // the "byte-identical / view-identical" contrast below a real measurement
    // rather than a claim.
    grace.record_membership(EraEvent::join(11, HOPPER)).expect("eid 11 is fresh");
    println!("  + join  hopper");

    // -----------------------------------------------------------------
    // The sync.
    // -----------------------------------------------------------------

    rule("they sync — in both directions");

    let mut ada_merged = ada.clone();
    ada_merged.merge(&grace).expect("same seam, both built by this API");
    let mut grace_merged = grace.clone();
    grace_merged.merge(&ada).expect("same seam, both built by this API");

    // The two replicas are NOT byte-equal: ERA keeps its substrates in
    // arrival order, and the arrivals differed. Equality of the *view* is the
    // convergence object, which is what `Era.resolve_same_sets` and
    // `GatedEra.ge_deterministic` are statements about.
    println!("  the two replicas hold identical STATE:  {}", ada_merged == grace_merged);
    println!("      (no — ada learned of hopper after lin, grace the other way round)");
    println!(
        "  their derived VIEWS are identical:      {}",
        ada_merged.view() == grace_merged.view()
    );
    println!("      (yes — and that is the theorem, not a coincidence)");

    let view = ada_merged.view();

    println!("\n  the agreed document:");
    print_tree(&view);

    println!("\n  membership, after the sync:");
    for (user, role) in &view.roles {
        println!("      {:<6} {:?}", who(*user), role);
    }
    println!("      (lin joined on ada's replica, hopper on grace's — both landed, both Readers)");

    println!("\n  intro's text, after two people wrote into the same anchor:");
    println!(
        "      “{}”",
        String::from_utf8_lossy(&view.node(&intro).map(|n| n.text.clone()).unwrap_or_default())
    );
    println!(
        "      both runs survived. their ORDER was decided by content address\n      \
         (`Sequence.run_order_by_id`) — arbitration, not intention, and the\n      \
         same arbitration at every replica."
    );

    // -----------------------------------------------------------------
    // The anomaly, named.
    // -----------------------------------------------------------------

    rule("⚠ the honest part: a move that un-happened");

    println!("  the replay kernel's verdict on every stored move op:\n");
    print_replay(&view, name);

    println!(
        "\n  Grace's op is older, so it sorts first and applies: intro moves under\n  \
         method. Ada's op then WOULD have moved method under intro — closing a\n  \
         cycle — so the replay skips it. Ada watched that move succeed on her\n  \
         own screen ten minutes ago."
    );
    println!(
        "\n      method's effective parent, on ada's phone before the sync:  {}",
        before
            .node(&method)
            .and_then(|n| n.effective_parent)
            .map(|p| name(&p))
            .unwrap_or_else(|| "the root".into())
    );
    println!(
        "      method's effective parent, after the sync:                  {}",
        view.node(&method)
            .and_then(|n| n.effective_parent)
            .map(|p| name(&p))
            .unwrap_or_else(|| "the root".into())
    );

    println!(
        "\n  This is `Move.view_not_stable`, and it is not a bug to be fixed: an\n  \
         op log whose view is derived by cycle-skipping replay is what you get\n  \
         once `acyclicity_not_iconfluent` has refuted replicated mutable\n  \
         parents. The alternative is coordination — a round trip before every\n  \
         drag-and-drop."
    );
    println!(
        "\n  What the kernel gives you back is ATTRIBUTION. The trace above names\n  \
         the exact op the sync retracted, so a UI can say “Grace's edit\n  \
         superseded your move” instead of quietly redrawing the tree."
    );

    // -----------------------------------------------------------------
    // The other gate, for contrast.
    // -----------------------------------------------------------------

    rule("for contrast: nothing here was denied");

    println!("  move ops the ROLE gate denied:  {}", view.denied_moves().count());
    println!("  (both authors were Writers when they moved. `cargo run --example gated`");
    println!("   is the same trace when authority is the thing that changes.)\n");
    println!("  lin may read:   {}", view.may(LIN, Capability::Read));
    println!("  lin may write:  {}   ← she joined after the promotion round", view.may(LIN, Capability::Write));
    println!();
}
