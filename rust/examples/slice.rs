//! **The vertical slice: an epistemic result, end to end, deliberately ugly.**
//!
//! ```sh
//! cargo run --example slice
//! ```
//!
//! codex's brief, verbatim: *"Do not wait for the final polished app. A
//! deliberately ugly but complete vertical slice will tell you whether the
//! language has the right intermediate representation."*
//!
//! So: a real [`Weave<String>`] on two replicas, a derived value computed from
//! it, that value carried as `Status` — the six-cell epistemic carrier from
//! `Uwueave/ResultStatus.lean` — rendered through `SemanticWidget`, the
//! intermediate contract from `Uwueave/RenderProgress.lean` §7, and printed as
//! plain `println!` boxes. Every state transition below names the theorem that
//! licenses the display.
//!
//! ⚠ **The Rust status layer is a hand transcription and nothing in it is
//! verified.** See the header of `src/status.rs` for the eight places it could
//! drift from the Lean. The Lean proofs license this design; they say nothing
//! about this code. What *is* Lean-authored here is what always was — the ERA
//! arbitration and the move replay behind `Weave::view()`.
//!
//! ## What the slice visits
//!
//! All six cells, in the order a real session produces them:
//!
//! | act | cell | what makes it that cell |
//! |---|---|---|
//! | 2 | `pending` | ada has asked her peer and nobody has answered |
//! | 3 | `provisional` | her own notes are scanned; grace is still owed |
//! | 4 | `exact` | the merge delivered grace's notes and closed her obligation |
//! | 5 | `forkedOpen` / `forkedClosed` | two replicas published **counts** instead of evidence |
//! | 6 | `absent` | a question with no answer and nobody left to ask |
//!
//! …and act 6 is where the loading-forever bug is built on purpose and caught.

use uwueave::status::{
    count_from_evidence, count_position, forget, honest_widget, loading, pending_sound,
    spinner_render, status_of, widget_of, widget_sound, Action, CandidatePresentation, Evidence,
    Finality, Plurality, Policy, SemanticWidget, Source, Status,
};
use uwueave::weave::Weave;
use uwueave::{EraEvent, EraRole, NodeId};

// ---------------------------------------------------------------------------
// The cast
// ---------------------------------------------------------------------------

/// Ada, in the weave's user space and in the evidence's source space. The two
/// happen to coincide here; nothing forces that, and a `Source` is deliberately
/// "anything that may still speak" rather than "a user".
const ADA: u64 = 1;
/// Grace — the peer whose silence is the whole of act 2.
const GRACE: u64 = 2;
/// The **local derivation** as a source. A recomputed count is attributed to the
/// machine that recomputed it, not to a peer: no peer ever said "five".
const DERIVED: Source = 9;

/// The word whose mentions we are counting.
const NEEDLE: &str = "weave";

type Doc = Weave<String>;

/// Ada's notes. Two of the three mention the needle.
const ADA_NOTES: &[&str] = &[
    "a weave merges without asking anyone",
    "grow-only sets are the free fragment",
    "every weave is a join-semilattice",
];

/// Grace's notes, all three mentioning the needle and none of them ada's.
const GRACE_NOTES: &[&str] = &[
    "the weave has six statuses, not five",
    "forks in a weave are shown, never collapsed",
    "a weave needs provenance to count",
];

/// The same three-note count for grace, but two of them are ada's notes **byte
/// for byte** — so the content-addressed store gives them the same id. This is
/// the second world of `no_count_merge_without_provenance`.
const GRACE_NOTES_OVERLAPPING: &[&str] = &[
    "a weave merges without asking anyone",
    "every weave is a join-semilattice",
    "a weave needs provenance to count",
];

// ---------------------------------------------------------------------------
// Ugly rendering. Plain println, no colour, no cleverness.
// ---------------------------------------------------------------------------

fn rule(title: &str) {
    println!("\n=================================================================");
    println!("  {title}");
    println!("=================================================================\n");
}

fn short(id: &NodeId) -> String {
    id[..3].iter().map(|b| format!("{b:02x}")).collect()
}

fn finality_str(f: Finality) -> &'static str {
    match f {
        Finality::Terminal => "terminal",
        Finality::Open => "open",
    }
}

fn plurality_str(p: Plurality) -> &'static str {
    match p {
        Plurality::Zero => "zero",
        Plurality::One => "one",
        Plurality::Many => "many",
    }
}

fn button_str(a: Option<Action>) -> String {
    match a {
        None => "(none - nothing to offer here)".to_string(),
        Some(x) => x.label().to_string(),
    }
}

/// **The whole UI.** A status becomes a `SemanticWidget` and the widget becomes
/// these lines. The renderer never sees the `Status` directly — that is the
/// point of interposing the contract (`RenderProgress.constant_widget_is_not_
/// honest`: a consumer into an arbitrary output type may be constant, a
/// consumer into `SemanticWidget` may not).
///
/// The fork is printed **as a fork**, every candidate with its source. There is
/// no branch anywhere in this function that picks one.
fn draw<T: std::fmt::Display>(label: &str, w: &SemanticWidget<T>, licence: &str) {
    /// Interior width of the ugly box.
    const W: usize = 66;
    let edge = || println!("  +{}+", "-".repeat(W));
    let row = |s: &str| println!("  |{s:<W$}|");

    edge();
    row(&format!(" {label}"));
    edge();
    row(&format!(
        "  finality : {:<12} plurality : {}",
        finality_str(w.finality),
        plurality_str(w.plurality)
    ));
    row(&format!(
        "  loading  : {}",
        if loading(w) { "YES  (*** spinner on screen ***)" } else { "no" }
    ));
    match &w.candidates {
        CandidatePresentation::Nothing => row("  shows    : (nothing)"),
        CandidatePresentation::Single(v) => row(&format!("  shows    : {v}")),
        CandidatePresentation::Several(cs) => {
            row("  shows    : A FORK - every candidate, none dropped:");
            for (v, src) in cs {
                row(&format!("             * {v}   (said by source {src})"));
            }
        }
    }
    row(&format!("  button   : {}", button_str(w.pending_action)));
    edge();
    println!("     licensed by: {licence}");
    println!();
}

// ---------------------------------------------------------------------------
// The document
// ---------------------------------------------------------------------------

/// Genesis, membership, and the root note. Every replica forks from this, so
/// they agree about the seam (`WeaveMergeError::SeamDisagreement` is what
/// disagreeing costs). The roles come out of the Lean ERA kernel.
fn genesis() -> (Doc, NodeId) {
    let mut doc: Doc = Weave::new([(ADA, 4096), (GRACE, 4096)]);
    for ev in [
        EraEvent::join(1, ADA),
        EraEvent::join(2, GRACE),
        EraEvent::promote(3, ADA, GRACE, EraRole::Writer),
    ] {
        doc.record_membership(ev).expect("fresh event ids, so no eid collision");
    }
    for eid in 1..=3 {
        doc.record_cut(1, eid);
    }
    let root = doc
        .add_node(ADA, vec![], "notebook".to_string())
        .expect("the first joiner is Admin, and 8 bytes fits a 4096-byte slice");
    (doc, root)
}

/// Add notes to a replica. Content-addressed, so identical bytes on two
/// replicas are **one** node — which is exactly what makes act 5's second world
/// possible.
fn write_notes(doc: &mut Doc, actor: u64, root: NodeId, notes: &[&str]) -> Vec<NodeId> {
    notes
        .iter()
        .map(|text| {
            doc.add_node(actor, vec![root], (*text).to_string())
                .expect("a promoted writer, and every note fits the slice")
        })
        .collect()
}

/// **The mention evidence's raw material** — read off the *real*
/// `Weave::view()`, whose node order and effective parents come from the Lean
/// replay kernel. Returns the short content addresses, which are stable across
/// replicas because they are hashes of the bytes.
fn scan(doc: &Doc, needle: &str) -> Vec<String> {
    doc.view().nodes.iter().filter(|n| n.contents.contains(needle)).map(|n| short(&n.id)).collect()
}

/// One replica's mentions, attributed to the source that saw them.
fn mentions_of(doc: &Doc, source: Source, needle: &str) -> Evidence<String> {
    let mut e: Evidence<String> = Evidence::new();
    for id in scan(doc, needle) {
        e.observe(id, source);
    }
    e
}

// ---------------------------------------------------------------------------
// The scenario
// ---------------------------------------------------------------------------

fn main() {
    println!("\nlean-uwueave - the vertical slice: an epistemic result, end to end");
    println!("(ugly on purpose; every box names the theorem that licenses it)");

    // -- act 1 -------------------------------------------------------------
    rule("ACT 1. two replicas of a real Weave<String>");

    let (shared, root) = genesis();
    let mut ada_doc = shared.clone();
    let mut grace_doc = shared.clone();

    let ada_ids = write_notes(&mut ada_doc, ADA, root, ADA_NOTES);
    let grace_ids = write_notes(&mut grace_doc, GRACE, root, GRACE_NOTES);

    println!("  ada, offline, writes {} notes:", ada_ids.len());
    for id in &ada_ids {
        match ada_doc.node(id) {
            Some(n) => println!("      [{}]  {}", short(id), n.contents()),
            None => println!("      [{}]  (missing)", short(id)),
        }
    }
    println!("\n  grace, offline, writes {} notes:", grace_ids.len());
    for id in &grace_ids {
        match grace_doc.node(id) {
            Some(n) => println!("      [{}]  {}", short(id), n.contents()),
            None => println!("      [{}]  (missing)", short(id)),
        }
    }

    // Ada's pre-merge replica, kept because provenance is about who saw what
    // *when they saw it*. After the merge her replica holds grace's notes too,
    // and attributing those to ada would be a lie the evidence carrier is
    // specifically built to prevent.
    let ada_before = ada_doc.clone();

    println!("\n  the question this slice answers, on ada's screen:");
    println!("      \"how many notes mention `{NEEDLE}`?\"");
    println!(
        "\n  A COUNT. `JoinHom.no_count_merge_without_provenance` classifies it\n  \
         `needsEvidence`: NO binary function on two counts is exact, because the\n  \
         pair (1,1) must answer 1 when the replicas saw the same note and 2 when\n  \
         they saw different ones. So the slice replicates the MENTION SET with\n  \
         attribution and recomputes the number. The number is never merged.\n  \
         Act 5 exhibits the two worlds that make that a theorem rather than a\n  \
         preference."
    );

    // -- act 2: PENDING ----------------------------------------------------
    rule("ACT 2. pending - ada has asked, and nobody has answered");

    // Two sources may still speak: ada's own scan (not run yet) and grace's
    // replica (not merged yet).
    let mut mentions: Evidence<String> = Evidence::new();
    mentions.owe(ADA).owe(GRACE);

    let cell = count_position(&mentions, DERIVED);
    println!("  mention evidence:  candidates {{}}   obligations {{ada, grace}}   certificates {{}}");
    println!("  count position  :  no candidate at all - NOT the number 0.");
    println!(
        "\n  Publishing `0` here would be `RenderSix.giveUpRender` at the count\n  \
         layer: the empty state asserted while a source is still owed. The count\n  \
         position holds no candidate until somebody has spoken.\n"
    );
    assert_eq!(status_of(&cell), Status::Pending, "nobody has spoken and grace is uncertified");
    draw(
        &format!("notes mentioning `{NEEDLE}`   [status: pending]"),
        &widget_of(status_of(&cell)),
        "RenderProgress.widgetOf - pending -> finality = open; honest_widget_loads_at_pending",
    );
    println!("  what this cell is waiting for: sources {:?}", cell.open_sources());
    println!(
        "\n  The button is `stop waiting`, not a promise about liveness. It is\n  \
         `RenderProgress.sealAll`: certify every source still owed. The candidate\n  \
         set is UNTOUCHED and the badge becomes `absent`. That move alone\n  \
         discharges the old `pending_escapable` clause\n  \
         (`statusOf_pending_escapable_by_sealing`), which is why that clause was\n  \
         never a liveness condition - a spinner satisfies it BY GIVING UP. This\n  \
         module carries truth and affordance and NOT progress: a `pending` cell\n  \
         here is not a promise that anything will ever arrive."
    );

    // -- act 3: PROVISIONAL ------------------------------------------------
    rule("ACT 3. provisional - ada's own notes are in; grace is still owed");

    mentions.merge(&mentions_of(&ada_before, ADA, NEEDLE));
    // Ada's local scan is complete: she will not find more in her own replica.
    // ⚠ A certificate is TRUSTED, not verified (`Evidence.lean`'s own boundary:
    // "`certify` adds one unconditionally"). Nothing here earns it.
    mentions.certify(ADA);

    let cell = count_position(&mentions, DERIVED);
    println!("  mention evidence, attributed:");
    for (id, src) in mentions.candidates() {
        println!("      [{id}]  seen by source {src}");
    }
    println!(
        "  obligations {:?}   certificates {:?}   closed? {}\n",
        mentions.obligations(),
        mentions.certificates(),
        mentions.is_closed()
    );
    assert_eq!(status_of(&cell), Status::Provisional(2), "ada saw two of her three notes match");
    draw(
        &format!("notes mentioning `{NEEDLE}`   [status: provisional]"),
        &widget_of(status_of(&cell)),
        "ResultStatus.statusOf_provisional - one candidate value, future OPEN",
    );
    println!(
        "  A number is on screen and it is not final. `ResultStatus.exact_does_not\n  \
         _strengthen` is why that is a cell rather than a bug: exactness weakens\n  \
         along future inclusion and does NOT run backwards, so `provisional`\n  \
         cannot be coerced up to `exact` by wishing."
    );

    // -- act 4: EXACT ------------------------------------------------------
    rule("ACT 4. exact - the merge delivers, and the obligation closes");

    let report = ada_doc.merge(&grace_doc).expect("both replicas forked from one seam");
    println!("  ada.merge(&grace) - the real Weave merge, through the real kernels:");
    println!("      nodes learned      : {}", report.nodes.inserted);
    println!("      membership events  : {}", report.membership.events_inserted);
    println!("      move ops learned   : {}", report.moves_learned);

    // The merge IS grace's delivery, so her obligation closes — and what she
    // contributes is attributed to HER, from her own replica, not to ada's
    // post-merge scan.
    mentions.merge(&mentions_of(&grace_doc, GRACE, NEEDLE));
    mentions.certify(GRACE);

    let cell = count_position(&mentions, DERIVED);
    println!("\n  mention evidence, merged and ATTRIBUTED:");
    for (id, src) in mentions.candidates() {
        let who = if *src == ADA { "ada" } else { "grace" };
        println!("      [{id}]  seen by {who}");
    }
    println!("  closed? {}\n", mentions.is_closed());
    assert_eq!(status_of(&cell), Status::Exact(5), "two of ada's plus three of grace's");
    draw(
        &format!("notes mentioning `{NEEDLE}`   [status: exact]"),
        &widget_of(status_of(&cell)),
        "ResultStatus.statusOf_exact - one value, roster closed; no button, nothing to await",
    );

    // The two architectures agree here, and the agreement is checkable rather
    // than asserted: merging the two replicas' evidence gives the same answer
    // as recomputing from the merged document.
    let recomputed = scan(&ada_doc, NEEDLE).len();
    println!(
        "  cross-check - merge-the-evidence vs recompute-from-the-merged-document:\n      \
         count_from_evidence(ada_evidence merge grace_evidence) = {}\n      \
         scan(ada_doc AFTER the real Weave merge)               = {}\n      \
         agree? {}",
        count_from_evidence(&mentions),
        recomputed,
        count_from_evidence(&mentions) == recomputed
    );
    println!(
        "\n  Note what merged and what did not. The MENTION SET merged (grow-only,\n  \
         attributed, union). The NUMBER was recomputed from it. That is `JoinHom`'s\n  \
         `ReplicatesEvidence` architecture, free for every interpreter with no\n  \
         hypothesis at all (`evidence_architecture_is_free`)."
    );

    // -- act 5: THE FORK ---------------------------------------------------
    rule("ACT 5. the fork - what replicating the NUMBER does instead");

    let ada_count = count_from_evidence(&mentions_of(&ada_before, ADA, NEEDLE));
    let grace_count = count_from_evidence(&mentions_of(&grace_doc, GRACE, NEEDLE));

    println!("  Suppose each replica had published its COUNT as a replicated value,");
    println!("  the way a naive summary cache does:\n");
    println!("      ada publishes   {ada_count}");
    println!("      grace publishes {grace_count}\n");

    let mut summary: Evidence<usize> = Evidence::new();
    summary.owe(ADA).owe(GRACE);
    summary.observe(ada_count, ADA);
    summary.observe(grace_count, GRACE);

    let forked_open = status_of(&summary);
    assert!(matches!(forked_open, Status::ForkedOpen(_)), "two values, nobody certified");
    draw(
        &format!("notes mentioning `{NEEDLE}` (summary-replicated)   [forkedOpen]"),
        &widget_of(forked_open),
        "ResultStatus.statusOf_forkedOpen - several candidates, future open",
    );

    summary.certify(ADA).certify(GRACE);
    let forked_closed = status_of(&summary);
    assert!(matches!(forked_closed, Status::ForkedClosed(_)), "both sources certified");
    draw(
        &format!("notes mentioning `{NEEDLE}` (summary-replicated)   [forkedClosed]"),
        &widget_of(forked_closed),
        "ResultStatus.statusOf_forkedClosed - waiting will NOT fix this one",
    );

    println!("  RESOLUTION. Three policies, on the same forked evidence. Each one");
    println!("  prints its own NAME and the alternatives it suppressed, because");
    println!("  `ResultStatus.resolved_value_is_not_a_function_of_the_evidence` says");
    println!("  a reader holding only the value can reconstruct neither:\n");
    for policy in [
        Policy::<usize>::by_source("bySource(ada)", ADA),
        Policy::<usize>::by_source("bySource(grace)", GRACE),
        Policy::<usize>::greatest("greatest"),
    ] {
        match policy.resolve(&summary) {
            Some(r) => {
                println!("      policy {:<18} -> {}", r.policy, r.value);
                println!(
                    "        suppressed, and RETAINED: {:?}",
                    r.alternatives.iter().filter(|(v, _)| *v != r.value).collect::<Vec<_>>()
                );
            }
            None => println!("      policy {:<18} -> declines (it names a source that never spoke)", policy.name),
        }
    }
    println!(
        "\n  And the status underneath is UNCHANGED - `resolution_leaves_the_status\n  \
         _alone`. A forkedClosed that ada's policy read as {ada_count} is still a\n  \
         forkedClosed: {}",
        status_of(&summary).name()
    );

    println!(
        "\n  ** the punchline **  The evidence-replicated answer is {}, and no policy\n  \
         over {{{ada_count}, {grace_count}}} could ever have produced it, because neither replica\n  \
         ever held it. Here is the pair of worlds that turns that from an anecdote\n  \
         into `no_count_merge_without_provenance`:",
        count_from_evidence(&mentions)
    );
    two_worlds();

    // -- act 6: ABSENT, and the loading-forever bug ------------------------
    rule("ACT 6. absent - and the loading-forever bug, built and caught");

    // A different question on the same document: "which note is pinned as the
    // summary of this notebook?" Nobody pinned one, and both replicas have
    // answered. There is no answer and there will not be one.
    let mut pin_evidence: Evidence<String> = Evidence::new();
    pin_evidence.owe(ADA).owe(GRACE);
    match ada_doc.seam().pin {
        Some(id) => {
            pin_evidence.observe(short(&id), ADA);
        }
        None => {}
    }
    pin_evidence.certify(ADA).certify(GRACE);

    println!("  a different question: \"which note is pinned as the summary?\"");
    println!("      candidates   : {:?}", pin_evidence.candidates());
    println!("      obligations  : {:?}", pin_evidence.obligations());
    println!("      certificates : {:?}", pin_evidence.certificates());
    println!("      closed?      : {}\n", pin_evidence.is_closed());

    let honest = status_of(&pin_evidence);
    assert_eq!(honest, Status::Absent, "no candidate, and every source certified");
    draw(
        "the pinned summary note   [status: absent]",
        &widget_of(honest.clone()),
        "RenderProgress.no_honest_widget_loads_at_absent - loading = false, BY THE INTERFACE",
    );
    println!(
        "  `ResultStatus.absence_outlives_exactness`: this is the MOST stable of\n  \
         the six cells. An `exact` report is retracted when a source nobody knew\n  \
         about is admitted; an `absent` one has no value to re-open.\n"
    );

    println!("  ---- now the bug, on purpose ----\n");
    println!("  `RenderSix.spinnerRender` is `statusOf` with definitive absence");
    println!("  re-badged as \"nothing observed yet\". It is the bug every app has");
    println!("  shipped, and it is NOT locally false: the answer set really is");
    println!("  empty. What is false is that waiting might help.\n");

    let lie = spinner_render(&pin_evidence);
    println!("      status_of(evidence)      = {}", honest.name());
    println!("      spinner_render(evidence) = {}   <-- the lie\n", lie.name());

    println!("  1. THE FIVE-CELL FOLD CANNOT SEE IT. `RenderSix.spinnerRender_folds");
    println!("     _to_render`: forgetting the zero-row split turns the lie back into");
    println!("     the sanctioned view, exactly.");
    println!("         forget(status_of(e))      = {:?}", forget(honest.clone()));
    println!("         forget(spinner_render(e)) = {:?}", forget(lie.clone()));
    println!(
        "         equal? {}   <-- the FIVE-status honesty predicate is SATISFIED by the spinner\n",
        forget(honest.clone()) == forget(lie.clone())
    );

    println!("  2. IT SPINS FOREVER. `spinnerRender_spins_forever`: the evidence is");
    println!("     closed, so every permitted (sealed) future is `absent` again and");
    println!("     the swap keeps re-badging it. The wait has NO end state.");
    for (name, future) in
        [("itself", pin_evidence.clone()), ("after `stop waiting`", pin_evidence.seal_all())]
    {
        println!(
            "         sealed future {:<22} -> spinner still says {:<8} (sealed? {})",
            name,
            spinner_render(&future).name(),
            pin_evidence.seals_to(&future)
        );
    }
    println!();

    println!("  3. THE EPISTEMIC CHECK CATCHES IT AT ONE STATE. `RenderProgress");
    println!("     .spinnerRender_is_not_pendingSound` needs NO future reasoning -");
    println!("     only the fact that this evidence is closed:");
    let states = [pin_evidence.clone()];
    println!("         pending_sound(status_of,      ..) = {:?}", pending_sound(status_of, &states));
    println!(
        "         pending_sound(spinner_render, ..) = {:?}\n",
        pending_sound(spinner_render, &states)
    );

    println!("  4. AND THE WIDGET LAYER REFUSES TO PAINT IT. This is the part that");
    println!("     makes the bug UNSHIPPABLE rather than merely detectable.");
    println!(
        "         honest_widget(widget_of)                    = {:?}",
        honest_widget(widget_of::<String>)
    );
    println!(
        "         widget_sound(widget_of . status_of,      ..) = {:?}",
        widget_sound(|e| widget_of(status_of(e)), &states)
    );
    println!(
        "         widget_sound(widget_of . spinner_render, ..) = {:?}\n",
        widget_sound(|e| widget_of(spinner_render(e)), &states)
    );
    println!("     Here is what the surface would have had to draw to tell the lie -");
    println!("     and it cannot, because the honest path never produces this widget:");
    draw(
        "the pinned summary note   [spinner_render: pending]",
        &widget_of(lie),
        "*** REFUSED *** by RenderProgress.WidgetSound at this one state (LoadsAtAbsent)",
    );
    println!(
        "  `no_honest_widget_loads_at_absent` is why: no assignment satisfying the\n  \
         interface can advertise loading = true at `absent`. The dishonest widget\n  \
         above exists in this program only because `spinner_render` was called by\n  \
         NAME. On the honest path - `widget_of(status_of(e))` - it is not\n  \
         reachable, and `constant_widget_is_not_honest` closes the other escape:\n  \
         one value cannot be both terminal and open, so a renderer cannot dodge\n  \
         the contract by ignoring its input."
    );

    // -- the honest limit --------------------------------------------------
    rule("THE LIMIT THAT SURVIVES - said plainly, not omitted");
    println!(
        "  `RenderProgress.salience_is_still_not_enforceable_after_the_widget`.\n  \
         The interface constrains the SEMANTIC layer. The last hop - widget to\n  \
         pixels - is still a function into an arbitrary type, and constant\n  \
         functions still exist. Six statuses, six DISTINCT widgets, and this\n  \
         renderer is free to paint them all the same:\n"
    );
    let all = [
        widget_of(Status::Exact(5usize)),
        widget_of(Status::Provisional(2usize)),
        widget_of(Status::ForkedClosed(vec![(2usize, ADA), (3usize, GRACE)])),
        widget_of(Status::ForkedOpen(vec![(2usize, ADA), (3usize, GRACE)])),
        widget_of(Status::<usize>::Absent),
        widget_of(Status::<usize>::Pending),
    ];
    let grey = |_w: &SemanticWidget<usize>| "#";
    println!(
        "      six distinct widgets, painted by a constant function: {}",
        all.iter().map(grey).collect::<Vec<_>>().join(" ")
    );
    println!(
        "\n  No interface reaches past its own output type, and this one does not\n  \
         either. What it DID buy: the widget layer can no longer SAY the result is\n  \
         still coming when it is not.\n"
    );

    println!("=================================================================");
    println!("  Everything above was computed. Nothing above was proved in Rust.");
    println!("  See src/status.rs's header for the eight ways it could drift.");
    println!("=================================================================\n");
}

/// **Two worlds with identical per-replica counts and different merged counts.**
///
/// `JoinHom.no_count_merge_without_provenance`, executed on the real
/// content-addressed store: in world B grace writes bytes ada already wrote, so
/// those are literally the same nodes (the id is `blake3(parents ‖ contents)`).
/// Her count is unchanged and the merged count is not.
fn two_worlds() {
    let world = |grace_notes: &[&str]| -> (usize, usize, usize) {
        let (shared, root) = genesis();
        let mut a = shared.clone();
        let mut g = shared.clone();
        write_notes(&mut a, ADA, root, ADA_NOTES);
        write_notes(&mut g, GRACE, root, grace_notes);
        let ea = mentions_of(&a, ADA, NEEDLE);
        let eg = mentions_of(&g, GRACE, NEEDLE);
        (count_from_evidence(&ea), count_from_evidence(&eg), count_from_evidence(&ea.merged(&eg)))
    };

    let (a1, g1, m1) = world(GRACE_NOTES);
    let (a2, g2, m2) = world(GRACE_NOTES_OVERLAPPING);
    assert_eq!((a1, g1), (a2, g2), "the two worlds must present the SAME input pair");
    assert_ne!(m1, m2, "…and different merged answers, or there is nothing to refute");
    println!();
    println!("      world A (grace's notes are all new)   : ada={a1}  grace={g1}  merged={m1}");
    println!("      world B (two of grace's ARE ada's)    : ada={a2}  grace={g2}  merged={m2}");
    println!(
        "      -> the input pair is ({a1},{g1}) in BOTH worlds and the answer is\n         \
         {m1} in one and {m2} in the other. So there is no m : Nat -> Nat -> Nat\n         \
         with m (count x) (count y) = count (x merge y). The count MUST carry its\n         \
         evidence. Not `should`: must."
    );
}
