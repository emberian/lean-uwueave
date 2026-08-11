//! **Authority: issue, delegate, exercise, revoke — and watch the data stay.**
//!
//! ```sh
//! cargo run --example gated
//! ```
//!
//! A move op in this crate cites the grant whose authority it exercises, and
//! the Lean replay kernel decides — inside the kernel, ahead of its sort —
//! whether that grant is still live. `Uwueave/Gated.lean` §5 proves that
//! in-kernel gate agrees with the abstract `gatedOps` model, so the gate this
//! example exercises is the gate the theorems are about.
//!
//! The thing to watch for is what a revocation *does not* do. It does not
//! delete anything. The op stays in the log, merges like any other datum, and
//! is still there to be enumerated and explained — it is simply not in the
//! view. **The gate is a view, not a filter on storage**, and every merge in
//! this example only ever adds.
//!
//! Three acts:
//!
//! 1. a delegation chain (owner → phone → scanner bot), with the bot's grant
//!    *attenuated* so part of the document is out of its reach;
//! 2. the owner revokes the phone — and the bot's grant dies too, although
//!    nobody revoked it, because revocation cascades down the chain;
//! 3. the surprise: removing authority can ADD a move to the view.

use uwueave::{CausalWeave, Grant, MoveLog, MoveOp, NodeId, OpOutcome, TracedReplay};

/// Replica ids. In this crate a move op's actor *is* its replica field, so
/// these double as "who did it".
const LAPTOP: u64 = 1;
const PHONE: u64 = 10;
const BOT: u64 = 20;

/// Grant ids. Well-formedness requires `parent < id`, and `0` is never a
/// valid grant — it is the null citation an op that names no authority
/// carries, and such an op never replays. There is no ungated path.
const OWNER_KEY: u64 = 1;
const PHONE_KEY: u64 = 2;
const BOT_KEY: u64 = 3;

fn short(id: &NodeId) -> String {
    id[..3].iter().map(|b| format!("{b:02x}")).collect()
}

fn rule(title: &str) {
    println!("\n━━ {title} ━━\n");
}

/// The document: four top-level folders, content-addressed.
///
/// Their order in the store — and therefore their *index*, which is what a
/// grant's scope is measured in — is by content address, not by the order
/// they were created in. That is the ⚠ in `movelog`'s module header made
/// visible: scope lives in the request's dense index space.
fn folders() -> (CausalWeave<Vec<u8>>, Vec<(String, NodeId)>) {
    let mut weave: CausalWeave<Vec<u8>> = CausalWeave::new();
    for label in ["inbox", "drafts", "archive", "trash"] {
        weave.insert(vec![], label.as_bytes().to_vec()).expect("a root node has no parents");
    }
    // `nodes()` iterates in ascending content-address order, which is exactly
    // the indexing the request encoder uses. Two replicas holding the same
    // weave therefore agree about every index without exchanging a word.
    let table: Vec<(String, NodeId)> = weave
        .nodes()
        .map(|n| (String::from_utf8_lossy(n.contents()).into_owned(), n.id()))
        .collect();
    (weave, table)
}

/// Print one traced replay as a table: every stored op, in the kernel's sort
/// order, with the verdict and — where there is one — the reason.
fn print_trace(traced: &TracedReplay, name: impl Fn(&NodeId) -> String) {
    for (op, outcome) in &traced.outcomes {
        let dest = match op.dest {
            None => "the root".to_string(),
            Some(d) => name(&d),
        };
        let actor = match op.replica {
            LAPTOP => "laptop",
            PHONE => "phone",
            BOT => "bot",
            _ => "?",
        };
        let verdict = match outcome {
            OpOutcome::Applied => "Applied",
            OpOutcome::SkippedCycle => "SkippedCycle",
            OpOutcome::SkippedInvalid => "SkippedInvalid",
            OpOutcome::SkippedUnauthorised => "SkippedUnauthorised",
            OpOutcome::OmittedUnknownNode => "OmittedUnknownNode",
        };
        println!(
            "      t={:<3} {:<7} move {:<8} under {:<8}  cites g{}   {verdict}",
            op.lamport, actor, name(&op.child), dest, op.cite
        );
    }
}

/// The effective parent overrides the replay produced — i.e. what actually
/// moved.
fn print_view(traced: &TracedReplay, name: impl Fn(&NodeId) -> String) {
    if traced.view.is_empty() {
        println!("      (empty — no move is in effect)");
        return;
    }
    for (child, parent) in &traced.view {
        let dest = match parent {
            None => "the root".to_string(),
            Some(p) => name(p),
        };
        println!("      {} is now under {}", name(child), dest);
    }
}

fn main() {
    println!("\nlean-uwueave — authority, and what a revocation does not delete");
    println!("══════════════════════════════════════════════════════════════");

    let (weave, table) = folders();
    let name = {
        let table = table.clone();
        move |id: &NodeId| -> String {
            table
                .iter()
                .find(|(_, nid)| nid == id)
                .map(|(label, _)| label.clone())
                .unwrap_or_else(|| short(id))
        }
    };

    // -----------------------------------------------------------------
    rule("the substrate, and the index space grants talk about");

    for (i, (label, id)) in table.iter().enumerate() {
        println!("      index {i}   {label:<8} [{}]", short(id));
    }
    println!(
        "\n  ⚠ A grant's scope is a CEILING ON THAT INDEX — scope σ covers the ops\n  \
         whose child index is < σ. The indexing is a function of the weave\n  \
         (ascending content address), so replicas agree about coverage exactly\n  \
         when their weaves agree. `Grant::universal` is the honest \"no\n  \
         attenuation\" grant for callers who do not want that coupling."
    );

    // Names for the two folders the bot will be able to touch, and one it
    // will not — read off the measured table rather than assumed.
    let bot_scope: u64 = 2;
    let covered = table[0].1;
    let covered_dest = table[1].1;
    let uncovered_index = 3;
    let uncovered = table[uncovered_index].1;

    // -----------------------------------------------------------------
    rule("the delegation chain");

    let mut phone_log = MoveLog::new();
    // The root of authority. `parent == 0` means "issued by the root
    // authority"; nothing in this crate checks that the issuer actually held
    // the parent grant — that is a signature, and signatures are a stated
    // premise (`Gated.lean`'s honest boundary), not something this code
    // enforces.
    phone_log.issue(Grant::universal(OWNER_KEY));
    // The owner delegates to a phone, unattenuated.
    phone_log.issue(Grant::delegate(PHONE_KEY, OWNER_KEY, u64::MAX));
    // The phone delegates to a scanner bot, NARROWED: indices 0..1 only.
    phone_log.issue(Grant::delegate(BOT_KEY, PHONE_KEY, bot_scope));

    println!("      g{OWNER_KEY}  issued by the root   scope ∞    the owner's laptop key");
    println!("      g{PHONE_KEY}  issued under g{OWNER_KEY}      scope ∞    the phone");
    println!(
        "      g{BOT_KEY}  issued under g{PHONE_KEY}      scope {bot_scope}    the scanner bot — \
         attenuated to indices 0..{}",
        bot_scope - 1
    );
    println!(
        "\n  Issuing is coordination-free (`Authority.wf_iconfluent`): grants are a\n  \
         grow-only set, so a delegation made offline is just another datum."
    );

    // -----------------------------------------------------------------
    rule("work, under that authority");

    // The phone moves a folder, citing its own key.
    let phone_move =
        MoveOp { lamport: 1, replica: PHONE, child: table[2].1, dest: Some(table[1].1), cite: PHONE_KEY };
    // The bot moves a folder inside its scope, citing the narrowed key.
    let bot_move =
        MoveOp { lamport: 2, replica: BOT, child: covered, dest: Some(covered_dest), cite: BOT_KEY };
    // ...and one outside it. Same bot, same key, one index too far.
    let bot_overreach =
        MoveOp { lamport: 3, replica: BOT, child: uncovered, dest: Some(covered_dest), cite: BOT_KEY };

    for op in [phone_move, bot_move, bot_overreach] {
        phone_log.record(op);
    }

    let before = phone_log.replay_traced(&weave);
    println!("  the kernel's verdict, op by op:\n");
    print_trace(&before, &name);
    println!(
        "\n      ^ the last one is attenuation biting: {} sits at index {uncovered_index},\n        \
         and the bot's grant covers only indices below {bot_scope}. Same bot,\n        \
         same key, one folder too far.",
        name(&uncovered),
    );

    println!("\n  what is in effect:");
    print_view(&before, &name);

    // -----------------------------------------------------------------
    rule("meanwhile, on the laptop: the phone is revoked");

    // A separate replica, which has never seen any of the ops above. All it
    // does is revoke one grant id.
    let mut laptop_log = MoveLog::new();
    laptop_log.revoke(PHONE_KEY);
    println!("      laptop revokes g{PHONE_KEY} — one id, no ops, no coordination");
    println!(
        "\n  Revocation is grow-only and fail-closed: once issued anywhere it\n  \
         reaches everywhere and never leaves."
    );

    let ops_before = phone_log.len();
    let grants_before = phone_log.grants().count();
    let revs_before = phone_log.revocations().count();

    // The merge. Union of three grow-only sets — the only thing it can do.
    phone_log.merge(&laptop_log);

    println!("\n  ...the phone syncs with the laptop...\n");
    println!(
        "      move ops stored:   {ops_before} → {}      ← nothing was deleted",
        phone_log.len()
    );
    println!(
        "      grants stored:     {grants_before} → {}      ← nothing was deleted",
        phone_log.grants().count()
    );
    println!(
        "      revocations:       {revs_before} → {}      ← the merge only ADDED",
        phone_log.revocations().count()
    );

    let after = phone_log.replay_traced(&weave);
    println!("\n  the same log, replayed against the new authority:\n");
    print_trace(&after, &name);

    println!("\n  what is in effect now:");
    print_view(&after, &name);

    println!(
        "\n  Read the second line again: the bot's op cites g{BOT_KEY}, and g{BOT_KEY} is in NO\n  \
         revocation set. It died because its ISSUER did — revoking a grant kills\n  \
         the whole delegation subtree under it (`Authority.demo_cascade_revoked`,\n  \
         `Gated.story_cascade`), decided inside the kernel."
    );
    println!(
        "\n  And the data is all still here. Every op above is still in the log,\n  \
         still merges, still enumerates, still explains itself. `Gated.lean`'s\n  \
         gate is a predicate the VIEW applies; storage never consulted it.\n  \
         `Exec.gated_unauthorised_is_forever`: revoking more can never\n  \
         un-refuse one of these."
    );

    // -----------------------------------------------------------------
    rule("⚠ one more, because it will bite you: removing authority can ADD a move");

    println!(
        "  `Exec.applied_set_not_antitone`. Gating an op out can UN-BLOCK one the\n  \
         cycle rule had been skipping — so \"revoke\" does not mean \"the view\n  \
         shrinks\". Here is that, at the keyboard.\n"
    );

    // Two grants, siblings under the owner's key, so revoking one does not
    // cascade into the other. Fresh ids, on a fresh log — the chain above is
    // not in play here.
    const KEY_A: u64 = 4;
    const KEY_B: u64 = 5;
    let a = table[0].1;
    let b = table[1].1;

    let mut log = MoveLog::new();
    log.issue(Grant::universal(OWNER_KEY));
    log.issue(Grant::delegate(KEY_A, OWNER_KEY, u64::MAX));
    log.issue(Grant::delegate(KEY_B, OWNER_KEY, u64::MAX));

    // The earlier op wins the order; the later one would close a cycle.
    let early = MoveOp { lamport: 1, replica: PHONE, child: a, dest: Some(b), cite: KEY_A };
    let late = MoveOp { lamport: 2, replica: BOT, child: b, dest: Some(a), cite: KEY_B };
    log.record(early);
    log.record(late);

    println!("  both grants live:\n");
    let both = log.replay_traced(&weave);
    print_trace(&both, &name);
    println!("\n  in effect:");
    print_view(&both, &name);

    // Now revoke the EARLIER op's grant. It leaves the feed — and the op it
    // had been blocking becomes applicable.
    log.revoke(KEY_A);
    println!("\n  ...g{KEY_A} is revoked (g{KEY_B} is a sibling, so no cascade)...\n");
    let one = log.replay_traced(&weave);
    print_trace(&one, &name);
    println!("\n  in effect:");
    print_view(&one, &name);

    println!(
        "\n  A move APPEARED because authority was taken away. Nothing is wrong:\n  \
         the gate removed an op, the cycle rule then had no reason to skip the\n  \
         other, and both facts are in the trace with their own names. What DOES\n  \
         hold is the local statement — this op was not replayed, and revoking\n  \
         more never un-refuses it — and the crate says exactly that and no more.\n"
    );
}
