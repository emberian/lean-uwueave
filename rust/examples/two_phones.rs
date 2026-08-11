//! **The README's opening story, runnable.**
//!
//! Two phones, offline, both editing. Then they meet.
//!
//! The shopping list converges — no conflict, no server, no waiting. The
//! shared balance does not, and cannot: that is a theorem (Bailis et al.,
//! 2015), not a gap awaiting a better library. This example shows both, and
//! then the priced exit the theorem leaves you.
//!
//! ```sh
//! cargo run --example two_phones
//! ```
//!
//! Everything printed below is computed, not narrated: the list really is two
//! `CausalWeave`s merged in both directions, the overdraft really is a
//! textbook-correct CRDT join producing an illegal state, and the escrow
//! really is `Weave`'s seam refusing a spend without asking a peer.

use std::collections::BTreeMap;

use uwueave::weave::{SeamChange, Weave, WeaveMergeError, WeaveOpError};
use uwueave::{CausalWeave, EraEvent, EraRole, NodeId};

/// Six hex characters of a content address — enough to recognise, short
/// enough to read. Ids are `blake3(parents ‖ contents)`, so these are stable
/// across runs and across machines.
fn short(id: &NodeId) -> String {
    id[..3].iter().map(|b| format!("{b:02x}")).collect()
}

fn rule(title: &str) {
    println!("\n━━ {title} ━━\n");
}

// ===========================================================================
// 1. The shopping list — the promise that survives meeting
// ===========================================================================

/// A shared shopping list is a grow-only set of items. Here it is a
/// [`CausalWeave`]: each item is a root node whose id is the hash of its
/// contents, so "same item" means "same bytes" everywhere, with no agreement
/// needed about who named it.
type List = CausalWeave<Vec<u8>>;

/// The list's contents, in the store's own iteration order — which is by
/// content address, not by who typed first. That order is arbitration, not
/// intention; it is identical on every replica, which is the property that
/// matters.
fn items(list: &List) -> Vec<String> {
    list.nodes().map(|n| String::from_utf8_lossy(n.contents()).into_owned()).collect()
}

fn shopping_list() {
    rule("1. the shopping list — the promise that survives meeting");

    // Both phones start from the same (empty) list. No server was involved in
    // that agreement: an empty set is an empty set.
    let mut phone_a: List = CausalWeave::new();
    let mut phone_b: List = CausalWeave::new();

    // Offline. Neither phone can see the other.
    //
    // `insert` cannot fail here: a root node names no parents, so there is
    // nothing to be missing. (`InsertError::MissingParent` is the only way it
    // refuses, and it exists to make the shape `acyclicity_not_iconfluent`
    // refutes — an edge to a node you have never seen — unrepresentable.)
    let eggs = phone_a.insert(vec![], b"eggs".to_vec()).expect("a root node has no parents");
    let bread = phone_b.insert(vec![], b"bread".to_vec()).expect("a root node has no parents");

    println!("  phone A, offline:  + eggs   [{}]", short(&eggs));
    println!("  phone B, offline:  + bread  [{}]", short(&bread));
    println!("\n  ...the phones sync...\n");

    // The merge. It is a set union keyed by content address — and by
    // `Acyclicity.grounded_iconfluent` it needs no cycle check and no
    // coordination, at any number of replicas.
    let mut a_then_b = phone_a.clone();
    a_then_b.merge(&phone_b).expect("both stores were built by this API, so both are closed");
    let mut b_then_a = phone_b.clone();
    b_then_a.merge(&phone_a).expect("both stores were built by this API, so both are closed");

    println!("  phone A now holds:  {}", items(&a_then_b).join(", "));
    println!("  phone B now holds:  {}", items(&b_then_a).join(", "));
    println!();

    // The three lattice laws, checked on the real objects rather than
    // asserted. `Uwueave/Lace.lean` is where they are proved in general; this
    // is what they look like on your kitchen table.
    println!("  A.merge(B) == B.merge(A):        {}   (commutative)", a_then_b == b_then_a);

    let mut twice = a_then_b.clone();
    twice.merge(&phone_b).expect("re-merging a store already absorbed");
    println!("  merging the same delta twice:    {}   (idempotent — gossip may repeat)", twice == a_then_b);

    println!("  still acyclic, no check run:     {}   (grounded_acyclic)", a_then_b.grounded());

    println!(
        "\n  Nothing was lost, nobody waited, and there was no server. This is\n  \
         what \"FREE\" means: the merge provably cannot break \"the list only grows\"."
    );
}

// ===========================================================================
// 2. The shared balance — the promise that cannot
// ===========================================================================

/// **The refuted shape.** This type exists in order to fail.
///
/// It is not a strawman: the merge below is a genuine, textbook-correct CRDT
/// join — a G-counter of per-replica withdrawal totals, joined pointwise by
/// maximum. It is commutative, associative and idempotent, it loses no
/// write, and every replica converges. It is *correct*.
///
/// And it still bankrupts you, because the specification it is correct
/// against never mentioned the balance. `Segmented.budget_not_iconfluent`
/// (and Bailis et al. before it) is the statement that no join over this
/// state can do better: the invariant `balance ≥ 0` is not
/// invariant-confluent, so **no** coordination-free merge maintains it.
#[derive(Debug, Clone, PartialEq, Eq)]
struct SharedBalance {
    start: i64,
    /// Per-replica grow-only withdrawal totals. Each phone only ever
    /// increments its own entry — the discipline a G-counter requires.
    withdrawn: BTreeMap<&'static str, i64>,
}

impl SharedBalance {
    fn new(start: i64) -> Self {
        Self { start, withdrawn: BTreeMap::new() }
    }

    fn balance(&self) -> i64 {
        self.start - self.withdrawn.values().sum::<i64>()
    }

    fn withdraw(&mut self, replica: &'static str, amount: i64) {
        *self.withdrawn.entry(replica).or_insert(0) += amount;
    }

    /// The join: pointwise max of the per-replica counters. Nothing clever is
    /// being withheld — this is the best merge that exists for this state.
    fn merge(&mut self, other: &Self) {
        for (replica, total) in &other.withdrawn {
            let slot = self.withdrawn.entry(replica).or_insert(0);
            *slot = (*slot).max(*total);
        }
    }
}

fn shared_balance() {
    rule("2. the shared $100 balance — the promise that cannot");

    println!("  The rule the app promises its user:  balance >= 0\n");

    let shared = SharedBalance::new(100);
    let mut phone_a = shared.clone();
    let mut phone_b = shared.clone();

    phone_a.withdraw("A", 80);
    phone_b.withdraw("B", 80);

    println!("  start:                       ${}", shared.balance());
    println!(
        "  phone A, offline:  -$80  →   ${:<4}  legal on A  ({} >= 0)",
        phone_a.balance(),
        phone_a.balance()
    );
    println!(
        "  phone B, offline:  -$80  →   ${:<4}  legal on B  ({} >= 0)",
        phone_b.balance(),
        phone_b.balance()
    );
    println!("\n  ...the phones sync...\n");

    let mut merged = phone_a.clone();
    merged.merge(&phone_b);
    let mut other_way = phone_b.clone();
    other_way.merge(&phone_a);

    println!("  merged:                      ${}   ← the rule is broken", merged.balance());
    println!("  merged the other way:        ${}   ← and it converges perfectly", other_way.balance());
    println!("  both directions agree:       {}   (it is a correct CRDT)", merged == other_way);

    println!(
        "\n  Each phone, alone, was being perfectly responsible. The merge was not\n  \
         written badly — it is a real semilattice join and it lost nothing. The\n  \
         invariant is simply not invariant-confluent, and Bailis et al. (2015)\n  \
         proved that means NO coordination-free system keeps it. The universe\n  \
         said no; that is the whole of it."
    );
}

// ===========================================================================
// 3. The priced exit — split it up front
// ===========================================================================

const ALICE: u64 = 1;
const BOB: u64 = 2;

type Doc = Weave<Vec<u8>>;

/// "The universe said no" is where the conversation starts, not where it
/// ends. This is the first item on the README's priced menu — *split it up
/// front* — using the crate's real escrow rather than a retelling of it.
///
/// `Weave`'s bounded resource is a storage budget in bytes rather than
/// dollars, but the shape is identical and so is the theorem:
/// `Segmented.budget_segmented` says spends are free *inside* an allocation,
/// and `budget_not_iconfluent` is why re-dividing the allocation is not.
fn priced_exit() {
    rule("3. the priced exit: split it up front");

    // The one agreement, made once: a budget of 100, divided 50/50. This is
    // the seam. Both phones must start from the same one — see the end of
    // this section for what happens when they do not.
    let mut shared: Doc = Weave::new([(ALICE, 50), (BOB, 50)]);

    // Membership, so both may write. The first joiner is Admin (Era.lean §1);
    // Alice then promotes Bob. The arbiter's cuts only *order* these events,
    // they do not decide them.
    for ev in [
        EraEvent::join(1, ALICE),
        EraEvent::join(2, BOB),
        EraEvent::promote(3, ALICE, BOB, EraRole::Writer),
    ] {
        shared.record_membership(ev).expect("fresh event ids, so no eid collision");
    }
    for eid in 1..=3 {
        shared.record_cut(1, eid);
    }

    println!("  budget 100, divided once:  alice=50  bob=50   ← the seam, agreed");
    println!("  (the crate's bounded resource is storage bytes; same shape, same theorem)\n");

    let mut phone_a = shared.clone();
    let mut phone_b = shared.clone();

    // Offline spends. Distinct bytes, so these are genuinely two different
    // nodes rather than one node stored twice (the store is content-addressed
    // and therefore idempotent: storing identical bytes costs nothing twice).
    phone_a
        .add_node(ALICE, vec![], vec![b'a'; 40])
        .expect("40 bytes fits alice's slice of 50");
    phone_b
        .add_node(BOB, vec![], vec![b'b'; 40])
        .expect("40 bytes fits bob's slice of 50");

    println!("  phone A, offline:  stores 40 bytes   ok — spent {}/50", phone_a.spent(ALICE));
    println!("  phone B, offline:  stores 40 bytes   ok — spent {}/50", phone_b.spent(BOB));

    // Running out is local and immediate. It is not a wait, not a round trip,
    // and not a maybe: `afford` compares two integers this replica already
    // holds.
    match phone_a.add_node(ALICE, vec![], vec![b'A'; 20]) {
        Err(WeaveOpError::QuotaExceeded { allocated, spent, requested, .. }) => {
            println!(
                "  phone A, offline:  stores 20 more   REFUSED — allocated {allocated}, \
                 spent {spent}, asked {requested}"
            );
            println!("                     ^ it ran out. it did not wait for phone B.");
        }
        other => println!("  unexpected: {other:?}"),
    }

    println!("\n  ...the phones sync...\n");

    let mut merged = phone_a.clone();
    merged.merge(&phone_b).expect("same seam on both sides, so the merge is licensed");
    println!(
        "  merged:  alice {}/50, bob {}/50 — both spends kept, budget intact",
        merged.spent(ALICE),
        merged.spent(BOB)
    );

    // And now the part the type system makes honest: re-dividing the budget
    // is a meeting, and a replica that skipped it cannot merge.
    let redivide = SeamChange::Reallocate(BTreeMap::from([(ALICE, 45), (BOB, 55)]));
    let mut phone_a = merged.clone();
    phone_a.apply_seam_change(&redivide).expect("sum is unchanged and nobody drops below spend");

    match phone_a.clone().merge(&merged) {
        Err(WeaveMergeError::SeamDisagreement { mine, theirs }) => {
            println!("\n  phone A re-divides to alice=45 bob=55, alone. It can no longer sync:");
            println!("      SeamDisagreement — mine {:?}", mine.allocation);
            println!("                         theirs {:?}", theirs.allocation);
            println!("      ^ the merge refuses rather than inventing a division nobody agreed to.");
        }
        other => println!("  unexpected: {other:?}"),
    }

    let mut phone_b = merged.clone();
    phone_b.apply_seam_change(&redivide).expect("the identical change, applied by the other side");
    phone_a.merge(&phone_b).expect("the meeting happened: both seams agree again");
    println!("\n  Both apply the same change — that IS the meeting — and syncing resumes:");
    println!(
        "      alice={}  bob={}",
        phone_a.seam().allocated(ALICE),
        phone_a.seam().allocated(BOB)
    );

    println!(
        "\n  Between meetings, nobody waits for anybody. That is the trade the\n  \
         theorem prices, stated in the API rather than in a comment."
    );
}

fn main() {
    println!("\nlean-uwueave — the whole idea, in two phones");
    println!("═══════════════════════════════════════════");

    shopping_list();
    shared_balance();
    priced_exit();

    println!(
        "\n  Next: `cargo run --example collaborate` builds a real document with\n  \
         two people in it; `cargo run --example gated` shows authority being\n  \
         revoked while the data stays put.\n"
    );
}
