# `uwueave` — the crate

A replicated document you can edit on two devices at once, where the delicate
decisions are **compiled from machine-checked proofs** rather than written
twice and hoped over.

Nodes in a content-addressed DAG, collaborative text, node moving, membership
and roles, delegated authority, and a storage budget — merged by one `merge`
and read through one `view`. Where the theory says a feature can be
coordination-free, it is. Where the theory says it cannot, the API says so out
loud instead of picking a winner quietly.

```sh
cd rust
cargo run --example two_phones    # start here — 30 seconds, no reading required
```

---

## The one idea, if you have never met it

Two replicas, both offline, both edit. When their states meet, some merge
function runs. The question this crate is organised around is: **which
promises can that merge be trusted to keep?**

Bailis et al. (2015) answered it exactly. A promise (an *invariant*) is
maintainable with zero coordination if and only if it is **invariant
confluent** — roughly, "whenever two legal states merge, the result is legal".
That is an iff, so it cuts both ways:

- *"the list only grows"* is I-confluent → merging can never break it, at any
  number of replicas, forever. Free.
- *"the balance never goes negative"* is **not** → and therefore **no** merge
  function maintains it. Not "no merge we could think of". No merge. You can
  see this fail in `cargo run --example two_phones`, using a textbook-correct
  CRDT that converges perfectly and still overdraws the account.

A "no" is not the end of the conversation, it is the start of a priced menu:
split the resource up front (escrow), let a referee order the events, keep both
answers and show them, or change what you promised. This crate implements the
free fragment as free, implements the unfree parts the way the theorems say
survives, and **refuses** the shapes they refute.

If you want the verdict for *your* schema rather than this one, that is what
the CLI is for — see [The CLI](#the-cli-uwueave-check) below.

---

## Prerequisite: a Lean toolchain

You need [elan](https://elan.lean-lang.org) on `PATH`. `cargo build` will fail
without it, deliberately.

This is not incidental tooling. The parts of this crate that must be *right* —
which move ops survive a replay, in what order text linearizes, who wins a
duel between two admins — are **authored in Lean**, next to the theorems about
them, compiled to C by `lake`, and linked in. `build.rs` runs `lake build`,
compiles every emitted `.c`, and links `libleanshared`. There is no second copy
of those semantics on the Rust side to drift from the first.

`build.rs` also **fails closed**: if `lake build` fails, the Rust build stops
rather than linking whatever C happened to be on disk from last time. A green
`cargo test` reachable from a red `lake build` would be a gate that cannot go
red, which is worse than no gate.

The first build is slow — it builds the whole Lean development. Later builds
are incremental, and `cargo` only re-runs `lake` when `Uwueave/` changes.

```sh
cd rust
cargo build     # slow the first time; needs elan
cargo test      # unit + property suites, replaying the Lean witnesses through the real kernels
```

---

## The examples

Three teaching examples, in the order they are meant to be read. Each one
prints its reasoning as it goes; the interesting output is the part that says
something you did not expect.

### `cargo run --example two_phones`

The README's opening story, executed. A shopping list converges (union merge,
no cycle check, no server). A shared $100 balance does not — both phones spend
$80, both stay legal, and the merge lands at −$60 through a join that is
commutative, associative, idempotent and loses nothing. Then the priced exit:
`Weave`'s escrow, where a spend runs out *locally and immediately* rather than
waiting for a peer, and re-dividing the budget is the only thing that needs a
meeting.

**Read it for:** what FREE and ESCALATES actually feel like at the keyboard.

### `cargo run --example collaborate`

The real one. Ada and Grace share a research notebook over the composed
`Weave<T>`: both add nodes, both write prose into the *same* paragraph, both
re-parent sections, and each admits a new collaborator. Then they sync in both
directions. The two replicas do **not** end up byte-identical — their
transports differ — and their derived views are identical anyway, which is the
theorem rather than a coincidence.

Then the honest part. Ada watches a move succeed on her own screen; after the
sync it has un-happened, because Grace's *older* op won the replay order and
Ada's would have closed a cycle:

```
      t=4   grace  move intro     under method     Applied
      t=9   ada    move method    under intro      SkippedCycle   ← retroactively un-happened
```

That is `Move.view_not_stable`. It is not a bug awaiting a fix: once
`acyclicity_not_iconfluent` has refuted replicated mutable parents, an op log
with a cycle-skipping derived view is what remains, and its price is this. What
makes it liveable is that the kernel hands back one outcome **per op**, so a UI
can say *"Grace's edit superseded your move"* instead of silently redrawing the
tree.

**Read it for:** the whole API in one story, and the anomaly named out loud.

### `cargo run --example gated`

Authority. An owner delegates to a phone, the phone delegates to a scanner bot
with an *attenuated* grant covering only part of the document, work happens
under those grants, and then the owner revokes the phone — concurrently,
offline, by adding one integer to a set.

After the merge, every op is gated out, including the bot's, whose grant
appears in no revocation set at all: revocation cascades down the delegation
chain. And **nothing was deleted** —

```
      move ops stored:   3 → 3      ← nothing was deleted
      grants stored:     3 → 3      ← nothing was deleted
      revocations:       0 → 1      ← the merge only ADDED
```

The gate is a *view*, not a filter on storage. The ops are still there, still
merge, still enumerate, still explain themselves.

The last act is the one that will bite you if nobody tells you: removing
authority can **add** a move to the view (`Exec.applied_set_not_antitone`),
because gating an op out can un-block one the cycle rule had been skipping. The
example shows it happening.

**Read it for:** grants, delegation, cascading revocation, and why "revoke"
does not mean "the view shrinks".

---

## The three kernels

Three decision layers are authored in Lean, emitted to C, and called through a
one-file shim. Each takes a byte-encoded request and returns a byte-encoded
answer; the Rust side does storage, indexing and marshalling, and takes **no**
decisions.

| kernel | Lean source | what it decides |
|---|---|---|
| **move replay** | `Uwueave/Exec.lean` | Given the op set, the node parents and the grant substrate: which ops are authorised, which would close a cycle, and what the resulting parent-override map is. Returns one status per op — that trace is what makes both anomalies attributable. |
| **sequence linearization** | `Uwueave/SeqKernel.lean` | Given a set of anchored text elements and their tombstones: the visible order. Convergence is `Sequence.sequence_view_sec`; sibling order at one anchor is content-address arbitration (`run_order_by_id`), and concurrent runs can come out interleaved (`interleaving_anomaly`). Both are priced, not hidden. |
| **ERA arbitration** | `Uwueave/EraKernel.lean` | Given membership events and the finality arbiter's epoch cuts: the execution order, which events were authorised *at their point of execution*, and every user's resolved role. `Era.duelling_admins_resolved` is the one it exists for — two admins demoting each other leaves one deterministic survivor, the same one at every replica. |

The marshaller between Rust and the replay kernel checks itself, on every
request in debug builds, byte-for-byte against Lean's *proven* canonical
encoder (`Exec.requestCanonicalKernel`). That is a differential, not a proof —
Rust has no formal semantics — and it is the strongest closure available for
the one unverified codec step.

**What is not claimed:** this crate's storage and index glue, the marshaller,
the C shim and Lean's C backend are all unverified, and they are the TCB. The
tests replay the Lean witnesses scenario-for-scenario through the real kernels,
which makes them good tests and zero formal evidence. `../docs/TRUST.md` keeps
three separate ledgers of exactly this.

---

## A short API tour

### `Weave<T>` — the composed document

The type a UI holds. Four substrates, one `merge`, one `view`. (Sketch — the
runnable version of this is `examples/collaborate.rs`.)

```rust
use uwueave::weave::{Capability, SeamChange, Weave};
use uwueave::{EraEvent, EraRole};

// The genesis seam: a storage budget, divided. Every replica must start
// from the SAME one — see "the seam" below.
let mut doc: Weave<Vec<u8>> = Weave::new([(ada, 4096), (grace, 4096)]);

// Membership. The first joiner is Admin; admins promote.
doc.record_membership(EraEvent::join(1, ada))?;
doc.record_membership(EraEvent::join(2, grace))?;
doc.record_membership(EraEvent::promote(3, ada, grace, EraRole::Writer))?;
doc.record_cut(1, 1);                      // the arbiter ORDERS; it does not decide

// The free operations.
let root = doc.add_node(ada, vec![], b"notebook".to_vec())?;
let intro = doc.add_node(ada, vec![root], b"intro".to_vec())?;
let anchor = doc.insert_text(ada, intro, None, b"We set out to ")?;
doc.insert_text(ada, intro, Some(anchor), b"measure the thing.")?;
doc.move_node(ada, 9, intro, Some(root))?; // RECORDED, not applied
doc.bookmark(grace, intro)?;
doc.set_activation(grace, intro, 7, true)?; // per-user cursor, by theorem

// The join. Infallible except where the theory says it must not be.
doc.merge(&other_replica)?;

// The reader.
let view = doc.view();
for node in &view.nodes { /* id, depth, effective_parent, text, pinned, … */ }
view.role(grace);                  // arbitrated, identical at every replica
view.may(grace, Capability::Write);
view.denied_moves();               // stored, replicated, and not in effect
view.replay;                       // one OpOutcome per op — the anomaly, attributed
```

Two things about this API are worth stating plainly, because they are design
consequences of theorems rather than taste:

**A move is stored, not applied.** `move_node` records an op. The effective
parent map is *derived* at `view()` time by the replay kernel. This is forced:
`Acyclicity.acyclicity_not_iconfluent` refutes a replicated mutable parent
pointer, so the only shape that survives is "replicate the monotone thing (the
op set) and derive the invariant-bearing thing (the tree)".

**The gate is a view.** `merge` never consults a role or a grant. A demoted
user's nodes, text and move ops merge like anyone else's — `view()` is where
the role change shows up, as `denied_moves()`. Storage that filtered by
permission would make what a replica *holds* depend on when it learned about a
demotion, which is divergence with extra steps.

### The seam — the document's entire coordination surface

Everything above merges without asking anyone. Two fields do not: the community
**pin** and the budget **allocation**. Together they are the `Seam`, and
`Weave::merge` **refuses** when two replicas disagree about it:

```rust
match a.merge(&b) {
    Err(WeaveMergeError::SeamDisagreement { mine, theirs }) => { /* hold a meeting */ }
    // …
}
```

There is deliberately no merge-time resolution of divergent seams, because
`WeaveState.weaveDocVerdict` exhibits two complete legal documents whose merge
breaks the pin rule — resolving it would mean inventing a policy and calling it
a merge. Changing the seam is `apply_seam_change`, applied *identically* at
every replica; that application **is** the coordination event the theorem
prices. How agreement is reached is the meeting's business and out of scope.

Notice the pin is an `Option`, not a set: the refuted shape is unrepresentable
rather than merely refused.

### The substrates, if you want them separately

Each is usable on its own, and each is what `Weave` composes.

| module | type | what it is |
|---|---|---|
| `causal` | `CausalWeave<T>` | Append-only content-addressed DAG. `merge` is set union by id. Grounded by construction (`rank = 1 + max parent rank`), so it **cannot** hold a cycle and no cycle check exists anywhere. Same-id-different-bytes is treated as corruption and refused loudly. |
| `seq` | `SeqCrdt` | RGA-style sequence with tombstones: a grow-only content-addressed element set, union merge plus tombstone-OR. `text()` calls the Lean kernel; the order is never stored. |
| `movelog` | `MoveLog`, `MoveOp`, `Grant` | Three grow-only sets (ops, grants, revocations), union merge. `replay(&weave)` gives the parent-override map; `replay_traced` gives it with one `OpOutcome` per op. Format v3 ops cite the grant they exercise, and there is **no ungated path**: an op citing nothing does not replay. |
| `era` | `EraGroup`, `EraEvent`, `EraRole` | Membership events and arbiter cuts, both grow-only. `resolve()` returns roles plus one status per event in *execution* order — the arbitration itself, observable. |

Two API notes that will save you a puzzled hour:

- **`Grant`'s `scope` is a ceiling in the request's node-index space**, not over
  content addresses. Indices are the weave's ascending-`NodeId` order, so two
  replicas agree about coverage exactly when their weaves agree.
  `Grant::universal` is the honest "no attenuation" grant when you do not want
  that coupling. The `gated` example prints the index table so you can watch it.
- **Revoking a grant kills its whole delegation subtree**, and revocation is
  grow-only and fail-closed: once issued anywhere it reaches everywhere and
  never leaves.

---

## The CLI: `uwueave-check`

Describe *your* replicated fields and the invariants you care about; get a
verdict per invariant with the theorem that settles it.

```sh
cargo run --bin uwueave-check -- examples/loom.schema
cargo run --bin uwueave-check -- --help          # the full shape and kind vocabulary
```

It is a **lookup table, not a checker** — and it is a lookup table whose
citations are cross-checked by the test suite against the Lean sources and
against `docs/MAP.md`'s keystone ledger, in both directions. A pair the Lean
development does not settle comes back `UNCLASSIFIED` rather than guessed;
`examples/loom.schema` deliberately contains one so you can see it happen.

---

## Reading further

- `../README.md` — the project, and the five things that surprised us
- `../docs/MAP.md` — every Lean module, what it settles, and the keystone ledger
- `../docs/TRUST.md` — three ledgers of what this rests on: logic, execution,
  environment, including what the build gate *cannot* prove
- `../docs/BIBLIOGRAPHY.md` — every paper, what we took, and what we declined

License: Unlicense OR MIT.
