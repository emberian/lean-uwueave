# lean-uwueave

When two people edit the same thing at the same time on different devices,
something has to happen when the edits meet. Usually what happens is decided
by accident — whatever the code happened to do — and discovered by users.
This repository is a careful map of that moment: which merges can be safe
with **no coordination at all**, which can never be, and what your real
options are when the answer is never. The map is machine-checked; the
impossibilities come with tiny two-device stories you can watch fail; and the
working code that ships alongside gets its trickiest decision straight from
the proofs.

## The whole idea, in one story

Two phones, both offline.

**A shared shopping list.** You add eggs; your partner adds bread. When the
phones sync, the lists merge — everything both of you wrote, no conflict, no
server, no waiting. This works *every* time, for *any* number of phones, and
nothing about it is lucky: "the list only grows" is the kind of promise that
survives merging.

**A shared bank balance of $100.** You spend $80; your partner spends $80.
Each phone, alone, was being perfectly responsible. When they sync: $160
spent, and no clever merge function can un-spend it. This isn't an
engineering gap waiting for a better library — it is a *theorem* (Bailis et
al., 2015) that no coordination-free system can keep that promise. The
question was never "is my merge algorithm good enough"; it's "can *this
particular promise* survive merging at all," and that question has a
definite, checkable answer for each promise you care about.

Everything in this repo lives in the space between those two phones:

- **A catalog of promises, classified.** Grow-only sets, counters, "last
  writer wins" registers, undo/redo, permission systems, DAGs and trees,
  budgets. Each one either *provably safe* (with the proof) or *provably
  impossible* (with the exact two-device story that breaks it — usually
  three lines, pasteable into any test suite in any language).
- **The escape routes, also proved.** When a promise can't survive merging,
  you have real choices: split the budget ahead of time so each device spends
  only its share (safe again, provably); keep *both* versions and show the
  fork instead of silently picking a winner; or replay a log of operations
  with a deterministic tiebreak — whose one honest cost (an old edit arriving
  late can undo a newer one) is *also* a theorem here, so you can design for
  it instead of being surprised by it.
- **Some genuinely nice surprises.** Content-addressing — naming things by
  the hash of their contents, the way git does — makes "no cycles in this
  graph" *free*, with no cycle-checking code at all. Permission systems where
  handing out narrower access works offline, on a plane, in a network
  partition, and late-arriving revocations can only ever *reduce* someone's
  access, never restore it. Sync protocols where sending small diffs is
  provably the same as sending everything.

## Try it in two minutes

The repo ships a small command-line tool for exactly the reader who has a
schema in mind and no interest in proofs. Describe your app's shared state:

```
field notes: gset
invariant notes: member
field pins: gset
invariant pins: unique
```

and `uwueave-check` answers with a verdict per promise:

```
notes  gset  member  FREE       gset_mem_iconfluent — Uwueave/Catalog.lean
pins   gset  unique  ESCALATES  gset_atMostOne_not_iconfluent — Uwueave/Catalog.lean
```

— including, for every ESCALATES, the two-device repro story and the priced
escape routes. Every verdict is a citation into a machine-checked theorem,
and every combination the theorems *don't* settle says so honestly instead
of guessing.

```sh
cd rust && cargo run --bin uwueave-check -- your.schema
```

## What "machine-checked" buys you here

The mathematics is written in [Lean 4](https://lean-lang.org) — a proof
assistant that will not accept a wrong proof — and it builds in about thirty
seconds on a laptop, with no heavyweight dependencies. A build-failing audit
gate pins every key theorem's trust base, so if anyone ever smuggles in an
unproved claim, **the build breaks**. And the Rust library doesn't
*re-implement* the delicate part (the replay tiebreak that keeps everyone's
document identical): the decision procedure is compiled *from the Lean
itself* and linked in. There is no second copy of the rules to drift out of
sync, because there is no second copy.

We are equally careful about what is *not* claimed: the storage glue and
codecs are ordinary tested code, cryptographic assumptions are stated as
assumptions, and wherever our models stop short of a hard problem (rich text
being the famous one), the file says so at the top. Honest boundaries beat
impressive blurs.

That extends to claims about the *field*. A theorem being machine-checked says
nothing about whether someone published it first, and those are separate
questions with separate evidence. On 2026-08-11 an outside reader showed that
eight of our novelty claims were already answered in the literature — that
nobody offered a certain combination of verdicts (LoRe did), that a certain
junction was empty (it was occupied), that a proposed equivalence held (it is
refuted in both directions). Every one is **retracted in the text where it was
made**, indexed in `FORCODEX.md` §0.5, with the papers annotated in the
bibliography. None of the theorems changed; the size of the claims around them
did. If you find another, tell us — a retraction is a deliverable here, and
the only embarrassing part is the interval before it lands.

## Going deeper

- **[The map](docs/MAP.md)** — every module and what it settles, theorem
  names included.
- **[The website](https://emberian.github.io/lean-uwueave/)** — the
  constructions presented properly, diagrams and all.
- **[The bibliography](docs/BIBLIOGRAPHY.md)** — every paper behind this,
  what each established, what we took, and what we deliberately declined.
- **The proofs themselves** — `Uwueave/*.lean`, written to be read: each
  module opens with a plain-language account of what it does and doesn't
  show.

## Building

```sh
lake build              # every proof + the audit gate (~30s cold, no mathlib)
cd rust && cargo test   # compiles the Lean kernel to C and links it (needs elan)
```

## Thanks

This library began as a gift into the [loom](https://github.com/socketteer/loom)
/ [universal-weave](https://github.com/transkatgirl/universal-weave)
ecosystem — branching-document tools whose builders ask exactly the right
questions about merging — and grew from the
[dregg](https://github.com/emberian/dregg) metatheory. Made by ember + Claude. The name
is spelled lean-uwueave, and that was never a typo.

License: Unlicense OR MIT.
