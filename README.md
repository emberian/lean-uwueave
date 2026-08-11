# lean-uwueave

**When two people change the same thing at the same time on different devices,
something has to happen when their changes meet.** Usually what happens is
decided by accident — whatever the code did — and discovered by users, as a
number that was quietly wrong or an edit that silently vanished.

This is a careful, machine-checked map of that moment. It says which promises
your software can keep with **no coordination at all**, which can never be kept
that way, and — when the answer is *never* — what your actual options are and
what each one costs.

Every "no" comes with a small, concrete story of two devices you can watch fail.
Every price comes with the theorem that justifies it. And the trickiest
decisions ship as *compiled proofs*, not as code someone wrote twice.

## The whole idea, in two phones

**A shared shopping list.** You add eggs; your partner adds bread. Offline. When
the phones sync, you have both — no conflict, no server, no waiting. This works
every time, for any number of phones, and it isn't luck: *"the list only grows"*
is the kind of promise that survives meeting.

**A shared $100 balance.** You spend $80; your partner spends $80. Each phone,
alone, was being perfectly responsible. They sync: $160 spent, and no clever
merge can un-spend it. This is not an engineering gap awaiting a better library
— it's a **theorem** (Bailis et al., 2015) that no coordination-free system can
keep that promise. You weren't bad at this. The universe said no.

Everything here lives between those two phones. And the useful part is that
"the universe said no" is *not* the end of the conversation — it's the start of
a priced menu:

- **Split it up front.** Give each device $50 of its own. Both stay within
  their share, both merge freely, and you only talk when you re-divide.
- **Let someone arbitrate.** A designated referee orders the events; everyone
  agrees on the same winner. Costs trust, and some rollback.
- **Keep both and show them.** Don't pick — surface the disagreement to the
  person, who has context the algorithm doesn't.
- **Change what you promised.** Sometimes "at most one" was never the real
  requirement.

Each of those is a theorem here, and — the part we're proudest of — some of
them **provably don't apply** to your particular problem, so the menu you get is
short and honest rather than a list of vague possibilities.

## What you can use without reading any proofs

- **A command-line tool.** Describe your app's shared data in a few lines;
  `uwueave-check` tells you which promises are free, which escalate, and which
  are free *within a seam* — each with the theorem name, so you (or a friend, or
  a model) can check the receipt.
- **The counterexamples.** Every impossibility comes with real states — usually
  three lines — that paste straight into your test suite in any language. A
  refutation here is a gift: it's the bug your users would have found, delivered
  early and politely.
- **A Rust crate.** An append-only content-addressed document store,
  collaborative text, node moving, membership and roles — where the delicate
  decisions are compiled from the proofs rather than reimplemented.

## Some things we found that surprised us

**Content-addressing gives you acyclicity for free.** Naming things by the hash
of their contents-and-parents — the way git does — means every edge points at
something older, so an append-only document *cannot* contain a cycle. No cycle
check, at any scale.

**Verified-correct and safe are different things.** A merge can be provably
correct against its own specification and still bankrupt you, because the
specification permitted it. We build both a counter that is verified *and*
overdrawing, and one that is safe *because it silently loses your data*.
Checking the data structure is not checking the application.

**Knowing the ancestor repairs one kind of conflict and never the other.** If
some ordering of the two concurrent actions would have been legal, a three-way
merge (git's model) can recover it — a released lock re-appearing, say. If *no*
ordering is legal — both people really did spend the money — then no merge in
existence helps, and you need one of the priced exits above.

**Asking for exactly one answer is what costs.** Computing over data that's
still arriving is free; *insisting* the result be a single value is provably a
coordination requirement. So a UI that shows `47 + (2 peers pending)`, or shows
both candidates, is not a degraded experience — it's the honest one, and the
cheap one.

**A merged document is still a document.** Even when two people's changes break
a rule — two "pinned" items where one is allowed — the result stays well-formed
enough to render, with both sides visible. Conflicts become something you draw,
not something you crash on.

## Reading further

- **[The map](docs/MAP.md)** — every module, what it settles, and a ledger of
  keystone theorems tagged by how general each is and whether its counterexample
  is actually reachable in practice.
- **[The website](https://emberian.github.io/lean-uwueave/)** — the same material
  with diagrams, for people who like diagrams.
- **[Trust](docs/TRUST.md)** — three separate ledgers of what this rests on:
  logic, execution, and environment. Including what our own build gate *cannot*
  prove.
- **[The bibliography](docs/BIBLIOGRAPHY.md)** — every paper behind this, what it
  established, what we took, what we declined. Several entries exist to record
  claims of *ours* that the literature refuted.

## Building

```sh
lake build              # every proof + the total axiom gate (Lean core only, no mathlib)
cd rust && cargo test   # compiles the Lean decision layers to C and links them (needs elan)
```

## How to read our claims

We try to be kind by being exact.

**"FREE"** means: merging provably preserves this promise, so coordination is
never required *for that promise*. It does not mean an operation can't break it
locally — validate your inputs — and it doesn't price metadata growth.

**Refutations are concrete states**, not intuitions. **Premises stay premises**:
where a guarantee needs a hash not to collide or a signature not to forge, that
is stated as an assumption and never absorbed into a theorem.

**Boundaries get decomposed, not just declared.** "That's outside our model" is
a stopping condition dressed as honesty, so every boundary here is split into
the part that is irreducibly an assumption and the part that is simply work
nobody has done yet — with the next step named.

And when we get something wrong, the correction lives where the claim lived.
Several parts of this repository exist because outside reviewers took the work
seriously enough to refute pieces of it; those retractions are in the documents,
not buried in the history.

## Papers, and thanks

The full annotated bibliography is [here](docs/BIBLIOGRAPHY.md). The short list:
Bailis et al. (the judgement this is built on), Shapiro et al. (CRDTs),
Gomes–Kleppmann et al. (mechanized convergence), Kleppmann et al. (move
operations, interleaving anomalies, undo/redo), Almeida–Shoker–Baquero (deltas),
Whittaker–Hellerstein (segmented confluence), Hellerstein–Alvaro (CALM),
Kuper–Newton (LVars), Omar et al. (typed holes), Ramesh et al. (Sal), the LoRe
authors, and the Power–Koutris–Hellerstein free-termination line.

Thanks to the weaver whose question started this, and to
[universal-weave](https://github.com/transkatgirl/universal-weave) for being the
kind of library worth building companions for. Made by ember + Claude, with the
[dregg](https://github.com/emberian/dregg) metatheory in the background, and
with review from two other AI systems who made it measurably better by telling
us where we were wrong.

The name is spelled lean-uwueave. That was never a typo.

License: Unlicense OR MIT.
