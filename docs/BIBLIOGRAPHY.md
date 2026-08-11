# Annotated bibliography

The papers behind lean-uwueave's theorems, and the honest seams between them.
Each entry says what the paper establishes, what this repo takes from it (with
the actual theorem and file names, so the mapping is checkable rather than
vibes), and where we differ or take nothing. "Context only" is a real verdict
here, not a slight — half the value of a library this small is knowing exactly
which ideas it *declined*.

**Where the PDFs live:** the collection is kept in the maintainers' paperbin,
not in this repository — ask and we'll point you at it. Several references
could not be archived and say so in their own entries; the pattern is always
the same and always explicit — **what we read, and therefore what the entry is
bounded by**. The long-standing two are **Najafzadeh–Shapiro–Eugster (VMCAI
2018)**, cited through the Kleppmann et al. move-op paper's related-work
discussion of it, and **Yu's causal-length set** (the design `ORSet.lean`'s
`CLSet` is named for), whose nearest archived neighbor is Lavoie's ∞P-Set
note, presenting the same odd/even-counter construction and crediting its
earlier appearance in Yu, Elvinger & Ignat's undo framework.

**⚠ Six entries below were added on 2026-08-11 because an external review
(codex) found claims of ours the literature refutes.** They are marked
**⚠ RETRACTION SOURCE** and each says which claim it kills. The retractions
themselves live where the claims were made — `FORCODEX.md` §0.5 indexes all
eight — because a retraction filed somewhere else is a footnote, and a
footnote is how a false claim survives. Read those entries first if you are
here to check whether we are overclaiming; they are the ones that cost us
something.

---

## The judgement, and foundations

**Peter Bailis, Alan Fekete, Michael J. Franklin, Ali Ghodsi, Joseph M.
Hellerstein, Ion Stoica — "Coordination Avoidance in Database Systems",
PVLDB 8(3) / VLDB 2015. (Archived: the extended version, arXiv:1402.2237.)**

*What it establishes.* Invariant confluence (I-confluence): an invariant can be
maintained coordination-free by a convergent replicated system **iff** every
merge of two invariant-satisfying states satisfies the invariant — necessary
*and* sufficient, over every possible implementation. They then classify real
database invariants (foreign keys, uniqueness, balances; ten of twelve TPC-C
invariants pass) and demonstrate the throughput this unlocks.

*What this repo takes.* The entire judgement. `Confluence.lean` is the
necessary-and-sufficient result restated over bare join-semilattices:
`IConfluent` (their Theorem 3.1's
coincidence, held as a definitional fact), and `escalation_witness` — failure
is constructive, the clashing pair *is* the bug report. Their motivating
non-negative-balance example is proved concretely as
`Catalog.pncounter_nonneg_not_iconfluent`, and their escrow exit as
`escrow_local_bound_iconfluent`.

*Where we differ.* Bailis et al. analyze transactions over database states and
build a coordination-avoiding prototype; this repo keeps only the state-merge
half of the judgement, proves single concrete miniatures instead of surveying
workloads, and offers no decision procedure and no performance claims.

**Michael Whittaker, Joseph M. Hellerstein — "Interactive Checks for
Coordination Avoidance", PVLDB 12(1): 14–27, 2018.**

*What it establishes.* Conditions under which invariant *closure* and invariant
confluence coincide, an interactive decision procedure (implemented in Lucy),
and **segmented invariant confluence**: a non-confluent invariant may still hold
within segments of the state space, so replicas coordinate only to cross a
segment boundary and run free inside one.

*What this repo takes.* `Segmented.lean` whole: `SegmentedIConfluent`,
conservativity over the plain judgement
(`iconfluent_iff_trivially_segmented`), and the punchline pair
`budget_not_iconfluent` / `budget_segmented` — one budgeted invariant, both
verdicts, discharging the escrow design of `Catalog.lean` §4 at the level
their framework asks for.

*Where we differ.* Their contribution is substantially the *checkability* —
the decision procedures and Lucy. Nothing here decides anything automatically;
our segmentation is one definition and one worked miniature, and their richer
segment machinery (per-segment restricted transaction sets) is not modeled.

**Joseph M. Hellerstein, Peter Alvaro — "Keeping CALM: When Distributed
Consistency is Easy", CACM 63(9): 72–81, 2020 (arXiv:1901.01930).**

*What it establishes.* The CALM theorem in its accessible form: a program has
a consistent, coordination-free distributed implementation **iff** it is
monotonic. Coordination is not the price of consistency in general — it is the
price of *non-monotonicity*, and the paper reads a decade of systems work
(Bloom, Anna, Lasp, CRDTs) through that lens, including the observation that
the CRDT literature's "eventual consistency" and the query literature's
"coordination-freedom" are the same boundary seen from two sides.

*What this repo takes.* The framing every module is written inside, and the
name of the second of the three verdicts §4 of `FORCODEX.md` sketches.
Concretely: `Catalog.gset_monotone_iconfluent` is the positive monotone case
on one lattice, `Confluence.lean`'s `Leq` order is the "growth" CALM reasons
over, and `Holes.lean` cites CALM as the corner of its triangulation that
supplies *coordination-freedom* (as against LVars' determinism). The library's
whole stance — that the verdict is a property of the *promise*, not of the
merge implementation — is CALM's stance narrowed to I-confluence.

*Where we differ.* CALM is stated for relational transducer networks and
proved there; nothing in this repo is a transducer, there is no network model,
and no theorem here is CALM. We take the boundary and prove instances of the
I-confluence specialization of it. Its successor below (Complete CALM)
subsumes both.

**Joseph M. Hellerstein — "Complete CALM: A Coordination Criterion for
Specifications", arXiv:2602.09435, 2026.**

*What it establishes.* A single semantic theorem generalizing CALM to arbitrary
concurrent specifications: a specification admits a coordination-free
implementation **iff** it is monotone (under any refinement order, not just set
inclusion), subsuming CALM, I-confluence, HATs and CRDT results as instances,
with a Complete CAP companion.

*What this repo takes.* Context, mostly — this repo lives entirely inside the
I-confluence instance the paper subsumes. The honest kinship is
`Catalog.gset_monotone_iconfluent` (upward-closed invariants survive union —
the positive monotone form, on one lattice) and the `Leq`-order framing of
`Confluence.lean`; no theorem here states the specification-level iff.

*Where we differ.* Everything above the instance: histories, observation
functions, refinement orders, proper coordination. We cite it as the widest
current statement of the boundary all our verdicts sit on.

⚠ **And it is the ancestor of an idea `FORCODEX.md` §4 proposed as new.** That
memo's corrected headline — *"is the value at this position stable under joins
of incomparable extensions"*, I-confluence **indexed by position in a
computation** — is an instance of this paper's shape, not a departure from it:
a specification is monotone here exactly when every admissible outcome at a
history has a compatible refinement at every causal extension, under a
*declared refinement order*, and "position in a computation" is a choice of
observation function. The paper recovers I-confluence as an instance
explicitly (its §6.1/§7). So the semantic ancestor of the position-indexed
idea is this, published first, at greater generality. What is genuinely ours
is narrower and should be described that way: machine-checked *instances* with
constructive counterexamples, the segmented refinement, and a coordination
*frequency*.

**Conor Power, Paraschos Koutris, Joseph M. Hellerstein — "The Free
Termination Property of Queries Over Time", arXiv:2502.00222, 2025.**
*(⚠ **RETRACTION SOURCE** — it kills the proposed headline *iff* of
`FORCODEX.md` §4/§5.1, in both directions.)*

*What it establishes.* The **completeness** question CALM's soundness question
leaves open: without coordination, when may a node *unilaterally terminate*,
knowing further arrivals cannot change its answer? Modeled over semiautomata,
so relational transducers and CRDT-style algebraic state land in one
framework. The results we lean on: **Proposition 10** — under inflationary
updates, a monotone query at a *maximal* output, or an **antitone** query at a
*minimal* output, freely terminates (Example 11: `∀x. x = a` settles forever
the instant one non-`a` arrives); **Definition 12 / Theorem 13** — a Boolean
threshold query's free-termination states are **exactly** the states at or
above its threshold antichain, so `|R| > 10` never settles anywhere below the
line even though it is monotone and already correct; **Example 16** — a query
neither monotone nor antitone (`R(c) ∧ ¬S(c)`) that nonetheless *has*
free-termination states; **Theorem 18**, the *inverse curse* — if every state
is invertible (a group; incremental view maintenance over rings), no
non-constant query has any free-termination state at all; and **Theorem 22** —
`(Q, I)` is coordination-free correct **iff** `I` is a free-termination state
for `Q`.

*What this repo takes.* A retraction, and a correction to the shape of a
theorem we had not yet built. `FORCODEX.md` §5.1 proposed *"a hole persists
across all gossip-only extensions **iff** the expression is non-monotone at
that position"*. Proposition 10 and Example 16 refute ⟸ (non-monotone
expressions that settle unilaterally); Theorem 13 refutes ⟹ (a monotone
expression whose hole is open forever). And Theorem 22 says why no re-indexing
repairs it: **settlement is a property of the pair (query, current state);
monotonicity is a property of the query alone.** What replaces it is the
future-exclusion pair already partly built in `Holes.lean` — *no exact value
without stability evidence* (`SealsTo` under `Stable`; `seal_survives_stable`
positive, `unstable_seal_clash` the price of skipping it) and *no hidden fork
after reachable divergence* (`determinate_result_not_iconfluent`, with
`CausalReach`'s Live tag supplying reachability). The inverse-curse theorem is
also the sharpest external statement of why `Catalog.pncounter_*` behaves
worse than `gcounter_*` for a reason that is **not** I-confluence.

*Where we differ, and what we owe it.* Their model is semiautomata with an
explicit quiescence point and a `ready` transition; we have no termination
predicate at all — `Holes.Stable` is an abstract licence, not a decision
procedure, and nothing here decides free termination for anything. Their §6
gives a linear-time algorithm for deciding free-termination states over finite
state spaces; we have no counterpart. The open question their framework hands
us and we have not answered: **is a `Segmented` seam boundary a threshold
antichain?** If it is, `Cost.crossings` is counting something they would
recognize.

**Marc Shapiro, Nuno Preguiça, Carlos Baquero, Marek Zawirski — "A
comprehensive study of Convergent and Commutative Replicated Data Types",
INRIA Research Report RR-7506, January 2011 (the companion of the SSS 2011
CRDT paper).**

*What it establishes.* The CvRDT/CmRDT formulation — state-based CRDTs as
join-semilattices with monotone merges, op-based as commuting concurrent
operations — plus the standard catalog: G-Set, 2P-Set, LWW register and set,
OR-Set, counters, graphs, sequences.

*What this repo takes.* `MergeState` in `Confluence.lean` is exactly their
join, presented by its operation (commutative, associative, idempotent).
`Catalog.lean`'s G-Set / G-Counter / PN-Counter / LWW and `ORSet.lean`'s
OR-Set are their specifications with the merge laws *proved* and a keystone
invariant classified each — `gset_mem_iconfluent`,
`gset_atMostOne_not_iconfluent`, `lww_every_invariant_iconfluent`,
`orset_present_survives`, and kin.

*Where we differ.* The study proposes and specifies; we machine-check
miniatures of a few entries and interrogate their *invariants*. Their directed
graph CRDT deliberately tolerates cycles for its web-crawl use case;
`Acyclicity.lean` prices what refusing cycles costs instead. Both are
coherent positions — they answer different applications.

**Victor B. F. Gomes, Martin Kleppmann, Dominic P. Mulligan, Alastair R.
Beresford — "Verifying Strong Eventual Consistency in Distributed Systems",
Proc. ACM Program. Lang. 1(OOPSLA): 109, 2017.**

*What it establishes.* A modular Isabelle/HOL framework with an axiomatic
network model and an abstract convergence theorem, yielding the first
machine-checked SEC proofs for RGA, OR-Set and a counter — and documents that
informal *and* previously mechanised proofs in this area have been wrong,
usually via false assumptions about the execution environment.

*What this repo takes.* The confessed mirror: `Confluence.lean`'s header cites
this as "the Isabelle account this mirrors", and `Move.derived_view_sec` is an
SEC statement in their sense (order-independence plus redelivery-immunity)
pushed through a derived view. The discipline of *proving* merge laws rather
than asserting them is theirs.

*Where we differ.* They model an asynchronous network with delivery events and
verify op-based algorithms against it; this repo has no network model at all —
merges of states stand in for delivery schedules. That is why our results are
about merge semantics, never about protocol executions. Lean core instead of
Isabelle/HOL; miniatures instead of a reusable framework.

**Pranav Ramesh, Vimala Soundarapandian, KC Sivaramakrishnan — "Sal:
Multi-modal Verification of Replicated Data Types", IIT Madras,
arXiv:2603.27202, March 2026.**

*What it establishes.* Lean-based verification of RDT and **MRDT**
implementations against **RA-linearizability** — a correctness condition for
replicated objects with a three-way (lowest-common-ancestor) merge, the Git
model — with a staged proof pipeline (proof reconstruction, then SMT, then an
AI tier) discharging 69% of verification conditions without SMT, and
property-based counterexample generation for the ones that fail. Thirteen
verified RDTs.

*What this repo takes.* The nearest neighbour, and a foil. `RALin.lean`
formalises RA-linearizability at this repo's miniature scale in order to prove
the two axes **independent**: `ra_linearizable_but_unsafe` takes Sal's own
Table-2 PN-counter — RA-linearizable for any fork and branches, every branch
legal at every prefix — and overdraws at the merge; the converse (a
max-counter that makes every invariant I-confluent by *losing* updates) shows
safety bought with data loss; `quadrants` inhabits all four cells;
`ra_lin_preserves_inductive_invariants` (axiom-free) is what RA-linearizability
genuinely does buy; `guarding_moves_the_bug` shows the two verdicts entangle
through op preconditions. Their LCA question is also the seed of
`Ancestral.lean` (`lock_ancestral_confluent` — mutual exclusion is free with
an ancestor and beyond every two-way join; `budget_defeats_every_faithful_merge`
— the bounded counter is beyond every *honest* three-way merge, so escrow
stands; `clash_dichotomy` names the rule).

*Where we differ.* Different question, and we should keep saying so: Sal asks
*is my merge implementation correct?*, we ask *can my application's promise
survive any merge at all?* Where Sal is ahead: automation (we hand-prove),
RA-linearizability as a correctness condition we model only in miniature,
MRDTs and three-way merge as a first-class setting, and breadth. Where the
repos diverge in kind: Sal verifies implementations against a specification,
this library classifies *invariants* and ships the refutations. (Amusing
independent convergence, worth recording: both picked `α → Bool` for decidable
sets, for the same reason.)

**Nuno Preguiça — "Conflict-free Replicated Data Types: An Overview",
arXiv:1806.10254, 2018.**

*What it establishes.* A survey organized by audience — application developer
(concurrency semantics: add-wins vs remove-wins, LWW, multi-value), system
developer (synchronization models), CRDT developer (design techniques).

*What this repo takes.* Context only — but load-bearing context: the survey's
stance that concurrency semantics are *choices with trade-offs* rather than a
correctness ranking is the stance `ORSet.lean` makes theorem-shaped ("neither
is better; they price the same square edit differently").

*Where we differ.* No specific theorem grounds in it; it is the map we hope a
reader arrives holding.

## Sets and registers

**Erick Lavoie — "State-Based ∞P-Set Conflict-Free Replicated Data Type",
arXiv:2304.01929, 2023.**
*(Archived under `causal-length-2pset-note.pdf` — note the file contains this
∞P-Set paper, not Yu's causal-length paper; see the header note.)*

*What it establishes.* A state-based set supporting unbounded alternating
add/remove per element via a grow-only dictionary of grow-only counters — odd
count means present — with longest-sequence-wins semantics and detailed
convergence proofs, presented pedagogically. Lavoie notes the core idea had
appeared, unnamed, in Yu, Elvinger & Ignat's undo framework (OPODIS 2019).

*What this repo takes.* `ORSet.lean`'s `CLSet` is this odd/even-counter
construction (which we name for Yu's causal-length set, per the lineage
above): `clset_present_iconfluent` and `clset_absent_iconfluent` — per-key max
*selects*, so per-element membership is free — and the honest counterweight
`clset_cross_element_not_iconfluent`, the third instance of "selection
lattices compose into non-selection lattices". The arbitration the design
bakes in (a longer remote history silently wins the element) is
longest-sequence-wins, stated as a price.

*Where we differ.* We classify the presence invariants of the counter core
only; the dictionary composition, memory comparisons against OR-Set/LWW-Set,
and the full convergence development are not modeled.

**Leo Stewen, Martin Kleppmann — "Undo and Redo Support for Replicated
Registers", PaPoC '24, Athens, 2024.**

*What it establishes.* A survey of undo/redo semantics in mainstream
collaborative software (local vs global undo, Undo Redo Neutrality, when a
remote operation blocks undo), and an undo/redo algorithm on top of the
multi-value register — undo as the reintroduction of an overwritten value —
intended for Automerge.

*What this repo takes.* `Undo.lean` in full is the semantic core of this paper
in miniature: an undo is an ordinary write of the restored value at a fresh
dominating clock, so the MV-register's existing guarantees cover it —
`undo_restores`, `redo_restores`, `undo_preserves_history`,
`undo_conflicts_visibly`, `undo_does_not_silently_lose`. `MVRegister.lean`'s
`conflict_surfaces` / `resolution_is_a_write` are the substrate claims their
algorithm stands on.

*Where we differ.* `Undo.lean`'s own honest-scope block is the authority: the
paper's contribution is an *algorithm* (RestoreOp anchors resolved by
history-DAG traversal, undo/redo stacks, redo-clearing, sibling ordering), and
our miniature is handed its targets directly, proves one round trip rather
than Undo Redo Neutrality's induction, and — since the paper's evidence is a
TypeScript prototype — checks nothing of theirs, only its own story.

## Trees, DAGs and moves

**Evelyn Borth, Philipp Lersch, Annette Bieniusa — "Directed Acyclic Graph
CRDTs", PaPoC '25, Rotterdam, 2025.**

*What it establishes.* A CRDT for DAGs in which nodes *and edges* can be added
and removed without coordination, with invariant violations (cycles, dangling
edges) detected after merge and repaired by deterministic **compensation** —
a Sequence CRDT records edge-insertion order, and the most recently added
cycle-contributing edge is removed identically at every replica. Implemented
on Yjs, with a comparison of compensation strategies.

*What this repo takes.* This is the named compensation exit in
`Acyclicity.lean`'s docblock. Their Figure 2 — two clients inserting opposite
edges between the same two tasks — *is* the clashing pair of
`acyclicity_not_iconfluent` (`{0 → 1}` ∪ `{1 → 0}`), which is the theorem any
DAG CRDT must route around: both replicas legal, the union not, so some policy
must fire.

*Where we differ.* Two legitimate exits from the same impossibility. Borth et
al. keep arbitrary edge insertion mutable and repair after sync — users retain
the full edit language and may occasionally watch a previously-valid edge be
removed by compensation. This repo instead shrinks the insertable language to
the grounded fragment (`grounded_iconfluent` + `grounded_acyclic`: every edge
descends in rank, which content-addressing gives for free) and routes
re-pointing edits through op-log arbitration (`Move.derived_view_sec`, priced
by `Move.view_not_stable`). Their price is paid at repair time, ours in
expressiveness and view stability; `acyclicity_not_iconfluent` is why neither
design could avoid paying somewhere.

**Martin Kleppmann, Dominic P. Mulligan, Victor B. F. Gomes, Alastair R.
Beresford — "A highly-available move operation for replicated trees", IEEE
Transactions on Parallel and Distributed Systems, 2021.**

*What it establishes.* A CRDT move operation for trees: order all operations
by timestamp, undo/redo on late arrivals so each op takes effect at its
ordered position, and skip any move that would create a cycle. Verified in
Isabelle/HOL (no cycles, convergence, SEC, for unbounded executions), with
demonstrated concurrent-move bugs in Dropbox and Google Drive as motivation.

*What this repo takes.* `Move.lean` §2's interpreter is "the Kleppmann rule
restricted to this universe": `miniInterp_acyclic` discharges, for the
miniature, the enforcement obligation their Isabelle Theorem 1 discharges in
general, and `view_not_stable` proves the price they surface informally as
moves that "jump back". `Exec.lean`'s replay kernel (total timestamp order +
cycle-skip, `@[export uwueave_replay_kernel]`) implements the same rule, and
the Rust `movelog::MoveLog` calls it rather than reimplementing it.

*Where we differ.* They verify the full algorithm over arbitrary trees and
unbounded executions; our generic theorem (`derived_view_sec`) covers the
pattern, but the cycle-skip enforcement is proved only for a two-node,
two-op miniature, and the refinement of `Exec.lean`'s executable replay to
`Move.lean`'s abstract model is named open work in `Exec.lean`'s header —
not claimed by adjacency.

**Martin Kleppmann, Victor B. F. Gomes, Dominic P. Mulligan, Alastair R.
Beresford — "OpSets: Sequential Specifications for Replicated Datatypes
(Extended Version)", arXiv:1805.04263, 2018.**

*What it establishes.* A specification framework in which a replicated
datatype's semantics is a function of a *set* of timestamped operations,
interpreted in sequential order — used to specify maps, sets, lists, text,
registers and trees (including the first atomic tree-move specification), to
expose a long-overlooked text-editing correctness property, all formalised in
Isabelle/HOL.

*What this repo takes.* The op-log pattern in its clearest published form.
`Move.lean`'s motto — replicate the monotone thing, derive the
invariant-bearing thing — is the OpSets stance, and `derived_view_sec` states
that stance's guarantee over any `MergeState`-shaped log. `MVRegister.lean`'s
derived view (`InView`, `view_antichain`) is the same shape at one slot.

*Where we differ.* OpSets uses interpretation-of-the-op-set as a
*specification* against which algorithms are verified; this repo uses it as an
*implementation pattern* and prices it (`view_not_stable`). Their list/text
specifications have no counterpart here at all.

**Liangrun Da, Martin Kleppmann — "Extending JSON CRDTs with Move
Operations", PaPoC '24, Athens, 2024.**

*What it establishes.* A move algorithm for Automerge-style JSON OpSets —
largest-ID-wins among concurrent moves of the same element, validity
re-checked so cycles never materialize, working uniformly across maps and
lists and interacting correctly with concurrent non-move operations, with
performance optimisations and a prototype.

*What this repo takes.* Context only — but it is the best evidence that the
`Move.lean` pattern (grow-only op set, deterministic winner, skip-invalid)
generalizes beyond trees to document namespaces, which is the shape
`Weave.lean` gestures at for split/merge/dedup edits.

*Where we differ.* Their work is production-shaped engineering of the pattern
inside a real OpSet; our miniature has two ops, one rule, and no performance
story.

**Mahsa Najafzadeh, Marc Shapiro, Patrick Eugster — "Co-design and
verification of an available file system", VMCAI 2018, pp. 358–381.**
*(NOT ARCHIVED — cited from the related-work discussion in the Kleppmann et
al. move-op paper above, which is where we read about it.)*

*What it establishes (as reported there).* Two implementations of a replicated
filesystem: a coordination-free CRDT in which conflicting concurrent moves are
resolved by **duplicating** tree nodes, and a centralised implementation in
which move operations must obtain a **lock** before executing — availability
traded for the absence of duplication.

*What this repo takes.* The clearest early statement that the concurrent-move
conflict forces a genuine fork in design space — duplicate, lock, or arbitrate
by timestamp. `acyclicity_not_iconfluent` is the impossibility behind the
fork, and `Move.lean` takes the third branch. Because we could not archive the
paper, every claim here is bounded by what Kleppmann et al.'s discussion
reports; read their §2.3 and §6.1 before citing it further.

*Where we differ.* We have not read the primary source — this entry is an
honest relay, flagged as such.

## Sequences

**Martin Kleppmann, Victor B. F. Gomes, Dominic P. Mulligan, Alastair R.
Beresford — "Interleaving anomalies in collaborative text editors",
PaPoC '19, Dresden, 2019.**

*What it establishes.* Several published sequence CRDTs can interleave two
users' concurrently inserted runs of text character-by-character (dense
position identifiers are the cause); the paper specifies non-interleaving and
shows how to rule out the lesser anomaly in one algorithm.

*What this repo takes.* `Sequence.lean`'s centerpiece is a *computed* instance
of the anomaly this paper names: two concurrently inserted runs merging to
`[4,3,2,1]`, strictly alternated, under an RGA-shaped anchored order — and it
is reproduced through the shipping kernel in a Rust test, so the anomaly is
observable in the compiled artifact and not only in the model. `Fugue.lean`
(below) is the answer to it.

*Where we differ.* Their specification of non-interleaving is general and
ours is a witness plus, in `Fugue.lean`, a theorem over generated concurrent
histories at miniature scale. Rich text, formatting, and the full algorithmic
landscape the paper surveys have no counterpart here; the README's scoping
("nothing here competes with loro's sequence CRDTs; this is the structural
layer around them") stands.

**Matthew Weidner, Martin Kleppmann — "The Art of the Fugue: Minimizing
Interleaving in Collaborative Text Editing", arXiv:2305.00583, 2023.**
*(NOT ARCHIVED — the design is implemented here from its published
description; this entry is bounded by that.)*

*What it establishes.* A list CRDT whose insertion order is a *tree* rather
than a dense identifier space: each character hangs off an origin as a left or
right child, so a replica's consecutive typing run becomes a **chain of
descendants** rather than a family of siblings, and a rival replica's
concurrent run hangs elsewhere in the tree. Two runs can therefore be ordered
against each other without their interiors interleaving — the anomaly the
PaPoC'19 paper specifies is ruled out by the shape of the order, not by a
repair.

*What this repo takes.* `Fugue.lean` builds that order at this repo's scale
and proves the property in general over generated concurrent histories:
`fugueOrder` is the in-order tree walk (fuel-totalized in `SeqKernel`'s
discipline), `runOps` is the chain rule as an insertion model, and
`fugue_runs_never_interleave` is the theorem — with `rga_head_runs_interleave`
the contrast in the *same* model on the *same* editing intent, so the two
readings differ only in the order, which is the honest form of the comparison.
`fugueOrder_nodup` and `fugueOrder_mem` are the well-formedness half.

*Where we differ.* Ours is a miniature over dense indices `0 ≤ i < n` where
the index order *is* the arbitration order; the paper's identifier scheme,
its complexity analysis, its handling of deletions and its evaluation have no
counterpart. `SeqKernel.lean` still ships the RGA order, with non-interleaving
an explicit non-claim — Fugue is proved here, not deployed here, and saying
otherwise would be adjacency dressed as a result.

## Deltas and operation logs

**Paulo Sérgio Almeida, Ali Shoker, Carlos Baquero — "Delta State Replicated
Data Types", arXiv:1603.01529, 2016.**

*What it establishes.* δ-CRDTs: mutators return small *delta-states* that are
joined into local and remote replicas, giving op-based message sizes over
unreliable channels with state-based robustness, plus anti-entropy algorithms
including a causally consistent one.

*What this repo takes.* Mostly context, with one real echo: `derived_view_sec`
is stated over `(base ⊔ Δ₁) ⊔ Δ₂` — increments *as states, joined in* — which
is precisely the δ reading of a join-semilattice, and
`Confluence.le_merge_left` (gossip is safe to repeat) is the monotonicity
δ-dissemination leans on.

*Where we differ.* No delta-interval machinery, no anti-entropy algorithms, no
causal-delivery proofs here.

**Carlos Baquero, Paulo Sérgio Almeida, Ali Shoker — "Pure Operation-Based
Replicated Data Types", arXiv:1710.04469, 2017.**

*What it establishes.* Op-based CRDTs where `prepare` may return only the
operation itself; replica state is a **PO-Log** — a partially ordered log of
operations — with a Tagged Causal Stable Broadcast API enabling log compaction
once entries become causally stable.

*What this repo takes.* The PO-Log is the most literal published ancestor of
`Move.lean`'s replicated state — "the set of operations ever issued", with the
visible structure a pure function of it. `derived_view_sec` is stated over
exactly such a log-shaped CRDT. (The blocklace paper below closes the loop by
showing its hash-DAG is isomorphic to a PO-Log.)

*Where we differ.* Their framework assumes causal-broadcast middleware and
proves compaction at stability; our log is a bare G-Set with *no* delivery
assumption — which is exactly why `view_not_stable` bites, since an older op
may arrive arbitrarily late — and we prove nothing about compaction.

## Byzantine settings

**Paulo Sérgio Almeida, Ehud Shapiro — "The Blocklace: A Byzantine-repelling
and Universal Conflict-free Replicated Data Type", arXiv:2402.08068
(v4, 2025).**

*What it establishes.* The blocklace — a partially-ordered generalization of
the blockchain in which each block carries signed hash pointers to
predecessors — is itself a CRDT (both pure op-based and delta-state) and a
universal store; because block identity is a *signed* hash, equivocation is
detectable from the equivocator's own artifacts, enabling protocols that
eventually exclude Byzantine nodes and bound their harm to a finite prefix.

*What this repo takes.* `Causality.lean` §2 is, by its own docstring, "the
blocklace §5 in miniature": `ForkEvidence` (two different blocks at one
(author, seq) slot), `fork_evidence_iconfluent` (evidence is monotone-forever
— a forked peer cannot gossip its way back to innocence), and
`no_unilateral_evidence` (honest singletons frame nobody). The
content-addressing remark in `Acyclicity.lean` — rank implied by hash-linking,
a reference cycle needing a hash cycle — is the blocklace's structural
premise, and the repo keeps their discipline of stating collision resistance
as a cryptographic premise rather than a theorem.

*Where we differ.* They build the protocols — detection, exclusion,
finite-harm bounds; we prove only the lattice-monotonicity core over a bare
observation set, with opaque `Nat` ids and nothing about signatures or hashes.

**Martin Kleppmann — "Making CRDTs Byzantine Fault Tolerant", PaPoC '22,
Rennes, 2022.**

*What it establishes.* Byzantine fault tolerance can be *retrofitted* to
existing op-based CRDTs — hash-DAG the updates, propagate between correct
nodes — and, unlike consensus, tolerates arbitrarily many Byzantine nodes,
making the construction immune to Sybil attacks in open peer-to-peer systems.

*What this repo takes.* `Causality.lean`'s header cites it as reaching the
same architecture as the blocklace: hash-graph plus equivocation-as-evidence.
`fork_evidence_iconfluent` is the safety half of that architecture in
miniature, and the grounded/hash-DAG rank of `Acyclicity.lean` is the same
structural trick doing convergence work.

*Where we differ.* Eventual delivery among correct nodes — the liveness half,
and the paper's careful network reasoning — has no counterpart here; there is
no network and no adversary model, only the monotone-evidence lattice fact.

**Kegan Dougal — "ERA: Epoch-Resolved Arbitration for Duelling Admins in
Group Management CRDTs", PaPoC '26, Edinburgh, 2026.**

*What it establishes.* In group-management CRDTs (Matrix, Keyhive), the
materialised view of the hash-DAG can *roll back* previously applied events
when concurrent events arrive — acute for mutual revocation ("Duelling
Admins"), where a Byzantine admin can exploit concurrency and backdating to
win the duel. ERA proposes a mutually trusted **finality arbiter** issuing
epoch events, giving a bounded total order within epochs and a finality
stronger than causal stability, while preserving availability between epochs.

*What this repo takes.* ERA's Rollback definition — a concurrent event whose
arrival changes the materialised view — is precisely the phenomenon
`Move.view_not_stable` proves *inherent* to derived views over grow-only
logs: growth of the monotone substrate does not grow the view. And ERA's
threat model overlaps `Causality.lean`'s: its detectable-backdating case is
our `ForkEvidence` shape (an author concurrent with itself).

*Where we differ.* Two legitimate exits again. ERA buys finality by
introducing a trusted arbiter role — structured, batched escalation. Our
miniatures stay at zero coordination and treat the rollback as a designed-for,
*surfaced* anomaly instead. And ERA's undetectable-backdating attack is
outside this repo's model entirely: `fork_evidence_iconfluent` speaks only to
equivocation that leaves two signed artifacts.

## Replicated computation: holes, partial values, and progress

*This section exists because `Uwueave/Holes.lean` and `Uwueave/Choreo.lean`
replicate a **computation** rather than a datum, and because a design memo
(`FORCODEX.md` §4) claimed novelty in this neighbourhood that four of these
five papers refute or narrow. Read the ⚠ entries before citing us as first at
anything here.*

**Lindsey Kuper, Ryan R. Newton — "LVars: Lattice-based Data Structures for
Deterministic Parallelism", FHPC 2013.**

*What it establishes.* Shared-memory cells whose contents are elements of a
join-semilattice, mutated only by monotone joins, read only through
**threshold reads** that *block* until the value crosses a declared threshold
set. Under those restrictions parallel programs are deterministic; the later
"freeze after writing" extension adds a `freeze` that permits an exact read at
the cost of *quasi*-determinism (a write after a freeze is an error).

*What this repo takes.* One corner of `Holes.lean`'s triangulation, and the
thing it refuses. Determinism-by-blocking is unavailable to a replica whose
peer is offline for a week, and the cost of refusing to block is a theorem
here rather than a design note: `determinacy_not_iconfluent` (at most one
candidate is not I-confluent — `Ceiling.uniqueness_ceiling` at a new carrier)
and its pullback `determinate_result_not_iconfluent`, whose clash pair is two
replicas each holding one candidate world and each computing a perfectly
determinate answer. `Holes.Stable` / `SealsTo` / `seal_survives_stable` are
freeze's role played by a *precondition on a collapse* instead of a wait on a
read; `unstable_seal_clash` is the concrete price of collapsing without it.

*Where we differ, and one thing to stop saying.* No blocking, no runtime, no
determinism result — quasi- or otherwise; nothing here is a parallelism story.
⚠ And the slogan "**LVars block, Hazel doesn't**" (`FORCODEX.md` §4.1) is
**kept only as a provocation and now labelled one**: an LVar threshold read
waits on a *synchronization* unknown (the value exists; the read waits for it
to cross a bound), while a Hazel hole is *syntactic/semantic incompleteness*
(no term has been written there). Those are two unknowns, not one unknown
under two policies, and the bridge between them is to be built rather than
asserted.

**Cyrus Omar, Ian Voysey, Ravi Chugh, Matthew A. Hammer — "Live Functional
Programming with Typed Holes", POPL 2019.**

*What it establishes.* An incomplete program still has meaning: holes are
membranes, evaluation proceeds *around* them yielding an indeterminate result
that refines as holes are filled, and hole closures capture the environment at
each hole so that live feedback is available at every edit state.

*What this repo takes.* The shape of carrying not-having-an-answer as a
**value** rather than as a spinner or a lie — `Holes.lean`'s `Partial α` is
`GSet World` with `hole` the empty candidate set, and §6's refusal to collapse
prematurely is Hazel's stance ("an indeterminate result is a result") given a
lattice-side account. The name of the file is a debt to this paper.

*Where we differ.* Everything that makes Hazel Hazel: a type system, a
bidirectional static semantics for incomplete terms, hole closures, an editor,
liveness. `Holes.lean` has **no expression language at all** — `f : World → α`
is an arbitrary Lean function, which is exactly why `evalSet_hom` holds with
no side conditions and exactly why nothing here can *classify* a program. Our
"hole" is also not their hole: theirs is a missing term, ours is an unreceived
replica's contribution, and §4's proposal that these are the same thing is a
conjecture (see the ⚠ under LVars above, and Grove below).

**Nick Rioux, Steve Zdancewic — "Functional Meaning for Parallel Streaming"
(λ∨), arXiv:2504.02975, 2025.**
*(⚠ **RETRACTION SOURCE** — prior art for a generic `Partial α`.)*

*What it establishes.* λ∨, an untyped call-by-value lambda calculus in which
**every value is a point of a streaming order**, all computations are monotone
with respect to it, and a parallel `∨` runs two computations simultaneously
and streams out their join. The streaming order coincides with the Scott
approximation order, giving a computationally adequate domain-theoretic model.
Threshold queries are the elimination form (pattern matching *is* a threshold
query); the monotone design makes set difference and absence-testing
**inexpressible**, so an action taken on what is currently present stays
valid. The taxonomy is finer than a single ⊥: `⊥` is a computation that
produced nothing and propagates like divergence, `⊥v` is *something produced
about which nothing is known*, and `⊤` is an **error** representing an
inconsistent result (a join of incomparable symbols).

*What this repo takes.* A correction and a measuring stick. `FORCODEX.md` §4.5
sketched `Partial α` — "a refinement lattice with `⊥ = ⟨hole⟩`" — as buildable
core; λ∨ is that idea already built as a general-purpose calculus with a
model, and any future `Partial α` here must be described relative to it rather
than as new. Its `⊥` / `⊥v` / `⊤` split is a distinction `Holes.lean` does
**not** currently make: our lattice has `hole` (no candidates) and
multi-candidate results, and no separate ambiguity error — a fork is a value
we intend to carry, not a `⊤`. That is a defensible difference for a loom
(forks are the product) and it is a difference, not an improvement.

*Where we differ.* We have no calculus, no operational semantics, no adequacy
theorem, and no syntax to be monotone *by construction* — `evalSet` pushes an
arbitrary function over a candidate set and proves the image distributes over
the join, which is a much smaller fact. λ∨'s inexpressibility-of-absence is
the design discipline `Holes.lean` would need before it could claim its
`Partial α` is well-behaved for *all* programs rather than for images.

**Michael D. Adams, Eric Griffis, Thomas J. Porter, Sundara Vishnu Satish,
Eric Zhao, Cyrus Omar — "Grove: A Bidirectionally Typed Collaborative
Structure Editor Calculus", POPL 2025.**
*(NOT ARCHIVED — relayed from an external review (codex) and the paper's
published abstract; ⚠ **RETRACTION SOURCE**. Every claim in this entry is
bounded by that indirection.)*

*What it establishes (as reported).* A bidirectionally typed calculus for
**collaborative** structure editing: edits form a CmRDT log replicated between
collaborators, so there is no patch synthesis and no three-way merge, and the
conflicts that a merge would have had to resolve are instead **represented in
the term with holes**. Hazel's static and dynamic account of incompleteness,
carried into a replicated multi-author setting.

*What this repo takes.* A retraction. `FORCODEX.md` §4 treated "typed holes ×
replicated collaborative editing" as unclaimed ground; **it is claimed, at
POPL, by Hazel's own authors.** Nothing in `Holes.lean` may be described as
first at that pairing. What Grove (as reported) does not do is ask whether an
*application invariant on the computed result* survives the merge — which is
`result_invariant_transfers` and `determinate_result_not_iconfluent` — and
that is the whole of the remaining delta, stated at its true size.

*Where we differ.* We have not read the primary source; read it before citing
this entry further. Structurally: Grove's holes are in a *program being
edited*, ours are in a *value being computed over replicated data*, and the
two coincide only if you accept §4's conjecture that those are one kind of
hole — which, per the LVars entry above, is a conjecture.

**Matthias Brun, Sára Decova, Andrea Lattuada, Dmitriy Traytel — "Verified
Progress Tracking for Timely Dataflow", ITP 2021.**

*What it establishes.* Timely Dataflow's progress-tracking protocol modeled in
Isabelle/HOL as two independent transition systems and proved **safe**,
separately and in combination, together with abstract assumptions on dataflow
programs sufficient for safety that had not previously been written down. The
central objects are **frontiers** — antichains of timestamps that lower-bound
what may still arrive at an operator's input — and **capabilities**, the
transferable right to produce output at a time.

*What this repo takes.* The shape our "stability licence" should have if it
ever becomes concrete. `Holes.Stable Arriving P` is deliberately abstract in
what may still arrive; a frontier is exactly that predicate, made a *data
structure*, distributed by a protocol, with the safety argument
machine-checked. It is also the best existing answer to `FORCODEX.md` §4.5's
open question about **attributed** holes: an antichain frontier *is*
attributed incompleteness, and it enters the system as protocol state rather
than as replica identity smuggled into the lattice.

*Where we differ.* Everything: there is no protocol here, no timestamps, no
operators, no capabilities, and no liveness or progress theorem of any kind
(`Liveness.lean` proves fair delivery attains the lub and explicitly does not
model ∞-often delivery). Their result is safety of a real deployed protocol;
ours is a lattice fact about images. Isabelle/HOL, not Lean.

## Local-first programming models, and where coordination is placed

*⚠ Two of these four are retraction sources. This section is the neighbourhood
`FORCODEX.md` §4.3 and §5.4 claimed was empty; it is not, and it was not.*

**Julian Haas, Ragnar Mogk, Elena Yanakieva, Annette Bieniusa, Mira Mezini —
"LoRe: A Programming Model for Verifiably Safe Local-First Software",
arXiv:2304.07133, 2023.**
*(⚠ **RETRACTION SOURCE** — it kills "nobody currently offers all three".)*

*What it establishes.* A programming model and compiler for local-first
applications built on three constructs: **reactives** (values changing in time
*and space*, replicated across devices, composed as a declarative dataflow
graph), **invariants** (first-order safety properties that must hold whenever
the application meets the outside world), and **interactions** (the boundary
with that world, processed atomically at one device). Static verification
discharges the invariants against the dataflow, **precisely identifying the
interactions whose concurrency would violate one**, and the compiler
**generates a coordination protocol for exactly those** — everything else
propagates in causal order. It emits verified executable code, with a
formalized proof principle behind the automation, and it targets peer-to-peer
local-first rather than geo-replicated databases: no central authority,
offline availability, and the safety of *derived* data verified "all the way
down" rather than at a store's API.

*What this repo takes.* A deleted claim. `FORCODEX.md` §4.3 proposed three
verdicts on one program — deterministic? coordination-free? does my invariant
on the result survive? — and asserted "nobody currently offers all three",
calling the third "the piece nobody has". **LoRe is essentially that
combination, shipping, three years earlier**, and the claim is gone. What
survives is narrower and is what this library should be measured on: LoRe's
verdict is **binary and per-interaction** (coordinate here, don't coordinate
there) discharged by an SMT backend, and it has no *segmented* verdict
(`Segmented.lean`, `SeamAlgebra.lean` — an invariant that fails globally and
runs free within a seam, with a calculus for when two seams collapse into
one), no coordination-**frequency** quantity (`Cost.crossings`,
`coordination_forced`), no counterexample-as-deliverable discipline
(`escalation_witness`), and no proof terms in a kernel under a total axiom
gate.

*Where we differ, honestly.* LoRe is a language with a compiler, an
evaluation, and generated protocols; this is a library of classified
miniatures with a schema CLI. On the axis that matters to a user — *can I
write my app in it* — LoRe is far ahead, and the correct posture is that
nobody here has yet measured against it.

**Roland Kuhn, Hernán Melgratti, Emilio Tuosto — "Behavioural Types for
Local-First Software", ECOOP 2023, LIPIcs 263:15.**
*(NOT ARCHIVED — relayed from an external review (codex) and the published
abstract; ⚠ **RETRACTION SOURCE**.)*

*What it establishes (as reported).* **Swarm protocols**: a system specified
from a global viewpoint and **projected** onto *machines* — local
specifications of peers — where peers communicate by **event notification**
over replicated logs rather than point-to-point message passing. Under
well-formedness conditions on the protocol, consistency is eventually
recovered and each conforming machine's locally observable behaviour
eventually matches the global specification, with local progress preserved
while peers are unavailable.

*What this repo takes.* A retraction, and the shape of the claim that survives
it. `FORCODEX.md` §4.7 said a literature search "found **nothing** at the
choreography × CRDT junction". That is withdrawn: choreographic projection
over eventually-consistent replicated state, with progress under
unavailability, is exactly this paper. `Choreo.lean`'s header carries the
retraction and the narrower claim we can defend — *no system we could find
combines projected local-first protocols with a coordination verdict derived
from **I-confluence** (`coordination_free_iff_iconfluent`) **and** a seam
refinement over it (`seam_coordination_free`)*. Kuhn et al. ask whether a
projection conforms and eventually converges; they do not ask whether an
application invariant survives the merge, and they carry no segmented notion.

*Where we differ.* We have not read the primary source. Structurally, and
subject to that: they have an operational communication model (event
notification, machines, unavailability) and we have none — `Choreo.lean`'s
asynchrony is state-based gossip with a synchronous roster barrier, labelled
TERMINAL in its own non-claims. Their well-formedness conditions and eventual
behavioural conformance have no counterpart here; our `projection_sound` is a
pointwise state equality on a finite, recursion-free fragment.

**Nicholas Schiefer, Geoffrey Litt, Daniel Jackson — "Merge What You Can, Fork
What You Can't: Managing Data Integrity in Local-First Software",
PaPoC '22, Rennes, 2022.**

*What it establishes.* The systems antecedent of "forks are the product". In a
local-first architecture there is a real tension between merging concurrent
changes without user intervention and maintaining data integrity constraints,
and the paper resolves it by refusing the usual assumption that all users must
converge to a single shared state as fast as possible. **Forking histories**:
on conflicting writes, expose *multiple coexisting event histories* that users
can see and edit, so integrity constraints hold **within each history** while
reconciliation is deferred to a human at a time of their choosing. Motivated
by "digital gardens" — photo libraries, note systems, reference managers —
where the data is large enough that a bad merge is undetectable and valuable
enough that it is catastrophic.

*What this repo takes.* The design stance `MVRegister.lean` and `Holes.lean`
make lattice-shaped. `conflict_surfaces` (concurrent writes both survive) and
`resolution_is_a_write` (resolving is an ordinary write, so no special
resolution path exists for a merge to get wrong) are the register-sized
version of forking histories; `Holes.lean`'s refusal to collapse a
multi-candidate result — a fork is a **final answer**, and collapse is a
separate operation with a precondition (`SealsTo` under `Stable`) — is the
same call at computation altitude. The paper is also the honest source for the
README's framing that keeping the fork is a *design*, not a failure to merge.

*Where we differ.* They propose a system design (history forking, its UI, its
storage) and we prove properties of a merge lattice; nothing here manages
histories, and the `MVRegister` miniature keeps a set of concurrent values
rather than a set of *histories*, which is strictly less. Their integrity
constraints are maintained per-history by construction; ours are classified
and either survive the join or hand you the pair that breaks it.

**Peter Alvaro, Neil Conway, Joseph M. Hellerstein, David Maier — "Blazes:
Coordination Analysis for Distributed Programs", ICDE 2014
(arXiv:1309.3324).** · **Sudip Roy, Lucja Kot, Gabriel Bender, Bailu Ding,
Hossein Hojjat, Christoph Koch, Nate Foster, Johannes Gehrke — "The
Homeostasis Protocol: Avoiding Transaction Coordination Through Program
Analysis", SIGMOD 2015 (arXiv:1403.2307).**
*(NEITHER ARCHIVED — relayed from an external review (codex) and the papers'
abstracts; ⚠ **RETRACTION SOURCE** for the cost claim.)*

*What they establish (as reported).* **Blazes** analyses a dataflow model of a
distributed program (inferred directly from the source, if it is Bloom),
identifies the locations that require coordination, and synthesizes
application-specific coordination code that outperforms general-purpose
protocols — naming two distinct strategies, *ordering* and **sealing**, where
sealing declares a partition of the input stream closed so an aggregate over
it may be emitted without waiting for the rest of the world. **Homeostasis**
answers "how much, how often": program analysis extracts how much inconsistency
a transaction can tolerate, sites are issued **treaties**, and a site runs
without communicating for exactly as long as its treaty holds.

*What this repo takes.* Two retractions in one. `FORCODEX.md` §5.4 asked
whether "how often must I coordinate, given this workload?" existed as a
formal quantity and guessed it did not — Homeostasis is that quantity, derived
from the program and workload, in 2015. And §4.2's "stability event" is
Blazes' **sealing**, as a compiler-inserted mechanism with a placement
analysis behind it, in 2014. `Cost.lean` remains worth having and its framing
changes: `coordination_forced` derives a **floor** from clash blocks in the
*spec*, for every seam in every universe, which is a different object from a
treaty (a floor is an impossibility; a treaty is an allowance), and
`crossings` counts σ-changes along a workload. "A proof-side account of a
quantity the systems literature has had for a decade" is the accurate
description; "nobody has this" was not.

*Where we differ.* We have not read either primary source; read them before
citing this entry further. Neither analysis, synthesis, nor protocol exists
here — `Cost.lean` counts and proves a lower bound over a given seam and
workload and generates nothing.

## Systems

**Héctor Sanjuán, Samuli Pöyhtäri, Pedro Teixeira, Ioannis Psaras —
"Merkle-CRDTs: Merkle-DAGs meet CRDTs", arXiv:2004.00107, 2020.**

*What it establishes.* Merkle-DAGs as a transport and persistence layer for
CRDT payloads: the **Merkle-Clock** — the hash-DAG itself as a logical clock —
replaces version vectors, giving per-object causal consistency with no
delivery guarantees, no membership knowledge, and very large dynamic replica
sets (the IPFS setting), at the cost of the DAG's growth and traversal.

*What this repo takes.* The content-addressing remark in `Acyclicity.lean` is
the Merkle-Clock observation done as lattice theorems: height in the hash DAG
is a rank, every edge descends in it by construction, so
`grounded_iconfluent` + `grounded_acyclic` (packaged as `causal_dag_free`)
explain *why* a Merkle-DAG store needs no cycle check at any replication
scale. The Rust `causal::CausalWeave` — blake3-derived ids, parents fixed at
creation, merge as skip-if-present union — is a store of exactly this shape.

*Where we differ.* Their systems layer (DAG-Syncer, Broadcaster, DHT/PubSub)
has no counterpart here, and the hash-cycle impossibility stays an explicit
cryptographic premise on our side — Lean has proved nothing about SHA-256 or
blake3.

**Romain Vaillant, Dimitrios Vasilas, Marc Shapiro, Thuy Linh Nguyen —
"CRDTs for truly concurrent file systems", 2021 (preprint self-dated
July 6, 2021).**

*What it establishes.* ElmerFS: a geo-replicated file system built on CRDTs,
whose conflict-resolution rules are chosen for user intuition — preserve the
effects of conflicting operations where possible, introduce nothing the
operations didn't express — so that a user can *complement or reverse* a
resolved conflict using ordinary file operations, all while keeping POSIX
compatibility.

*What this repo takes.* Context, plus one named kinship: "the resolution
should be reversible by ordinary operations" is the design stance
`MVRegister.resolution_is_a_write` gives a lattice-side account of — no
special resolution case exists for the merge to get wrong. ElmerFS is also
the fully-grown instance of `Weave.lean`'s claim that every filesystem-shaped
application eventually meets the move conflict and must pick a policy.

*Where we differ.* Names, paths, inodes, hard links, POSIX semantics — the
things that make a filesystem a filesystem — are not modeled anywhere in this
repo.

---

*A last honesty note, repo-side: every mapping above is to a machine-checked
miniature, and the miniatures are small on purpose. Where an entry says a
paper's result "is" some theorem here, read: the load-bearing idea appears
here at toy scale with its proof obligations discharged — never that the
paper's full result has been formalized. `Audit.lean` pins what the theorems
actually depend on.*
