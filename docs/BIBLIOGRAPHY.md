# Annotated bibliography

The papers behind lean-uwueave's theorems, and the honest seams between them.
Each entry says what the paper establishes, what this repo takes from it (with
the actual theorem and file names, so the mapping is checkable rather than
vibes), and where we differ or take nothing. "Context only" is a real verdict
here, not a slight — half the value of a library this small is knowing exactly
which ideas it *declined*.

**Where the PDFs live:** the collection is kept in the maintainers' paperbin,
not in this repository — ask and we'll point you at it. Two references could
not be archived: **Najafzadeh–Shapiro–Eugster (VMCAI 2018)**, which we cite
anyway through the Kleppmann et al. move-op paper's related-work discussion of
it (its entry below is explicit about that indirection), and **Yu's
causal-length set** (the design `ORSet.lean`'s `CLSet` is named for) — the
collection's nearest archived neighbor is Lavoie's ∞P-Set note, which presents
the same odd/even-counter construction and credits its earlier appearance in
Yu, Elvinger & Ignat's undo framework.

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

*What this repo takes.* Context only — and deliberately so. This paper is the
canonical evidence that sequence semantics is its own research area with its
own subtle invariants, which is exactly why the README scopes text out
("nothing here competes with loro's sequence CRDTs; this is the structural
layer around them"). No theorem in this repo addresses lists or interleaving.

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
