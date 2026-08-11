# TRUST — three ledgers

*What this repository asks you to believe, sorted by what kind of belief it is.*

This file exists because an external reviewer — **codex** — read our claim that
three boundaries were *terminal* (signature unforgeability, the C backend TCB,
Bailis's full generality) and demolished it, along with a habit it had grown
out of. His two findings, restated so they can be checked against this file:

1. **`#audit_floor` establishes logical hygiene, not semantic adequacy.** The
   gate proves that no proof in this tree leans on anything outside Lean's own
   axiom floor. It cannot prove that any of those theorems is *about* the thing
   we say it is about.
2. **Calling everything "premises" hides where more work would reduce trust.**
   One list mixes a hardness assumption nobody can discharge with an
   engineering obligation someone could close next month. Lumping them makes
   the second look like the first — which is exactly how a boundary stops
   being worked on.

So: three ledgers, not one list. Every row says what it rests on and whether
it is **irreducibly a premise** or a **transmutable obligation with a named
next step**.

`Uwueave/Gated.lean`'s honesty section already labels its own items
⟨TERMINAL⟩ / ⟨UNDONE⟩ — that section is the seed of this file and was more
careful than the briefing document that summarised it: it wrote
"⟨TERMINAL, **at this layer**⟩" where `FORCODEX.md` wrote "terminal". The
qualifier was the whole argument, and it got dropped in transit.

---

## How to read a row

**PREMISE** — no work inside this repository removes it. Either it is a
mathematical assumption the discipline itself rests on (kernel soundness) or a
computational hardness assumption the world has not settled (collision
resistance). A premise is not a defect; an *undecomposed* premise is.

**OBLIGATION** — currently trusted, but closable by identified work. The row
must name the work. "Large" is not a disqualifier; "unnamed" is.

**NARROWABLE** — the third category, which the two-way split hides. The gap
between a theorem's statement and the intent it was written to capture is not
assumed (nothing is asserted) and not closable (there is no formal object on
the far side to prove anything about). It is *narrowed* — by refutable
witnesses, executable differentials, and adversarial readers — and it never
reaches zero. Treating it as a premise makes it sound settled; treating it as
an obligation makes it sound schedulable. It is neither.

Facts below were read out of the tree on **2026-08-11**, mid-wave. Counts move;
mechanisms are what to check.

---

## Ledger 1 — the logical TCB

*What must hold for "the proof went through" to mean anything.*

| Item | Rests on | Verdict | Next step |
|---|---|---|---|
| Lean's kernel | The soundness of Lean 4's type theory and of the kernel that implements it. Every theorem here is a kernel-accepted term and nothing else. | **PREMISE**, with a transmutable edge | Independent checking. **Lean4Lean** (Carneiro) is a formalization of Lean's metatheory and an independent checker written in Lean — and its development *found a soundness bug in the Lean 4 kernel*, which is the whole argument for doing it. Re-checking this tree under an independent checker is a real, bounded task; it does not remove the premise, it stops one implementation from being its sole custodian. |
| The axiom floor `{propext, Classical.choice, Quot.sound}` | Classical logic with quotients. This is what "a Lean proof" already means; the repo adds nothing to it. | **PREMISE** | None, and none is wanted. Note what the floor is *for*: `#audit_floor` exists for what it excludes — `sorryAx` (a hole that would otherwise ship as a warning) and `Lean.ofReduceBool`/`ofReduceNat` (`native_decide`, which trusts the compiled evaluator, i.e. quietly imports Ledger 2 into Ledger 1). |
| `#audit_floor` itself | An unverified `elab` metaprogram in `Uwueave/Audit.lean`: it filters `env.constants` by the `Uwueave` prefix, calls `collectAxioms`, and throws. It is not a theorem. It audits the tree from *inside* the tree. | **OBLIGATION** | It already carries a vacuity tripwire (fewer than 300 constants in the walk is a hard failure — at the time of writing the walk sees 3778). The next step is a *second, differently-shaped* check that does not share the first's failure mode: an out-of-band `#print axioms` sweep over the ledger names, run by a script rather than by the elaborator being audited. A gate that cannot go red is not a gate; a gate that can only go red one way is halfway there. |
| Statement ⟷ intended protocol | Reading. Nothing else. `necessity` is a theorem; that it says what Bailis says is a judgement made by humans and models looking at both. | **NARROWABLE** | The house bar already in use: a model must be **satisfiable and refutable**, never vacuous in either direction — `Necessity.lean` carries both (`gset_true_is_cfcs` on one side, `atMostOneBit_necessity` on the other). Extend that bar from models to *statements*: every keystone should have a witness that makes it fire and a neighbouring statement that a witness refutes. |
| Model completeness — a missing operation or failure mode | Per-module "what this does NOT capture" sections, written by the author of the module. | **NARROWABLE**, per row **OBLIGATION** | These lists are good and they are self-reported. `Necessity.lean` names five gaps (multi-hop schedules, liveness, Byzantine replicas, op-based causal broadcast, interactive transactions); `Liveness.lean` names four; `Era.lean` names the hash DAG, causal-closure computation, backdating detection, arbiter lists and timestamps. The transmutable half is that each named gap is a work item with a paper behind it. The narrowable half is the gap nobody listed. |
| Reachability ⟷ the shipping API | `CausalReach.lean` models causal cuts and tags a clash Live or LatticeOnly. `docs/MAP.md`'s reachability axis is derived **only from module docstrings** and refuses to guess — which is honest, and is a docstring-level judgement, not a machine-checked one. | **OBLIGATION** | `KernelCFCS.lean` is the pattern: embed the *shipping* op alphabet into the model (`Necessity.Impl` over `GSet Exec.Op`) so reachability is asked of the ops the kernel actually replays. It exists for the move kernel only. Doing the same for `SeqKernel` and `EraKernel`, and then for the Rust crate's public op vocabulary, converts a docstring axis into a theorem axis. |
| Serialized bytes ⟷ the proved abstract state | Partly proved, and the proved part is real: `replay` is *definitionally* decode → `absReplay` → encode; `replay_encodeRequest` and the four `decode*_encodeRequest` lemmas close the input codec against the canonical encoder; `decode_encode_id` and `getWord_encodeView` close the output codec at word level. | **OBLIGATION**, partly paid | ⚠ The abstract-to-concrete *symbol* bridge (`Move.lean` §3, `absReplay_matches_miniInterp`) holds on the **2-node universe only** — its own header says so. Generalizing that bridge past two nodes, and giving the seq and era kernels the codec closure the move kernel has, is the named work. |
| Docstring ⟷ theorem | Authorial discipline plus a house rule ("docstrings must match statements exactly"). No mechanism enforces it. | **NARROWABLE**, with a mechanism seed | There *is* one partial mechanism, and it should grow: `rust/src/bin/uwueave-check.rs` resolves its theorem citations through real namespace structure and checks verdict **polarity** against the Lean statements, so the CLI cannot advertise a verdict the theorem contradicts. That covers citations, not prose. A docstring is an unchecked claim in the same TCB as everything else here. |

**Eight rows: two PREMISE, three OBLIGATION, three NARROWABLE.**

---

## Ledger 2 — the execution TCB

*What must hold for the shipping artifact to behave like the theorems.*

This is the ledger codex most wanted broken up, and he is right: "the C backend"
is not one boundary, it is at least five, and only some of them are hard. None
of them is terminal. **Verified compilation is an existence proof, not a
hope** — CompCert is a C compiler with a machine-checked proof of semantic
preservation from source to assembly, and CakeML is a functional language whose
compiler is verified down to machine code. Both are the shape of the thing this
row needs; neither is currently in the pipeline below.

| Item | Rests on | Verdict | Next step |
|---|---|---|---|
| Lean's C code generator | `lake build` emits `.lake/build/ir/**/*.c` from the Lean IR, including the `@[export]` entry points. Unverified, and the semantic distance from `Uwueave.Exec.replay` to the emitted C is the largest single jump in this repo. | **OBLIGATION** | Three real routes, in ascending cost: **translation validation** per emitted function (check the C against the IR for the handful of exported kernels, not the whole tree); a **proved exporter subset** (the kernels use a narrow fragment — arrays, `Nat`/`UInt64`, structures, no closures over the FFI boundary); and full verified compilation, which CakeML shows is achievable for a functional source language. ⚠ CompCert does **not** cover this row — it starts at C. |
| The C compiler and linker | `cc::Build` at `opt_level(2)`, warnings off, whatever the host toolchain is. | **OBLIGATION** | Compile the emitted C with **CompCert** and link that. This is the cheapest experiment on the page: the surface is the emitted kernels plus `shim.c`, and the only question is whether Lean's emitted C sits inside CompCert's supported subset. Answering that question is a day, not a project — and it converts the lower half of "the C backend" from trusted to proved. |
| The Lean runtime (`libleanshared`) | Reference counting, the allocator, `lean_alloc_sarray`, `lean_dec_ref`, module initializers. Linked as a dylib from the toolchain, with an rpath baked in by `build.rs`. | **OBLIGATION** | Same two techniques as the row above, with one specific hazard on top: refcount discipline **across** the FFI boundary is manual here, and the ownership contract ("`uwueave_replay_kernel` consumes `arr`") lives in a C comment. State that contract as a spec first; you cannot verify what is not written down. |
| `shim.c` | 120 lines, six exported functions (`init`, `replay`, `seq`, `era`, `request_canonical`, `free`), each doing the same thing: copy bytes in, call the kernel, copy bytes out, `malloc` the result for the caller to free. | **OBLIGATION**, and the cheapest one here | It is small enough to *specify and verify* — this is squarely inside what VST or Frama-C handle — or to eliminate by generating it. ⚠ Note the drift worth fixing while someone is in here: `rust/src/lib.rs` and `FORCODEX.md` both describe a "three-function shim"; there are six. |
| The ABI and the FFI boundary | `extern "C"` declarations in `rust/src/ffi.rs` matching `shim.c` by hand; `*mut u8` + `std::slice::from_raw_parts` + `shim_uweave_free`; a `std::sync::Once` for runtime init. Nothing checks the two declarations agree. | **OBLIGATION** | ABI/FFI proofs are a live research area and a large step. The bounded first step is smaller and worth doing regardless: generate the `extern "C"` block from the same source as `shim.c` so a signature change cannot silently disagree, and write the safety contract per call rather than per module. |
| Rust `unsafe` | **8 occurrences, all of them in `rust/src/ffi.rs`** — no `unsafe` anywhere else in the crate. That concentration is a genuine design win and should be defended. | **OBLIGATION** | Miri cannot follow execution across FFI, so "run Miri" is not the answer here. The honest steps are: keep the concentration (any new `unsafe` outside `ffi.rs` is a regression), and give each call an explicit written safety contract discharging the pointer/length/ownership obligations the C side imposes. |
| The Rust marshaller | `movelog.rs` builds the request bytes. It is checked byte-for-byte against the **proven** canonical encoder via `ffi::request_canonical` — but through `debug_assert!` (`movelog.rs:322`), so **the check is compiled out of release builds**. And it is test evidence either way: Rust has no formal semantics to prove against. | **OBLIGATION**, with an unusually good next step | Do not strengthen the differential — **delete the marshaller**. `Exec.encodeRequest` is already written in Lean and already proved to round-trip through all four decoders. Export it. Then Rust marshals nothing, the differential has nothing to compare, and this row leaves the ledger instead of getting a better test. (Second-best, if the export is deferred: make the assert unconditional, so release builds are not strictly less checked than debug.) |
| Storage and index glue | `causal.rs`, `movelog.rs`, `seq.rs`, `era.rs`, `weave.rs` — `BTreeMap`/`BTreeSet` stores, derived indexes, merge plumbing. Property tests (`rust/tests/properties.rs`) assert laws over the real crate through the real kernel. | **OBLIGATION** | The tests are good tests and zero formal evidence, which `lib.rs` already says. The transmutation is the same one as the row above: every *decision* these modules make that could live in Lean should, leaving them holding only storage. The house rule is already "no Rust twin of a decision procedure"; this row is the remaining distance to it. |
| The build wiring | ⚠ `rust/build.rs` runs `lake build`; **if that build fails but `Uwueave.c` is already on disk, the crate compiles and links the stale C anyway** (`build.rs:25-31`). Separately, `lib.rs` documents that plain `lake build` does not emit `SeqKernel.c` / `EraKernel.c` until the root module imports them, so those two kernels can be linked stale by ordinary use. | **OBLIGATION** — and this is a live integrity hazard, not a theoretical one | Two fixes, both small. Wire `Uwueave.SeqKernel` and `Uwueave.EraKernel` into the root module so `lake build` keeps every emitted `.c` fresh (already named in `lib.rs` as the orchestrator's job). Then make `build.rs` **fail** when `lake build` fails, rather than falling back to whatever C is lying around: a green `cargo test` must not be reachable from a red `lake build`. |
| Persistence and durability | **Nothing.** There is no persistence layer: every store is an in-memory `BTreeMap`/`BTreeSet`, `Cargo.toml`'s only runtime dependency is `blake3`, there is no serde, no file format, and `std::fs` appears solely in the CLI reading a schema file. | Not a premise — an **absent component** | Listing "storage durability" as a trusted assumption would be a lie of shape: nothing is trusted because nothing exists. What matters is what happens when it does. When a durable format lands, it gets the codec treatment this repo already knows how to apply — a *proved* encoder in Lean with round-trip theorems, as `encodeRequest` has — and not a `#[derive(Serialize)]` that reintroduces an unproved wire format at the bottom of the stack. |

**Ten rows: zero PREMISE, nine OBLIGATION, one absent component.** That is the
headline of this ledger, and it is the correction codex asked for: *nothing in
the execution stack is terminal.* It is all engineering, some of it large, none
of it impossible, and two rows of it (CompCert on the emitted C; exporting
`encodeRequest`) are small enough to do this month.

---

## Ledger 3 — environment and model premises

*What must hold about the world for the theorems to bind to a deployment.*

### 3a. Delivery, identity, membership

| Item | Rests on | Verdict | Next step |
|---|---|---|---|
| Fair delivery | `Liveness.lean`'s `FairOn`: a **finite covering** — every participant's received set is membership-equivalent to the issued set. Under it, every replica reaches `joinAll`; under an unfair schedule there is a constructive starvation witness. | **PREMISE** at the model boundary, with transmutable edges | The model is deliberately not a network. Its own non-capture list names the edges: loss as a probability, RTT, topology dynamics, "eventually" as a temporal modality over infinite traces, and multi-hop epidemic diameter for `n > 2` under pull-only schedules. Each is a theorem someone could write; the coinductive-stream version of fairness is the standard next rung. |
| Identity and authenticity | **Nothing in the tree.** A `UserId` is a bare `u64` anyone may write into an op (`weave.rs`); `Authority.lean` puts authentication "outside this model entirely"; `Gated.lean` states the kernel "authenticates nothing and is not asked to". | **OBLIGATION** — see 3b, where this decomposes | The gate bounds what a cited grant can **do**, never who may cite it. That is a coherent design; it is not a discharged premise. |
| Membership closure | `Era.lean` §8 carries the invited/member/left lifecycle beside §3's role codes. ⚠ Its own docstring records that **§3's promote does not check membership** — an invitation alone does not gate it — so the lifecycle is a second, parallel authorisation predicate rather than a strengthening of the first. `GatedEra.lean` derives membership from causal closure with no signatures and no backdating detection. | **OBLIGATION** | Compose the two authorisation predicates instead of running them in parallel, and prove the composite is what the kernel decides — the same move `Gated.lean` §5 already made once (`kernel_gate_agrees_gatedOps`), which is why this is a known-shaped task rather than an open one. |
| Trusted announcements (Era's arbiter) | ERA's own protocol design: a distinguished peer periodically announces epoch cuts that **order** events without naming winners. Nobody coordinates; replicas never wait; the price is trust in one announcement stream plus rollback of the unfinalised suffix. | **PREMISE** of the protocol — and a smaller one than it looks | The equivocation case is already handled, not assumed away: an event named by several cuts takes the least epoch, so a **concurrently-announcing arbiter degrades to deterministic re-ordering, never divergence** (`resolve_same_sets` holds with no honesty hypothesis). What remains is named: prefix stability under cut growth is *not* claimed, and backdating detection, arbiter lists and transparency are out of scope here — the paper answers them with signatures and fraud proofs, which is Ledger 3b's work, not a new premise. |
| Clock uniqueness and tiebreaks | The kernel's total order is `(lamport, replica, child, dest)` with the request index breaking ties — which only identical duplicate ops can produce, so the sort is stable and determinism does **not** depend on replica ids being distinct. `Catalog.lean` §3 records that LWW's *value* tiebreak is load-bearing: without it two writes at the same timestamp make merge non-commutative. | **OBLIGATION**, and narrower than usually stated | Determinism is fine. What breaks under duplicated replica ids is **attribution**: `movelog.rs` identifies one user with one replica id, so two users sharing an id are indistinguishable to every theorem here. That is the identity row again, and it is where the fix belongs — not in the sort. |
| Crash behaviour and recovery | Nothing exists to crash: the stores are in-memory, so a crash loses everything and no recovery path is claimed or implemented. | Not a premise — an **absent component** | Same disposition as the persistence row in Ledger 2. Recording "we assume crash-atomic storage" would manufacture a constituency; there is none yet. |
| Byzantine peers | `Causality.lean` gives the accountable-BFT primitive — fork evidence is a monotone fact of a grow-only set, so `fork_evidence_iconfluent` makes detection **permanent**: a peer caught equivocating cannot gossip its way back to innocence. Its dual is stated too (`no_unilateral_evidence`: one block frames nobody). But there is no BFT protocol; `Delta.lean`, `Liveness.lean` and `Necessity.lean` all exclude Byzantine replicas by name. | **OBLIGATION** | The target is already cited throughout: the blocklace (Almeida–Shapiro) and Kleppmann's BFT-CRDTs, whose architecture this repo's grounded hash-DAG already matches. The step is a delivery model in which a peer may lie, not merely be slow. |

### 3b. Cryptography — the row codex was most right about

Our claim was "signature unforgeability is terminal." Two things are wrong with
that, and the second is worse than the first.

**First**, unforgeability is terminal only as a *named hardness assumption* —
EUF-CMA for some concrete scheme, on some concrete curve, against some concrete
adversary class. Everything wrapped around it is engineering, and engineering is
provable. **EverCrypt is the existence proof**: a verified cryptographic
provider whose implementations carry machine-checked memory safety, functional
correctness against the spec, and secret independence. "The crypto is trusted"
has not been a whole answer since it shipped.

**Second, and this is the finding**: *signature unforgeability is not currently
a premise of this repository at all*, because no statement in the tree mentions
signatures. `Authority.lean` says authentication is "outside this model
entirely." `Gated.lean` says the kernel authenticates nothing.
`weave.rs` says a `UserId` is a `u64` anyone may write. There is no hypothesis
to discharge — which means the boundary was labelled terminal without ever
having been *stated*. That is strictly weaker than a premise, and it is the row
with the cheapest first step on this page.

| Item | Rests on | Verdict | Next step |
|---|---|---|---|
| Scheme hardness (EUF-CMA) | An assumption about a signature scheme this repo does not name. | **PREMISE**, once named | State it. An `AuthenticIssuer`-shaped hypothesis on grants gives the proofs something to carry and the deployment something to discharge. |
| The unforgeability handoff | Nothing. | **OBLIGATION**, and the pattern already exists one file over | Build the **forgery extractor**, by direct analogy with `uniqueGrant_violation_extracts_collision` and `uniqueAnchor_violation_extracts_collision`: a state violating the authenticity hypothesis should hand back a constructive forgery, so an adversary reaching it *is* a forger. That is exactly how this repo already refuses to assume hash injectivity, and it is why the hash row is in better shape than the signature row. |
| Protocol use and domain separation | Partially good, entirely unmodelled: `rust/src/causal.rs` domain-separates its content address (`blake3` over `"uwueave.causal.v1"` ‖ lengths ‖ parents ‖ contents), which is the right instinct — and no theorem knows about it. | **OBLIGATION** | Lift the deployed id scheme into the model, so `UniqueAnchor` / `UniqueGrant` are premises about *the encoding the crate actually computes* rather than about an abstract `id = hash(…)`. ⚠ While doing it, fix a live mismatch: `Sequence.lean` calls the premise "a premise about SHA-2" and the shipping crate uses **blake3**. |
| Key rotation and revocation | Grant revocation is modelled and proved fail-closed (`authority_view_antitone`: late revocations only ever shrink authority — the security dual of `view_not_stable`). **Key** rotation is not modelled at all; `Authority.lean` also lists timed/temporary revocation, un-revoke and re-grant as unmodelled. | **OBLIGATION** | Rotation is a lattice question in a repo that is good at lattice questions: what monotone evidence retires a key, and does the derived view stay antitone under it? The grant machinery is the right substrate and the theorem shape is already known. |
| Implementation correctness, constant time, parsing | Nothing — there is no signature implementation here, and `blake3` is trusted as a dependency. | **OBLIGATION** | This is the EverCrypt row: implementation correctness, memory safety and secret independence are *proved* properties in shipping code today. Parsing deserves its own mention — a signature verifier's parser is where real deployments break, and it is ordinary verifiable code. |
| Hash collision resistance | The best-decomposed row in the repo, and the model to copy. No `InjectiveHash` typeclass exists, deliberately: finite hashes are not injective, by pigeonhole. The boundary is stated as `UniqueAnchor` / `UniqueGrant` — "this state exhibits no collision" — and each has an extractor turning a violation into a constructive collision witness. `causal.rs` refuses a same-id-different-bytes encounter loudly (`MergeError::IdCollision`) rather than deduplicating silently. | **PREMISE** (collision resistance) with the handoff **proved** | The remaining transmutable part is the binding described two rows up: the extractor hands over a collision in the *model's* id scheme, and connecting that to blake3-as-deployed is unbuilt. |

### 3c. Bailis's generality

`Necessity.lean` proves both directions for **one execution substrate**:
join-semilattice replicas, atomic local `tryApply` seeing only local state,
convergence as `⊔`, safety as global `I`-validity — with satisfiable and
refutable witnesses on both sides so the model is not vacuous either way. It is
a real model, and it is one model.

| Item | Rests on | Verdict | Next step |
|---|---|---|---|
| The judgement, for this substrate | `necessity` + `iconfluent_implies_cfcs`, over `Confluence.lean`'s `IConfluent`, not a private redefinition. | Proved — this row is the asset, not the debt | — |
| Richer transaction histories | The model's ops are atomic local transformers; Bailis's interactive multi-round transactions with mid-transaction reads of remote state are named as out of scope. | **OBLIGATION** | Theorem work with a known target — the paper's own model is the specification. |
| Failures and process assignment | Not modelled: no crashes, no process-to-replica assignment, no partial failure inside a run. | **OBLIGATION** | Same. |
| Arbitrary outcome refinement | The model's outcome is a lattice state and its order is the merge's order. Bailis-style safety is `I`-validity of that state. | **OBLIGATION**, and the ambitious one | **Complete CALM** (Hellerstein, arXiv:2602.09435; PDF in `~/paperbin/uweave/`) is the broader semantic target: a specification maps execution histories to outcome sets under a *declared refinement order*, and admits a coordination-free implementation **iff** its outcomes are monotone. It explicitly recovers CALM, CRDTs, HATs and **I-confluence** as instances. So the transmutation is not "prove more about our lattice" — it is to restate the judgement over specifications and recover `IConfluent` as the instance it already is. That is the largest single item on this page and the one most worth doing. |

**Ledger 3 totals: seventeen rows across 3a/3b/3c — four PREMISE, eleven
OBLIGATION, one absent component**, plus one proved asset row in 3c that is
listed to mark where the debt starts.

---

## The corrected house rule

The old slogan was:

> *An honest label is a stopping condition and therefore a sin.*

It was **right about the danger and wrong about the remedy.** It taught us to
audit caveats for excuses, which worked — an earlier pass killed nine of them.
But it left only two verdicts, *theorem of the model* or *undone work in a
caveat's clothes*, and so it pushed every genuine boundary into the first bin
and then declared that bin closed. "Terminal" became a place to put things.
Three of them went in, and codex got all three back out.

The replacement:

> **Every boundary must be decomposed into its irreducible premise and its
> remaining transmutable obligations. A genuine model boundary is not a sin;
> leaving it undecomposed is.**

What this changes in practice:

- **"Terminal" is never a verdict about a whole boundary.** It is a verdict
  about a *residue*, and you only get to say it after naming what you removed.
  "Signature unforgeability is terminal" was three obligations and an unstated
  hypothesis wearing one word.
- **A row with no next step must say why there is none.** An empty next-step
  column is a claim, and claims are checked at source.
- **Cost is not a verdict.** "That would need a verified compiler" is an
  estimate. It is never a reason to leave the row undecomposed, and the
  existence proofs (CompCert, CakeML, EverCrypt, Lean4Lean) are all things
  someone already built while the estimate was being quoted.
- **Watch the qualifier drop in transit.** `Gated.lean` wrote
  "⟨TERMINAL, at this layer⟩"; the summary wrote "terminal". The summary is
  what got reviewed, and it was the summary that was wrong. When a boundary is
  restated somewhere more visible than its file, the qualifier is the part
  most likely to fall off — and the part that was load-bearing.

Everything above is a claim about this repository on 2026-08-11, checkable by
reading the files it cites. If a row is wrong, that is the good kind of wrong:
say so, and it moves a ledger.

*Written after codex's review, which is the reason this file has three ledgers
instead of one list.*
