# PREOSCRIPTING

*The design document for **preoscript** — a language for composing promises,
future-relative evidence, and proof-carrying repair plans. Committed, unlike
the correspondence in `CODEXHELP.md`; this is what we intend to build, revised
in place as we learn we were wrong.*

---

## 1. The thesis

> **preoscript rejects a budget using a semantic lower bound, accepts one only
> with a witnessed upper bound, and never lets a number or a singular UI value
> erase the strategy, fork, future, or premise that justified it.**

That sentence is not ours. It is the corrected thesis an external reviewer
handed back after refuting our first one, and we adopted it because it is
better. Our original — "a language whose types carry a coordination budget" —
was a scalar, and a scalar is not soundly compositional (§4.1).

## 2. The name is the first rule

`preo` = **preorder**. There are at least four live in this system, and
conflating any two of them produces false theorems (we produced one, and
retracted it):

| preorder | meaning | module |
|---|---|---|
| `⊑` | lattice order (`x ⊔ y = y`) | `Confluence.lean` |
| causal reachability | some history prefix reaches this state | `CausalReach.lean` |
| delivery-future | only already-issued events may arrive | `Evidence.lean` |
| extension-future | new application writes are permitted too | `Evidence.lean` |

**In preoscript you cannot write a stability claim without naming which future
you mean.** `Evidence.futures_not_interchangeable` is why: a query can be final
under delivery and open under extension. And the futures are *nested*, not
independent — delivery ⊆ extension — so stability under the larger implies
stability under the smaller, and the reverse coercion is invalid. That
subtyping direction should be a theorem the language derives, never a rule it
asserts.

The pun is deliberate and we are keeping it: a `preo` declaration
**pre**scribes what runs free and **pro**scribes what cannot afford itself.

## 3. What the language must say that the library cannot

The library classifies. A language must retain things that ordinary theorem
calls discard:

1. the **globally shared** repair choice (§4.1);
2. **unresolved future obligations**, per position;
3. **status-dependent downstream restrictions** (a fork you may not silently
   collapse);
4. **promise changes** introduced by a repair — arbitration buys agreement and
   spends monotonicity, and a solver that "meets the budget" by quietly solving
   a different application problem is the failure mode;
5. **composition before optimization**;
6. **proof-carrying synthesis results**.

If a design can be expressed as a tactic call plus a report, it does not need a
language. These six cannot.

## 4. The coordination effect

### 4.1 Not a number — a profile

Our first design graded a session by a count of "meetings". It fails under
composition:

```
min_σ (c₁ σ + c₂ σ)   ≠   (min_σ c₁ σ) + (min_σ c₂ σ)
```

The right-hand side lets each stream pick its *own* best seam; the left-hand
side correctly demands one globally coherent choice. Our own
`Cost.no_seam_frees_both` is the witness: two streams, each free under some
seam, with **no single seam freeing both**.

So a coordination grade is a **cost profile over the strategy space**,
`P : Σ → Nat`, composed **pointwise**, and minimized only when the session
closes. In practice the elaborator retains symbolic strategy variables, the
constraints over them, a cost expression conditional on each choice, and the
proof terms establishing each route's validity — and the solver chooses after
composition, never before. (`Uwueave/CoordEffect.lean`.)

### 4.2 A floor rejects; only a plan accepts

```
Floor(spec, W)  ≤  Cost(plan, W)  ≤  Budget
```

`Cost.coordination_forced` gives the left inequality — a bound forced by what
you *promised*, independent of implementation. It licenses **rejection** and
nothing else. `floor ≤ budget` does **not** license acceptance; accepting
requires exhibiting a plan and proving its upper bound.

Hence three outcomes, not two (`Uwueave/Budget.lean`):

```lean
inductive BudgetVerdict
  | accepted   (plan : Plan) (upper : plan.cost ≤ budget)
  | rejected   (floor : budget < unavoidableFloor)
  | unresolved (obligation : SynthesisObligation)
```

`unresolved` carries what would have to be exhibited. It is not the
honest-label sin, because it names its own remaining work.

### 4.3 Crossings are not meetings

`Cost.lean` counts **seam crossings**. It models no attendance, no coalescing,
no barriers, no elapsed time. So a session budget must say which currency it
means, and the language should not offer a single word that hides five:

```
peer barriers · arbiter cuts · network rounds · user prompts · rollbacks
```

Calling all five "meetings" manufactures attractive false zeroes. A meeting is
a *scheduling interpretation* over demands with scope, participants, epoch,
evidence and rounds. `Uwueave/Scheduling.lean` now builds that interpretation:
proof-carrying obligations compose pointwise under one shared strategy, a
schedule witnesses coverage, and five currencies remain separate. Its exact
2-crossings→1-meeting, 0→1, and 1→2 examples prove there is no scalar
conversion in either direction. The standalone `preo_budget` command now
accepts an existing five-currency `ProfileUpperBound` for an exact generated
session. What remains unbuilt is *unbounded* schedule discovery and the prettier
inline budget block—not witnessed budget acceptance, the bounded authored search
in `Preo.Planning`, the protocol AST, its proof-carrying elaboration, or the
scheduling judgement. `Protocol.Term` carries the bounded
operation/sequence/parallel/choice/repeat/sync language. An inline `preo`
protocol accepts a typed term in that AST; the standalone `preo_protocol`
command gives all six constructors a parser-safe native spelling and expands to
that same semantic API.

### 4.4 Prices are records, not numbers

Arbitration does not cost "0". It costs a trusted announcement and rollback
exposure. Exposing a fork costs the singular-output contract. Escrow costs
rights allocation and metadata. Retaining evidence costs storage and replay.
So a price is a record with fields, each justified by a theorem in the tree or
omitted (`Uwueave/Repair.lean`), and a deployment supplies its own valuation
`Price → Cost` — because a team that considers rollback catastrophic and
metadata cheap should not be forced to share a scalar with one that does the
opposite.

## 5. Results carry their epistemic status

### 5.1 Static capability vs runtime status

`derive verdict : Forked Claim` is ambiguous: does it mean *every* evaluation
forks, or that this computation *may* fork? It means the second, so the
declaration should state **capability** (`mayOpen`, `mayFork`) and evaluation
should return a **status view**. Two axes, not one.

### 5.2 The status space is bigger than four

Candidates × closure gives at least six cells, because zero candidates is a
real state and its two closures mean different things:

| candidates | open | closed |
|---|---|---|
| zero | nothing observed yet | **definitive absence** |
| one | provisional singleton | exact singleton |
| many | open fork | closed fork |

`Evidence.lean` ships five constructors (`vacuous` is the zero case, named
rather than folded away). Visibility — produced-but-uninspectable, from
authorization, encryption, laziness, or an opaque remote — is an **independent
axis**, not a sixth constructor, so the underlying evidence stays factored and
the four common views are *derived*.

### 5.3 Exactness is indexed by a future, and often by a value

`Exact Delivered α` and `Exact Working α` are different claims, and
`Exact Working α <: Exact Delivered α` because surviving the larger future set
implies surviving the smaller. That coercion must come from a theorem about
future inclusion, never an ad-hoc subtyping rule.

And exactness is frequently *value*-dependent. For an existential over a
grow-only set, `true` is self-certifying — no future retracts it — while
`false` stays open until closure. So the honest result is not "this Boolean
becomes exact after a seal"; it is one epistemic carrier whose status depends
on the value it currently holds.

### 5.4 Futures range over worlds, not states

Two replicas can share a materialized state and differ in issued-but-undelivered
events, frontier, seals, roster, capabilities, and known merge bases. So
`DeliveryFuture` cannot be defined from the state alone, and an exactness
certificate that escapes its frontier or epoch context is unsound under reuse.
(`Uwueave/WorldFuture.lean`.)

### 5.5 Resolution must compile — auditably

"You cannot silently collapse a fork" is right; "you cannot ever pick one" is
wrong. The enforceable property is:

> **No branch selection occurs through an implicit coercion.**

So resolution is explicit and *retained in the type*: `resolve verdict by
era_order` yields `ResolvedBy EraOrder Claim`, carrying the policy and — where
disclosure rules allow — the suppressed alternatives.

## 6. Field kinds: capabilities, not a record

`MergeState` cannot be mandatory. A join CRDT, an op-replay structure, and an
MRDT with a merge base have genuinely different merge signatures — and
`Ancestral.join_is_ancestral_merge_iff_trivial` proves a join *is* a three-way
merge only on a one-point carrier. One mandatory binary interface would either
lie about three-way merge or discard the base uncertainty that makes it
valuable. So merge is a **model** with a context type
(`Uwueave/MergeModel.lean`), and a field kind supplies *layered* capabilities:

| capability | supplies |
|---|---|
| `MergeModel` | carrier, merge context, outcomes, laws |
| `OperationalModel` | operations, local admission, issued evidence |
| `ReachabilityModel` | worlds, reachable executions, live witnesses |
| `FutureModel` | named futures and their inclusions |
| `ClosureModel` | frontiers, seals, finalization certificates |
| `ObservationModel` | result domain and its approximation order |
| `FootprintModel` | read/write scope and independence |
| `FiniteEvidence` | finite support and materialization |
| `ExecutableModel` | codec, kernel, refinement theorem |
| `DisclosureModel` | what provenance may be shown, to whom |

A new paper should add one capability and some rules — never extend a universal
`FieldKind` record.

**Verdict routes do not live inside field kinds.** A rule like *"monotone
summary + upward-closed invariant ⟹ confluent pullback"* is not part of G-Set
identity; it applies to anything satisfying its premises. Routes belong in an
extensible `RuleSet` where every route returns a proof-carrying verdict, so
search order may change performance or which explanation you get, but never
soundness.

⚠ That last sentence is no longer a design intention — it is
**`Preo.run_answer_congr`**, and the surface is built on it
(`Uwueave/Preo/Classification.lean`). Read what it does and does not say: the
*answer* is invariant under any membership-preserving change of registry; the
*explanation* is a list, and which one a report prints first is a separate
policy. The proof is not bookkeeping — it reduces to `Preo.verdict_agree`, that
a `free` and a `clash` for one invariant are contradictory **terms**, so the
disagreement a first-match order was protecting against cannot be constructed.

**Exits are morphisms between specifications** — source merge model and promise
to target merge model and promise — not values in a per-field list.

**Composition needs formulas, not badges.** If a component exports only
`FREE`/`ESCALATES`/`SEAM`, the information needed to compose relationally is
already gone: composition needs the invariant, its footprint, its reachability
assumptions, the selected future, the strategy variables, and the promise
deltas.

## 7. The surface

Promises and prices, not fields and annotations — because a surface of
decorated struct fields can only classify what we already know how to classify.

```
preo Swarm where
  field findings : GrowSet (Agent, Claim)
  field holds per Agent : Slot File
  field spent per Agent : Escrow Tokens
  field roster : EraGroup

  invariant one_writer : ∀ f, |{a | holds a = f}| ≤ 1
  invariant in_budget  : ∀ a, spent a ≤ alloc a

  future Delivered on (Future.evidenceWorldModel Holes.Val) :=
    Future.Delivery Holes.Val
  future Working on (Future.evidenceWorldModel Holes.Val) :=
    Future.Extension Holes.Val

  typed derive next_score over {
    schema := [.nat, .nat],
    reach := [before, afterRemote, afterLocal]
  } := .natSucc (.field 0)

  derive anyone_found : Bool = ∃ (a,c) ∈ findings, c = target
  derive open_files   : Nat  = |files \ range holds|

  protocol WaveProtocol over TeamStrategy := waveProtocol
  session Wave under TeamEra runs WaveProtocol at chosenStrategy := chosen_is_admissible
```

The typed-term form above is the expert escape hatch. The native spelling is a
separate command with a punctuation-delimited recursive body:

```
preo_protocol WaveNative over TeamStrategy at chosenStrategy :=
  .seq [
    .operation { id := 1, crossings := 0, needs := [] },
    .repeat {
      count := 2,
      body := .sync {
        currency := .userPrompt,
        participants := [0],
        scope := 0,
        epoch := 0,
        evidence := .none,
        round := 0,
        barrier := 0 } } ]
```

It emits predictable `Term`, `Elaboration`, `Session`, `Plan`, `Limits`, and
`ProfileUpperBound` constants. Choice is nonempty and selected by an explicit
natural in this first deterministic fragment; crossing origins are bounded by
the operation's written crossing count.

Note what the session result carries that our first sketch did not: a checked
**schedule/plan**, a **multi-currency cost profile**, and an actual **protocol
shape**. The standalone `preo_budget` surface now accepts a limit only by
consuming a `Scheduling.ProfileUpperBound` — one real plan satisfying all five
currency coordinates for the exact named session. It performs no schedule
search. An `allows` list
naming an operation vocabulary is not a workload — if `reallocate` may repeat
without bound, no finite worst-case bound follows from membership in a list.
The field, invariant, future, typed-derive, ordinary-derive, protocol and
session forms shown here are live. `typed derive` is parser-hard at the braces
and `:=`: `Raw.infer` must produce an intrinsically typed `Expr.Term`, after
which the command exposes exact positional `Holes`, erased `Reads`,
proof-carrying `MergeSafe?`/`MonotoneSafe?`, and a checked cache/update chain
(`updateCache` promotes each proved result without reevaluation).
Its written finite `reach` also feeds a real `ResultProgram.CheckedDeclaration`:
the generated default is an exact singleton result under the equality future,
with preserve-fork resolution and explicit inspectable/shown policy, plus a
checked six-status report at the reference carrier. `reportAt` requires proof
that its environment belongs to the written reach and retains that proof in a
`ReachReport`, tying every generated report to the effect-inference domain; an
empty reach therefore cannot report.
Malformed operators,
out-of-range fields and raw `.custom` fail the entire row before any typed term
or analysis is emitted. A future must name its full
`Preo.Future.WorldModel`, so no declaration can be inferred from materialized
state alone. An inline protocol body remains a typed Lean term of
`Protocol.Term TeamStrategy`, the deliberate opaque escape hatch. The native
`preo_protocol` parser does not duplicate protocol semantics: it expands its
six data-shaped forms into that same `Protocol.Term`, calls
`Protocol.elaborate` once, and exposes the checked schedule and exact
five-currency bound. Inline sessions call
`Protocol.elaborate`/`elaborateProfilePlan` once and expose their checked
schedule and upper bound. Certificates and budgets remain parser-safe
standalone commands whose dependent types are ordinary Lean terms:

```
preo_certificate Quiesced :
  Future.CheckedCertificate Swarm.Delivered answer key accepts exactWorld := proof

preo_budget WaveLimit for Swarm.Wave : fiveCurrencyLimits := checkedProfileBound

preo_export SwarmManifest from Swarm : hostValidationConfig :=
  declaration := { id := 100, stateType := 101, schema := 1 }
  | field findings := { id := 102, kind := 10, carrier := 103, key := none }
  | invariant one_writer := {
    id := 104, carrier := 103, codec := findingsCodec, answered := rfl }
  | future Delivered := {
    certificate := Quiesced, id := 105, world := 106, relation := 107 }
  | budget WaveLimit for Wave := {
    id := 110, session := 108, plan := 109,
    samePlan := checkedProfileBound_is_wave_plan }
```

`preo_certificate` requires its written type to reduce to
`Future.CheckedCertificate`; it never infers an index from materialized state.
`preo_budget` pins `checkedProfileBound` to `Swarm.Wave.session`. The earlier
pretty in-declaration budget block and schedule synthesis remain unbuilt.

`preo_export` is a checked manifest rather than a report serializer. It starts
one `Export.DeclarationBundle` at the generated state and folds each row
directly through the corresponding proof-indexed builder. Field rows name the
generated carrier; invariant rows require an existing answered classification
equality and an explicit `FirstOrderCodec`; future rows require the exact named
certificate; session rows accept only a `Protocol.Elaboration`. Numeric IDs are
written data—not hashes of Lean names. The command emits the checked bundle,
artifact, canonical encoding, durable format/bytes, raw V2 projection, explicit
validation result, private validated value and deterministic rendered source.
Its kernel-computed validation gate rejects duplicate stable IDs and malformed
references at compile time. An unresolved invariant has no `answered` proof, a
certificate for another future/world does not typecheck, and a composed
`ProfilePlan` is refused until `DeclarationBundle` grows a semantic builder for
that shape. A budget row is also the session/plan row: it calls
`addElaborationWithBudget` and requires an explicit proof that the named
`preo_budget` carries exactly the elaboration's plan. A valid bound for a
different plan of the same session is refused rather than silently relabelled.
The encoding retains its five written limits and five realized coordinates.
Decoding remains one-way first-order data and never reconstructs a verdict,
certificate or scheduling plan.

### 7.1 Deep only where analysis requires it

Every deep constructor is a case in every theorem forever. The live typed core
therefore stays deliberately first-order: booleans, naturals, products,
options, typed field reads, boolean operations and natural operations. It is
already enough for sound structural dependency extraction, positive merge/monotonicity
certification, checked incremental reuse and a six-status result adapter.
Sessions independently get operation, sequence, parallel, finite choice,
bounded repetition and synchronization. Everything else keeps the ordinary
Lean `derive` escape hatch:

```
derive custom = opaque LeanFunction
  monotone by …   mergeable by …   status by …   footprint by …
```

An expert adds a computation without teaching every theorem to recurse through
arbitrary Lean syntax. That escape hatch receives only the theorem-backed
mergeability routes it actually matches; it does not acquire typed-program
reads or cache laws by inspection.

One boundary is explicit: a typed row's authored `Expr.Schema` and `Expr.Env`
are not silently identified with the surrounding declaration's generated
`State`. An application that wants document evaluation writes a
`State → Expr.Env Schema` projection and calls the emitted `.Eval`. The
elaborator currently makes no field-name/type coercion claim.

### 7.2 Robust proof and work boundaries

Production code that only needs the proposition-closing `classify` tactic,
finite enumerations, probe search, or the small proof idioms may import
`Uwueave.Tactics.Core`. Code that needs `Spec.Verdict` values,
`classifyIn?`/`classify?`/`classifyFinite`, or the `verdict` tactic should
import `Uwueave.Tactics.Verdict`; it already imports `Core`. The larger
`Uwueave.Tactics` module is the demonstration suite and deliberately imports
additional domains.

Automatic tactic work is bounded. The exhaustive route used implicitly by
`classify` and `verdict` accepts at most 64 enumerated states and 4096 ordered
pairs. An over-cap or nontransparent `FinEnum` spine is a loud typed resource
refusal, not a route miss; unexpected internal failures are likewise not
silently converted to inapplicability. The explicit value function
`classifyFinite` remains logically total and has no implicit work cap. “Total”
describes its result type, not its compile-time cost.

There is one narrower current Preo caveat: an invariant over a carrier with
both `FinEnum` and `DecidablePred` makes the elaborator emit the explicit,
uncapped `classifyFinite` result as an accumulated facet. A supplied verdict
does not suppress that route, because applicable facets are accumulated rather
than chosen first-match. Until the elaborator shares the tactic work gate, keep
automatically enumerable Preo carriers small or avoid installing `FinEnum` for
a large carrier.

Two recursive generators also have semantic simp interfaces on purpose:

- For `Preo.Planning.actionChoices`, use
  `mem_actionChoices_iff_sublist` and `actionChoices_length`. Do not normalize
  `actionChoices_cons` across a large action list: it materializes `2^n`
  candidates. Runtime-facing construction should use `checkActionUniverse`,
  which rejects duplicates and a caller-supplied `maxChoices` bound before
  materialization. That bound is authored policy, not a global system ceiling.
- For bounded protocols, use `repeatSession_crossings` and
  `repeatSession_demands` to simplify observations. The structural
  `repeatSession_zero`/`repeatSession_succ` and
  `repeatDemands_zero`/`repeatDemands_succ` equations are explicit `rw` tools,
  not global simp rules. Avoid
  `simp [repeatSession]` at large literal bounds. These observation laws avoid
  proof-normalization blowups; exact denotation still retains the real linear
  repeated demand stream.

## 8. Why it is a UI substrate

The epistemic status of a value determines its widget: `Exact` renders a value;
`Open` renders the value **and** what is pending; `Forked` renders candidates
with provenance; `OpenForked` does both.

Three enforceable properties, and one honest limit:

- **No exact badge without a stability certificate.**
- **No singular extraction from a possible fork without a named policy.**
- **No "fully synchronized" status without naming the scope it is relative to.**
- ⚠ Types enforce *semantic presence*, not **salience**. A correctly typed
  `OpenForked` can still be rendered as one-pixel grey text below the fold. So
  keep constructors abstract, expose total eliminators, require every status to
  be handled, and make exact badges consume certificates.

**Obligations are affordances only when someone can discharge them.** "Waiting
on Bob" is not actionable if the current user cannot request it, Bob has
retired, or the producer set is itself unknown. An actionable obligation needs
an actor, an authorization proof, a precondition, and an effect.

**Provenance may need redaction.** The contract is not "always show every
branch"; it is *no silent selection, and every shown or hidden branch has an
explicit disclosure decision.* A redacted fork is still a fork.

The load-bearing claim we have **not** proved, stated as a hypothesis rather
than a fact: *a recurring class of local-first UI misrepresentations consists
of unproved coercions from open, forked, or scope-relative evidence to an exact
singular presentation.* Checking it needs a defect corpus and a coding
protocol. We are not going to claim "most bugs" without one.

## 9. Synthesis

Two targets, both handed to us by review, both now in the tree:

**Seams are graph colorings.** Build the clash graph — vertices are reachable
legal states, edges join pairs whose merge is illegal — and a valid seam is
exactly a coloring with no monochromatic clash edge. Seam-finding becomes
search, and because a coloring is one **global** object, minimizing over
colorings after composing constraints is sound where per-stream minima are not.
(`Uwueave/SeamColoring.lean`.)

**The coarsest summary is a quotient.** For a query `f`, contextual equivalence
`x ≈_f y ⟺ f x = f y ∧ ∀ z, f (x ⊔ z) = f (y ⊔ z)` is stable under adding
context, and its quotient is the candidate coarsest future-sufficient evidence
domain. Membership collapses to one bit; exact count collapses to nothing; a
threshold query should land in between. (`Uwueave/MinimalSummary.lean`.)

## 10. Status

| feature | backing | status |
|---|---|---|
| FREE / ESCALATES / SEAM verdicts | `Confluence`, `Catalog`, `Ceiling`, `Segmented` | proved |
| clash repro | `escalation_witness` | proved |
| priced exit menu | `Exits` | proved |
| typed repairs + promise deltas | `Repair`, `RepairMenu` | **proved**: generated repairs retain exact promise relations and an eight-axis price, including reachability restriction rather than falsely pricing escrow as free |
| mergeable-vs-replay verdict | `JoinHom.summaryFold_iff_joinHom` | proved |
| epistemic result carrier | `Evidence`, `Holes` | proved |
| future-indexed exactness | `Evidence`, `WorldFuture`, `Preo/Future` | **proved and surfaced**: declarations retain the world model/index; checked stability and certificates project proofs, and only extension→delivery restriction exists |
| coordination floor | `Cost.coordination_forced` | proved |
| cost profiles + composition | `CoordEffect`, `Scheduling` | **proved**: pointwise composition precedes one global strategy choice; schedules retain five currencies |
| budget trichotomy | `Budget`, `Preo.Planning` | **proved**; explicit duplicate-free, pre-capped authored action universes additionally compute an exact witnessed minimum without claiming to enumerate arbitrary schedules or seams |
| merge models | `MergeModel` | **proved** for join, ancestral and op-replay models, now universe-polymorphic at the generic model layer |
| seam synthesis | `SeamColoring`, `MenuTotality` | **proved for explicit finite carriers/palettes**, including exhaustive refusal and a least-width certificate; infinite search remains outside the result |
| summary synthesis | `MinimalSummary`, `TextSummary` | **proved semantically** through contextual quotients; the fixed text window now has an exact iff, while executable quotient construction for arbitrary evaluators remains open |
| arbitrary refined outcomes | `Specification` | **proved semantically**: under totality, coordination-freedom is exactly history monotonicity plus fiber directedness, and `IConfluent` is the singleton-outcome instance |
| classification → `Verdict` term | `Tactics.classifyFinite` (`Uwueave.Tactics.Verdict`) | **proved**; the explicit total function is uncapped, while automatic tactic routing has a 64-state/4096-pair work gate |
| surface syntax + elaborator | `Preo/Syntax`, `Preo/Elab`, `Preo/Demo`, `Preo/ProtocolSurface` | **built**: built-in and explicit-seed application carriers, invariants/ordinary derives, intrinsically typed derives with exact dependencies + checked incremental/result/report artifacts, keyed fields, named world futures/certificates, typed-term and native protocols, proof-carrying sessions, five-currency budgets and explicit checked export manifests |
| classification ACCUMULATES facets | `Preo/Classification` | **built**: `Classification` holds `global`/`seams`/`mergeability`/`obligations` as *lists*; rules add, never replace |
| route-order invariance | `Preo.run_answer_congr` | **proved**: two registries with the same rules in any order certify the same answer. Bottoms out in `Preo.verdict_agree` (two verdicts for one invariant cannot disagree — the pair is uninhabitable), not in bookkeeping. `run_answer_of_perm` is the permutation corollary. |
| ✅ seam verdicts in the surface | `Preo.budgetSeam`, `Preo.seamAlong`, `Segmented.budget_segmented` | **CLOSED** (was "inexpressible"). A globally clashing invariant now carries a `SegVerdict` facet *alongside* its clash — `Preo.seam_forces_clash` proves a seam is not a third alternative but forces the ESCALATES column. `Demo`'s `LoomDoc2.in_budget.seam` **is** `WeaveState.quotaVerdict`, by `rfl`. `seamAlong` lifts it to the whole declared document, using the emitted section (`<field>.plant`) that fragment 1 said the elaborator could not synthesize. |
| ✅ cross-field invariants in the surface | `Spec.Verdict.cross`, `Spec.pointsAtExisting_iconfluent` | **CLOSED** (was refused by name). A two-field invariant is classified against the *product* state; `LoomDoc2.fk` **is** `Spec.refIntVerdict` by `rfl`. The keyed form is also live: `KeyedDoc.fk.verdict` is `WeaveState.bookmarksVerdict` by `rfl`. Three or more fields is still refused: `Verdict.cross` is binary. |
| ✅ `derive` + mergeability verdict | `JoinHom.Fourth`, `summaryFold_iff_joinHom`, `Preo.mergeability_comp` | **CLOSED**. `derive n : T = <expr>` emits the computation plus a `Fourth` facet with its `Fourth.Correct` proof. Registry: ∃-read, filtered view, high-water mark, set image (`fromResults`) and count (`needsEvidence`, via `no_count_merge_without_provenance`) — each *attempted by typechecking*, so an unknown shape is an obligation, never a guess. ⚠ the `needsEvidence` transport to document scale needs the projection **surjective**, not merely a hom; the elaborator emits `<field>.surj` for exactly that. |
| ✅ typed program + local runtime/result adapter | `Preo.Expr`, `Preo.Incremental`, `Preo.ResultProgram`, `typed derive` | **BUILT for the first-order local evaluator.** `Raw.infer` is retained by an exact success witness; positional holes/reads, positive merge and monotone proof options, checked chained cache/update correctness and off-dependency zero work are emitted from that one term. An authored finite reach produces a least six-status effect and proof-carrying reach-indexed checked reports under the explicit equality future/preserve-fork/default disclosure policy. `Demo` compares the whole program to a hand value by `rfl`, checks a two-update cache chain plus report site/status/policy, and fail-closes malformed and opaque rows. Arbitrary Lean stays in ordinary `derive`; document-State projection and non-equality futures require explicit application proofs. **Still unbuilt:** typed-program rows in `preo_export`, and wiring `ContextCompiler` summaries into this command. |
| ✅ **seam composition in the surface** | `SegVerdict.selfSeam`, `liftFst`/`liftSnd`, `andSeams`, `absorbFree`, `prependFree` | **CLOSED at the general surface/combinator layer.** `TwinQuota.documentSeam` is the existing product seam by `rfl`; `NestedSurface` finds two seam rows through eight right-nested fields and absorbs six checked FREE rows; the general algebra reconstructs `WeaveState.weaveDocSeamVerdict` as the same value. `GroupedCarrierSurface.State` now **is** `WeaveDoc` by `rfl`, with the explicit `core₀` seed. The remaining exact full-surface obstruction is narrower: built-in `Quota` plants structural zero, which is not `BudgetInv 10`; the surface cannot silently substitute the invariant-specific `quota₀`. |
| ✅ **`per` / keyed families in the surface** | `Confluence.keyed_cross_iconfluent`, pointwise `MergeState` | **CLOSED for field carriers and keyed referential integrity.** `field bookmarks per Bool : GrowSet Nat` emits `Bool → GSet Nat`; `KeyedDoc.fk.verdict` is `WeaveState.bookmarksVerdict` by `rfl`. Unsupported keyed relations remain obligations, and automatic keyed clash seams still require a concrete key/default witness. |
| ✅ **named world futures in the surface** | `Preo.Future.FutureDecl`, `WorldIndex`, `CheckedStability`, `CheckedCertificate` | **CLOSED.** `future N on M := D` checks `D : FutureDecl M`; `preo_certificate N : CheckedCertificate ... := proof` retains the complete world index and is whole-value `rfl` to the hand certificate. Same-state/different-world refusal and one-way delivery⊆extension variance remain theorem-visible in `Demo`. |
| ✅ **protocol/session surface** | `Protocol.Term`, `Protocol.Elaboration`, `Preo.ProtocolSurface`, `elaborateProfilePlan`, `elaborateComposedProfilePlan` | **CLOSED with both a typed opaque body and native `preo_protocol`.** The native command covers operation/sequence/parallel/nonempty choice/bounded repeat/sync and emits the exact elaboration, session, plan and five-currency bound. Inline sessions expose checked plans/upper bounds and composed profiles select one global strategy. Reports name semantic artifacts and deliberately contain no invented verdict bit or meeting scalar. |
| ✅ **five-currency budget surface** | `Scheduling.ProfileUpperBound`, `preo_budget`, `Preo.Planning` | **CLOSED for witnessed acceptance and bounded authored search.** A standalone command consumes one real plan satisfying `Currency → Nat` pointwise at the exact generated session. `Demo` rediscovers `coalescedProfileUpperBound` by `rfl`; separate theorems refute acceptance from crossings or a peer-meeting floor. `Preo.Planning` searches only a duplicate-free, pre-capped authored action universe. **Unbuilt:** arbitrary schedule discovery and a pretty inline budget block. |
| ✅ **first-order checked export** | `Preo.Artifact`, `Preo.Export`, `Preo.ArtifactDurable`, `Preo.ProjectionV2`, `preo_export` | **BUILT AND SURFACED.** Private proof-indexed builders project answered classifications, certified world futures, ordinary/profile protocol elaborations and exact-plan five-currency budgets into one canonical first-order artifact. The manifest supplies every stable ID, witness codec and budget plan equality explicitly; it emits canonical durable bytes and must pass V2 structural/resource validation before rendering. Unresolved invariants, wrong certificates, wrong-plan budgets and duplicate IDs fail closed. Published V1 remains the budget-empty legacy schema. Composed profile plans wait for a dedicated checked export builder; decoded wire tags have no path back to semantic proof constructors. |
| **declaration composition** | `Preo.Export.DeclarationBundle` is one checked declaration bundle, not composition | **unbuilt across declarations**: composing two independently authored declarations still needs formulas, footprints, futures, strategies and promise deltas rather than concatenating artifacts |
| ✅ **scheduling judgement** | `Scheduling.Session`, `Obligation`, `Schedule`, `ProfilePlan`, `ProfileUpperBound`, `Protocol.Term`, `Preo.Planning` | **built and surfaced**: typed origins, metadata-rich demands, separate currencies, witnessed pointwise limits, bounded protocol semantics, shared-strategy composition, bounded authored action-subset search, and exact crossing/meeting non-function refutations. **Unbuilt:** arbitrary schedule discovery and the pretty inline budget block. |
| recursive protocols | `ChoreoRec` | **built as guarded finite approximants** with recursion-free conservativity and a concrete barrier deadlock; temporal liveness/fair delivery remain explicit hypotheses, not syntax-derived claims |
| durable artifacts | `Durable` | **proved logical codec/journal rung** with canonical roundtrip and torn-tail recovery; no filesystem, flush or crash-atomicity guarantee is claimed |

## 11. What would make us abandon this

Recorded now, while it is cheap to say:

- If the deep-embedded core cannot stay under roughly a dozen constructors
  without losing the analyses in §7.1, the language is the wrong shape and the
  right answer is a tactic library plus a code generator.
- If declaration composition turns out to be expressible by composing verdicts
  after all, §3's justification collapses and we should say so.
- If the graded effect cannot be made sound outside the segmented fragment, the
  budget feature should ship as an *analysis* that reports, not a *type* that
  refuses.

*Revised in place. Every claim here that a reviewer refutes gets its retraction
written where the claim was made, not appended at the end.*
