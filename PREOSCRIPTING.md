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
conversion in either direction. What remains unbuilt is the surface protocol
AST and its explicit elaboration to those demands—not the scheduling judgement.

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

  future Delivered = deliver-only
  future Working   = deliver + agents may still act

  derive anyone_found : Bool = ∃ (a,c) ∈ findings, c = target
  derive open_files   : Nat  = |files \ range holds|

  session Wave under plan TeamEra
    budget { userPrompts ≤ 1 · peerBarriers ≤ 1 · arbiterCuts ≤ 1 }
    parallel { bounded N claim_file · at_most 1 reallocate }
```

Note what the session carries that our first sketch did not: a **plan**, a
**multi-currency budget**, and an actual **protocol shape**. An `allows` list
naming an operation vocabulary is not a workload — if `reallocate` may repeat
without bound, no finite worst-case bound follows from membership in a list.
The `field … per … : …` spelling is live; the future and session forms in this
example remain the next surface fragments and are intentionally not accepted by
the current parser.

### 7.1 Deep only where analysis requires it

Every deep constructor is a case in every theorem forever. So deep-embed only
what monotonicity/join-homomorphism analysis, footprint extraction, closure
generation, projection, repair synthesis, and cost composition genuinely need:
constants, field reads, products, positive selection, map/filter over finite
evidence, quantifiers with explicit closure rules, aggregation, explicit
resolution, explicit seal. Sessions get operation, sequence, parallel, finite
choice, bounded repetition, synchronization. Everything else takes the escape
hatch:

```
derive custom = opaque LeanFunction
  monotone by …   mergeable by …   status by …   footprint by …
```

An expert adds a computation without teaching every theorem to recurse through
arbitrary Lean syntax.

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
| typed repairs + promise deltas | `Repair` | in flight |
| mergeable-vs-replay verdict | `JoinHom.summaryFold_iff_joinHom` | proved |
| epistemic result carrier | `Evidence`, `Holes` | proved |
| future-indexed exactness | `Evidence`, `WorldFuture` | proved / in flight |
| coordination floor | `Cost.coordination_forced` | proved |
| cost profiles + composition | `CoordEffect` | in flight |
| budget trichotomy | `Budget` | in flight |
| merge models | `MergeModel` | in flight |
| seam synthesis | `SeamColoring` | in flight |
| summary synthesis | `MinimalSummary` | in flight |
| classification → `Verdict` term | `Tactics.classifyFinite` | proved |
| surface syntax + elaborator | `Preo/Syntax`, `Preo/Elab`, `Preo/Demo` | **built — fragment 2** |
| classification ACCUMULATES facets | `Preo/Classification` | **built**: `Classification` holds `global`/`seams`/`mergeability`/`obligations` as *lists*; rules add, never replace |
| route-order invariance | `Preo.run_answer_congr` | **proved**: two registries with the same rules in any order certify the same answer. Bottoms out in `Preo.verdict_agree` (two verdicts for one invariant cannot disagree — the pair is uninhabitable), not in bookkeeping. `run_answer_of_perm` is the permutation corollary. |
| ✅ seam verdicts in the surface | `Preo.budgetSeam`, `Preo.seamAlong`, `Segmented.budget_segmented` | **CLOSED** (was "inexpressible"). A globally clashing invariant now carries a `SegVerdict` facet *alongside* its clash — `Preo.seam_forces_clash` proves a seam is not a third alternative but forces the ESCALATES column. `Demo`'s `LoomDoc2.in_budget.seam` **is** `WeaveState.quotaVerdict`, by `rfl`. `seamAlong` lifts it to the whole declared document, using the emitted section (`<field>.plant`) that fragment 1 said the elaborator could not synthesize. |
| ✅ cross-field invariants in the surface | `Spec.Verdict.cross`, `Spec.pointsAtExisting_iconfluent` | **CLOSED** (was refused by name). A two-field invariant is classified against the *product* state; `LoomDoc2.fk` **is** `Spec.refIntVerdict` by `rfl`. ⚠ narrower than `WeaveState.bookmarksVerdict`, which is the per-user keyed form — this surface has no `per`. Three or more fields is still refused: `Verdict.cross` is binary. |
| ✅ `derive` + mergeability verdict | `JoinHom.Fourth`, `summaryFold_iff_joinHom`, `Preo.mergeability_comp` | **CLOSED**. `derive n : T = <expr>` emits the computation plus a `Fourth` facet with its `Fourth.Correct` proof. Registry: ∃-read, filtered view, high-water mark, set image (`fromResults`) and count (`needsEvidence`, via `no_count_merge_without_provenance`) — each *attempted by typechecking*, so an unknown shape is an obligation, never a guess. ⚠ the `needsEvidence` transport to document scale needs the projection **surjective**, not merely a hom; the elaborator emits `<field>.surj` for exactly that. |
| ✅ **seam composition in the surface** | `SegVerdict.selfSeam`, `liftFst`/`liftSnd`, `andSeams`, `absorbFree`, `prependFree` | **CLOSED at the general surface/combinator layer.** `TwinQuota.documentSeam` is the existing product seam by `rfl`; `NestedSurface` finds two seam rows through eight right-nested fields and absorbs six checked FREE rows; the general algebra reconstructs `WeaveState.weaveDocSeamVerdict` as the same value. The exact hand carrier is still not one surface declaration because flat fields cannot name grouped `WeaveCore`, and FREE verdicts cannot manufacture its legal planting witness `core₀`. |
| ✅ **`per` / keyed families in the surface** | `Confluence.keyed_cross_iconfluent`, pointwise `MergeState` | **CLOSED for field carriers and keyed referential integrity.** `field bookmarks per Bool : GrowSet Nat` emits `Bool → GSet Nat`; `KeyedDoc.fk.verdict` is `WeaveState.bookmarksVerdict` by `rfl`. Unsupported keyed relations remain obligations, and automatic keyed clash seams still require a concrete key/default witness. |
| **declaration composition** | — | **unbuilt** |
| ✅ **scheduling judgement** | `Scheduling.Session`, `Obligation`, `Schedule`, `ProfilePlan` | **built below the surface**: typed origins, metadata-rich demands, separate currencies, witnessed bounds, shared-strategy composition, and exact non-function refutations. **Unbuilt:** protocol/session syntax and a theorem-backed elaboration from bounded sequence/parallel/sync into demands. |

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
