/-
# Uwueave.CoordEffect — the coordination grade is a **profile**, not a number.

`Cost.lean` answers *how often must I coordinate?* with a `Nat`. `CODEXHELP.md`
§2.1 proposed putting that `Nat` in a type — `session Wave @ ≤ 1 meeting` — and
refusing programs that exceed their budget. **codex's second review (the
`CODEXHELP.md` §0.1 errata, 2026-08-11) refuted the scalar form**, and we accept
the refutation:

  > a scalar meeting count is not soundly compositional, because
  > `min_σ (c₁ σ + c₂ σ) ≠ (min_σ c₁ σ) + (min_σ c₂ σ)` — independently choosing
  > each stream's best seam undercounts the globally coherent choice.

This file is the repair, in the library's own vocabulary. A coordination grade
is not a number; it is a **cost profile over the strategy space**

    Profile X := X → Nat

composed **pointwise** (`P ⊗ Q`), with minimization **deferred** until the
session closes (`optimum`). The strategies are seams — bundled *with* their
`SegmentedIConfluent` proof, so an inadmissible seam cannot enter the space —
and a profile's value at `τ` is `Cost.crossings` under that seam.

## What landed

  * **§1** `Profile`, pointwise composition `⊗` with its monoid laws, `Profile.zero`.
  * **§2** the finite strategy space (`Admissible`: a head and a list, so it is
    finite **and** nonempty by construction) and `optimum`. Three facts make it
    usable and one makes it *sound*: `optimum_le_of_mem`, `le_optimum`,
    `optimum_antitone_of_subset`, and **`optimum_achieved`** — the minimum is
    attained *at a member*, so it is a number some single strategy actually pays.
  * **§3** the headline **`opt_compose_ge_sum_opt`**, its exact equality
    condition (`opt_compose_eq_sum_opt_of_common_optimum` — the scalar grade is
    sound *iff you have a common minimizer*, and that is the hypothesis it was
    silently assuming), and the n-ary session form `opt_session_ge_sum_opt`.
  * **§4** strategies as *valid seams*, `streamProfile`, and the bridge to
    `Cost.coordination_forced`: the spec-forced floor lower-bounds the profile's
    minimum (`forced_le_optimum`), and — the part the scalar grade could not say
    — **forced floors ARE additive across composed streams**
    (`forced_le_optimum_compose`). Profiles refine `Cost.lean`; they do not
    replace it.
  * **§5** ⚠ **the strict witness.** `Cost.no_seam_frees_both` is exactly the
    shape codex's falsifiability bar asks for: two streams, each **free** under
    some valid seam, and no single valid seam freeing both. As profiles:

        optimum pinSpace pinTrueProfile = 0
        optimum pinSpace pinFalseProfile = 0
        optimum pinSpace (pinTrueProfile ⊗ pinFalseProfile) = 1

    — floor and achievement meet at `1` (`pin_session_costs_exactly_one`), so
    the gap is not slack in a bound: the scalar grade reports `0` for a session
    that costs `1`. `opt_compose_ge_sum_opt` is therefore **strict** here
    (`pin_opt_compose_strict`),
    and the per-stream sum of minima is a budget **no strategy can pay**
    (`pin_indep_min_unpayable`, `0 < (P₁ ⊗ P₂) τ` for *every* `τ`). Without this
    witness the headline inequality is a triviality; with it, a scalar grade
    would have accepted `@ ≤ 0` for a workload whose every coherent schedule
    costs ≥ 1.

    The witness does not depend on our choice of strategy space:
    `pin_composed_floor_universal` proves the `≥ 1` for **every** admissible
    space over **every** segment type in **every** universe, so enlarging the
    catalogue of seams cannot rescue the scalar grade.

## Soundness of the discipline, and its exact hypotheses

**`optimum_compose_achieved`**: `∃ τ ∈ A.toList, optimum A (P ⊗ Q) = P τ + Q τ`.
Compose-then-minimize returns a cost that **one coherent global strategy
achieves**, and by `Strategy.valid` that strategy is a seam the invariant
actually admits. The hypotheses, named rather than assumed:

  1. **Nonempty**, by construction — `Admissible` carries a `head`. Over an
     empty space there is no strategy and no minimum, and the statement would be
     false rather than vacuous.
  2. **Finite**, by construction — the space is a `List`. Nothing here minimizes
     over all seams of all types; `Cost.coordination_forced` is what quantifies
     that widely, and §4 connects the two.
  3. **⟨scope⟩ the list is a *chosen enumeration*, not an exhaustion.** No
     theorem here says a given `Admissible` contains every seam a schema could
     use, so `optimum A P` is an **upper bound** on the true infimum over all
     seams. `optimum_antitone_of_subset` is that scope as a theorem: enlarging
     the space can only lower the optimum, never raise it.

The unsound alternative is refuted rather than merely avoided: `optimum A P +
optimum A Q` is *not* achievable in general (`pin_indep_min_unpayable`), and it
is exactly the number the scalar grade computes.

## ⚠ Honest scope — inherited from `Cost.lean` and repeated, not assumed read

  * ⟨scope⟩ **Crossings are not meetings.** Repeating `Cost.lean`'s own
    disclaimer because a profile *looks* more like a budget than a crossing
    count and the qualifier is exactly what falls off in transit: a
    "coordination event" here is a **seam crossing on one replica's stream**.
    How many peers must attend, whether two replicas crossing "the same"
    boundary hold one meeting or two, and whether several future seam values can
    be agreed in one round are not determined here. `Scheduling.lean` adds the
    explicit participant/scope/epoch/evidence/round/barrier coeffects and
    refutes any scalar conversion in either direction. Every `Nat` in this file
    remains a crossing count under the stated stream model, and a `@ ≤ n` grade
    built on it budgets crossings, not meetings.
  * ⟨scope⟩ `[DecidableEq Seg]` on every seam, inherited from `crossings`.
  * ⟨scope⟩ Per-stream, per-seam counting is `Cost.lean`'s; composition here is
    **pointwise addition of two streams' counts under a shared strategy**. That
    is the aggregate `Cost.lean` §9 declined to define, and it is a *choice*: it
    prices two concurrent streams as the sum of their crossings. A model where a
    single boundary crossed by both replicas is one event, not two, would price
    it lower — see the next bullet.

## Non-claims, labelled

  * ⟨DONE downstream in `Uwueave.Scheduling` and `Uwueave.Protocol`⟩
    **Scheduling and coalescing now have an explicit semantics.** `Scheduling`
    carries attendance and all five currencies in proof-covered demands, proves
    exact coalescing counterexamples, and requires one real schedule for a
    profile upper bound. `Protocol` supplies the compositional deep AST and
    proof-carrying elaboration. The boundary that remains is a theorem, not
    missing machinery: `⊗` here is pointwise addition of *crossings*, while a
    protocol may emit zero, one, or several schedulable demands per crossing.
    Therefore no generic inequality converts this `optimum` into meetings, and
    nothing in this file calls it one.
  * ⟨UNDONE U-0019, narrowed to the native surface and general subsumption⟩ **The
    semantic typing target has landed.** `Protocol.Elaboration` produces checked
    schedules and exact currency-profile bounds, and Preo has checked
    `protocol`/`session` forms whose bodies are typed `Protocol.Term`s. What is
    still absent is a custom parser for those six protocol constructors and a
    general graded weakening/subsumption judgement over `CoordEffect.Profile`;
    `SeamAlgebra`'s candidate laws are not connected to such a judgement here.
  * ⟨TERMINAL for this file⟩ **`optimum` is a min over the supplied space.** Not
    a fix, a definition: the infimum over *all* seams is not a `Nat` this file
    can compute, because seams range over every type in every universe.
    `Cost.coordination_forced` is the tool for statements over all seams, and
    §4 is the only bridge claimed.
  * ⟨UNDONE U-0020⟩ **No liveness, no delivery, no time** — as in `Cost.lean`. A
    profile counts events, never wall-clock.
-/
import Uwueave.Cost

namespace Uwueave.CoordEffect

open Uwueave Uwueave.Segmented Uwueave.Cost

universe u v w

/-! ## §1. Profiles — cost as a function of the strategy, composed pointwise -/

/-- **A cost profile.** The coordination cost of a workload, *as a function of
the strategy chosen for the whole session* — not a number. This is the object
codex's refutation demands: minimization is a thing you do to a profile at the
end, not a thing already baked into the grade. -/
def Profile (X : Type u) : Type u := X → Nat

/-- **Pointwise composition.** Two workloads run in one session under **one**
shared strategy, so their costs add *at each strategy separately*. Nothing is
minimized here; that is the entire point. -/
def Profile.comp {X : Type u} (P Q : Profile X) : Profile X := fun x => P x + Q x

@[inherit_doc] scoped infixl:65 " ⊗ " => Profile.comp

/-- The free profile: a workload that costs nothing under every strategy. Unit
for `⊗`. -/
def Profile.zero (X : Type u) : Profile X := fun _ => 0

/-- Composition is pointwise, by definition — stated so the reading "the cost of
two streams under one strategy" is visible rather than buried in a `fun`. -/
@[simp] theorem Profile.comp_apply {X : Type u} (P Q : Profile X) (x : X) :
    (P ⊗ Q) x = P x + Q x := rfl

theorem Profile.comp_comm {X : Type u} (P Q : Profile X) : P ⊗ Q = Q ⊗ P :=
  funext fun x => Nat.add_comm (P x) (Q x)

theorem Profile.comp_assoc {X : Type u} (P Q R : Profile X) :
    (P ⊗ Q) ⊗ R = P ⊗ (Q ⊗ R) :=
  funext fun x => Nat.add_assoc (P x) (Q x) (R x)

theorem Profile.zero_comp {X : Type u} (P : Profile X) : Profile.zero X ⊗ P = P :=
  funext fun x => Nat.zero_add (P x)

theorem Profile.comp_zero {X : Type u} (P : Profile X) : P ⊗ Profile.zero X = P :=
  funext fun x => Nat.add_zero (P x)

/-! ## §2. The strategy space, and the deferred minimum

Minimization needs a space to minimize over, and the honest one is **finite and
nonempty**: a head strategy and a list of alternatives. Nonemptiness is not
bookkeeping — it is what makes `optimum_achieved` (§2's soundness result) true
rather than vacuous. -/

/-- **A finite, nonempty space of admissible strategies.** A head and a tail, so
"the space is nonempty" is a fact about the type rather than a hypothesis anyone
can forget to discharge. -/
structure Admissible (X : Type u) where
  /-- One admissible strategy, always present. -/
  head : X
  /-- The remaining admissible strategies. -/
  rest : List X

/-- The space as a list — always a `cons`, hence never empty. -/
def Admissible.toList {X : Type u} (A : Admissible X) : List X := A.head :: A.rest

theorem Admissible.head_mem {X : Type u} (A : Admissible X) : A.head ∈ A.toList :=
  List.mem_cons_self

theorem Admissible.mem_of_mem_rest {X : Type u} {A : Admissible X} {x : X}
    (h : x ∈ A.rest) : x ∈ A.toList :=
  List.mem_cons_of_mem _ h

/-- The standard finite minimum of an accumulator and the mapped profile.
`optimum` seeds it with the head strategy's cost, which is where nonemptiness
is spent. -/
def minAlong {X : Type u} (P : Profile X) (n : Nat) (xs : List X) : Nat :=
  ((n :: xs.map P).min?).getD n

/-- `minAlong` is the standard minimum of its accumulator and mapped inputs.
This is the canonical bridge to `List.min?` and its specification library. -/
theorem minAlong_eq_listMin {X : Type u} (P : Profile X) (n : Nat) (xs : List X) :
    minAlong P n xs = ((n :: xs.map P).min?).getD n := rfl

theorem minAlong_le_acc {X : Type u} (P : Profile X)
    (n : Nat) (xs : List X) : minAlong P n xs ≤ n := by
  rw [minAlong_eq_listMin]
  exact List.min?_getD_le_of_mem List.mem_cons_self

theorem minAlong_le_of_mem {X : Type u} (P : Profile X)
    (n : Nat) (xs : List X) (x : X) (hx : x ∈ xs) : minAlong P n xs ≤ P x := by
  rw [minAlong_eq_listMin]
  exact List.min?_getD_le_of_mem
    (List.mem_cons_of_mem n (List.mem_map.mpr ⟨x, hx, rfl⟩))

theorem le_minAlong {X : Type u} (P : Profile X) (k n : Nat) (xs : List X)
    (hn : k ≤ n) (hall : ∀ x ∈ xs, k ≤ P x) : k ≤ minAlong P n xs := by
  apply (List.le_min?_iff (show (n :: xs.map P).min? = some (minAlong P n xs) by
    simp [minAlong])).2
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact hn
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact hall x hx

theorem minAlong_achieved {X : Type u} (P : Profile X) (n : Nat) (xs : List X) :
    minAlong P n xs = n ∨ ∃ x ∈ xs, minAlong P n xs = P x := by
  have hm : minAlong P n xs ∈ n :: xs.map P :=
    List.min?_mem (show (n :: xs.map P).min? = some (minAlong P n xs) by
      simp [minAlong])
  rcases List.mem_cons.mp hm with hm | hm
  · exact Or.inl hm
  · obtain ⟨x, hx, hPx⟩ := List.mem_map.mp hm
    exact Or.inr ⟨x, hx, hPx.symm⟩

/-- **The deferred minimum.** Compose profiles for as long as the session runs;
`optimum` is what you take when it closes. It is a minimum over the *supplied*
space — see the module's ⟨scope⟩ note and `optimum_antitone_of_subset`. -/
def optimum {X : Type u} (A : Admissible X) (P : Profile X) : Nat :=
  minAlong P (P A.head) A.rest

/-- The optimum is no worse than any admissible strategy's cost. -/
theorem optimum_le_of_mem {X : Type u} {A : Admissible X} {P : Profile X} {x : X}
    (hx : x ∈ A.toList) : optimum A P ≤ P x := by
  simp only [Admissible.toList, List.mem_cons] at hx
  rcases hx with h | h
  · subst h; exact minAlong_le_acc P (P A.head) A.rest
  · exact minAlong_le_of_mem P _ _ x h

/-- A lower bound on every admissible strategy is a lower bound on the optimum
— the direction every floor result below travels. -/
theorem le_optimum {X : Type u} {A : Admissible X} {P : Profile X} {k : Nat}
    (h : ∀ x ∈ A.toList, k ≤ P x) : k ≤ optimum A P :=
  le_minAlong P k (P A.head) A.rest (h A.head A.head_mem)
    (fun x hx => h x (Admissible.mem_of_mem_rest hx))

/-- **The optimum is attained at an admissible strategy.** Not an infimum with
no witness: the number `optimum A P` is a cost some single member of the space
actually pays. This is what makes minimizing a composed profile *sound* — see
`optimum_compose_achieved`. -/
theorem optimum_achieved {X : Type u} (A : Admissible X) (P : Profile X) :
    ∃ x ∈ A.toList, optimum A P = P x := by
  rcases minAlong_achieved P (P A.head) A.rest with h | ⟨x, hx, hxe⟩
  · exact ⟨A.head, A.head_mem, h⟩
  · exact ⟨x, Admissible.mem_of_mem_rest hx, hxe⟩

/-- **A richer catalogue of strategies never costs more.** This is the module's
⟨scope⟩ note as a theorem: `optimum A P` is a minimum over the strategies we
listed, so it is an *upper bound* on the true infimum, and the only way it moves
when the space grows is down. Every floor proved below is therefore a floor for
the enlarged space too. -/
theorem optimum_antitone_of_subset {X : Type u} (A B : Admissible X) (P : Profile X)
    (h : ∀ x ∈ A.toList, x ∈ B.toList) : optimum B P ≤ optimum A P := by
  obtain ⟨x, hx, hxe⟩ := optimum_achieved A P
  rw [hxe]
  exact optimum_le_of_mem (h x hx)

/-! ## §3. THE HEADLINE — composing then minimizing is never cheaper

`min_σ (c₁ σ + c₂ σ) ≥ (min_σ c₁ σ) + (min_σ c₂ σ)`, in the library's terms, and
the gap is real (§5). -/

/-- **THE INEQUALITY.** Composing profiles and *then* minimizing is never
cheaper than minimizing each independently, and §5 shows it can be strictly
worse. The scalar coordination grade computes the right-hand side; the cost a
session actually pays is the left. That difference is codex's refutation, and
this is it as a theorem.

The proof is the whole content of the refutation in three lines: the composed
optimum is attained at *one* strategy `x` (`optimum_achieved`), and each
independent optimum is ≤ that same `x`'s cost — but nothing forces the two
independent optima to be attained at `x`, or at each other. -/
theorem opt_compose_ge_sum_opt {X : Type u} (A : Admissible X) (P Q : Profile X) :
    optimum A (P ⊗ Q) ≥ optimum A P + optimum A Q := by
  obtain ⟨x, hx, hxe⟩ := optimum_achieved A (P ⊗ Q)
  have h1 : optimum A P ≤ P x := optimum_le_of_mem hx
  have h2 : optimum A Q ≤ Q x := optimum_le_of_mem hx
  have hsplit : (P ⊗ Q) x = P x + Q x := rfl
  omega

/-- **The composed optimum is payable by one coherent strategy.** The soundness
statement for the discipline: compose-then-minimize does not return an
abstraction, it returns the cost of a single admissible strategy that both
workloads share. Hypotheses, all structural: the space is nonempty (`Admissible`
carries a `head`) and finite (it is a `List`); §4's `Strategy` additionally makes
every member a seam the invariant admits. -/
theorem optimum_compose_achieved {X : Type u} (A : Admissible X) (P Q : Profile X) :
    ∃ x ∈ A.toList, optimum A (P ⊗ Q) = P x + Q x := by
  obtain ⟨x, hx, hxe⟩ := optimum_achieved A (P ⊗ Q)
  exact ⟨x, hx, hxe⟩

/-- **Exactly when the scalar grade is sound.** If one admissible strategy is
optimal for *both* workloads at once, composing and minimizing agrees with
minimizing independently. So the scalar grade was not wrong about arithmetic —
it silently assumed a **common minimizer**, and §5 exhibits a workload with
none. Stated as the repair's boundary: a scalar grade is sound on a session
whose streams share an optimum, and nowhere else in general. -/
theorem opt_compose_eq_sum_opt_of_common_optimum {X : Type u} (A : Admissible X)
    (P Q : Profile X) {x : X} (hx : x ∈ A.toList)
    (hP : P x = optimum A P) (hQ : Q x = optimum A Q) :
    optimum A (P ⊗ Q) = optimum A P + optimum A Q := by
  have hle : optimum A (P ⊗ Q) ≤ P x + Q x := optimum_le_of_mem hx
  have hge := opt_compose_ge_sum_opt A P Q
  omega

/-! ### The session form — n streams, one strategy, minimized at the close -/

/-- A session's profile: every stream's profile composed pointwise. Minimization
happens once, on this, when the session closes. -/
def sessionProfile {X : Type u} : List (Profile X) → Profile X
  | [] => Profile.zero X
  | P :: Ps => P ⊗ sessionProfile Ps

/-- What the scalar grade would compute for a session: each stream minimized on
its own, then summed. `opt_session_ge_sum_opt` says this under-reports. -/
def independentTotal {X : Type u} (A : Admissible X) : List (Profile X) → Nat
  | [] => 0
  | P :: Ps => optimum A P + independentTotal A Ps

/-- **The headline, n-ary.** Over a whole session, the sum of per-stream optima
is a lower bound on the session's real optimum — the scalar grade under-reports
the session, not merely a pair. -/
theorem opt_session_ge_sum_opt {X : Type u} (A : Admissible X) :
    ∀ Ps : List (Profile X), optimum A (sessionProfile Ps) ≥ independentTotal A Ps := by
  intro Ps
  induction Ps with
  | nil => exact Nat.zero_le _
  | cons P Ps ih =>
      have hstep := opt_compose_ge_sum_opt A P (sessionProfile Ps)
      show optimum A (P ⊗ sessionProfile Ps) ≥ optimum A P + independentTotal A Ps
      omega

/-! ## §4. Strategies are seams — and the spec-forced floor bounds the optimum

A strategy is a seam **with its validity proof attached**, so an admissible
space cannot contain a projection the invariant does not admit. The profile of a
workload is then `Cost.crossings` as a function of the strategy. -/

/-- **A coordination strategy: a valid seam.** Bundling `SegmentedIConfluent`
with the projection is what makes `optimum` meaningful — a minimum over
projections that are not seams would be a smaller number and a false one. -/
structure Strategy {S : Type u} [MergeState S] (I : Invariant S) (Seg : Type v) where
  /-- The seam this strategy coordinates at. -/
  seam : S → Seg
  /-- …and the proof it is one: merges inside a fiber are legal and stay inside. -/
  valid : SegmentedIConfluent seam I

/-- **The profile of one op stream**: its `Cost.crossings` count, as a function
of the strategy the session picks. This is the object that used to be collapsed
to a `Nat` too early. -/
def streamProfile {S : Type u} {Seg : Type v} {Op : Type w} [MergeState S]
    [DecidableEq Seg] {I : Invariant S} (step : S → Op → S) (s : S) (w : List Op) :
    Profile (Strategy I Seg) :=
  fun τ => crossings τ.seam step s w

@[simp] theorem streamProfile_apply {S : Type u} {Seg : Type v} {Op : Type w}
    [MergeState S] [DecidableEq Seg] {I : Invariant S} (step : S → Op → S) (s : S)
    (w : List Op) (τ : Strategy I Seg) :
    streamProfile step s w τ = crossings τ.seam step s w := rfl

/-- **The spec-forced floor lower-bounds the profile's minimum.** A workload
whose run passes through `n` clash pairs costs at least `n` under *every*
admissible strategy, hence at least `n` after minimization.

Profiles therefore **refine** `Cost.coordination_forced` rather than replacing
it: the floor that is a fact about the specification survives the move from a
number to a function, and it is what a `@ ≤ n` grade would have to respect. -/
theorem forced_le_optimum {S : Type u} {Seg : Type v} {Op : Type w} [MergeState S]
    [DecidableEq Seg] {I : Invariant S} {step : S → Op → S} {s : S}
    {bs : List (List Op)} (hcl : ClashBlocks I step s bs)
    (A : Admissible (Strategy I Seg)) :
    bs.length ≤ optimum A (streamProfile step s bs.flatten) :=
  le_optimum (fun τ _ => coordination_lower_bound τ.valid hcl)

/-- **Forced floors ARE additive across composed streams** — the thing the
scalar grade could not say. Optima do not add (§3, §5), but the
specification-forced floors of two concurrently-run streams do, because the
floor holds at *every* strategy pointwise and pointwise addition is what `⊗`
does. So a session's budget must be at least the sum of its streams' floors,
and that statement is available in profile form without a common minimizer. -/
theorem forced_le_optimum_compose {S : Type u} {Seg : Type v} {Op : Type w}
    [MergeState S] [DecidableEq Seg] {I : Invariant S} {step : S → Op → S}
    {s₁ s₂ : S} {bs₁ bs₂ : List (List Op)}
    (h₁ : ClashBlocks I step s₁ bs₁) (h₂ : ClashBlocks I step s₂ bs₂)
    (A : Admissible (Strategy I Seg)) :
    bs₁.length + bs₂.length
      ≤ optimum A (streamProfile step s₁ bs₁.flatten ⊗ streamProfile step s₂ bs₂.flatten) := by
  refine le_optimum (fun τ _ => ?_)
  have e₁ := coordination_lower_bound τ.valid h₁
  have e₂ := coordination_lower_bound τ.valid h₂
  show bs₁.length + bs₂.length
    ≤ crossings τ.seam step s₁ bs₁.flatten + crossings τ.seam step s₂ bs₂.flatten
  omega

/-! ## §5. ⚠ THE STRICT WITNESS — two free streams whose composition is not

`Cost.lean` §9 proved the shape codex's falsifiability bar asks for: on the
uniqueness ceiling, pinning `true` is free under the seam "is `false` pinned?",
pinning `false` is free under "is `true` pinned?", and **no valid seam frees
both** (`Cost.no_seam_frees_both`). As profiles that is a strict instance of
§3 — and it is what refutes the scalar grade rather than merely bounding it. -/

/-- The strategy that frees the stream pinning `true`: the seam "is `false`
pinned?", valid by `Cost.seamFalse_segmented`. -/
def pinFreeingTrue : Strategy pinInv Bool :=
  ⟨fun s => s false, seamFalse_segmented⟩

/-- The strategy that frees the stream pinning `false`: the mirror seam, valid
by `Cost.seamTrue_segmented`. -/
def pinFreeingFalse : Strategy pinInv Bool :=
  ⟨fun s => s true, seamTrue_segmented⟩

/-- The admissible space for the pin workload: the two seams `Cost.lean` §9
exhibits. Both are valid; neither frees both streams. -/
def pinSpace : Admissible (Strategy pinInv Bool) :=
  ⟨pinFreeingTrue, [pinFreeingFalse]⟩

/-- The profile of the stream that pins `true`, at any segment type. -/
def pinTrueProfile {Seg : Type v} [DecidableEq Seg] : Profile (Strategy pinInv Seg) :=
  streamProfile pinStep emptyPin [true]

/-- The profile of the stream that pins `false`, at any segment type. -/
def pinFalseProfile {Seg : Type v} [DecidableEq Seg] : Profile (Strategy pinInv Seg) :=
  streamProfile pinStep emptyPin [false]

theorem pinFreeingTrue_mem : pinFreeingTrue ∈ pinSpace.toList :=
  pinSpace.head_mem

theorem pinFreeingFalse_mem : pinFreeingFalse ∈ pinSpace.toList :=
  Admissible.mem_of_mem_rest List.mem_cons_self

/-- **Each stream is free somewhere in the space.** `Cost.lean`'s two zero
counts, read as profile values. -/
theorem pin_streams_free :
    pinTrueProfile pinFreeingTrue = 0 ∧ pinFalseProfile pinFreeingFalse = 0 :=
  ⟨pinTrue_free_under_seamFalse, pinFalse_free_under_seamTrue⟩

/-- The other half of each seam's bill: the seam that frees the `true`-stream
charges the `false`-stream one crossing, and vice versa. This is what makes the
two profiles genuinely *incompatible* rather than merely distinct. -/
theorem pin_streams_pay :
    pinFalseProfile pinFreeingTrue = 1 ∧ pinTrueProfile pinFreeingFalse = 1 := by
  constructor
  · show crossings (fun s : PinSet => s false) pinStep emptyPin [false] = 1
    decide
  · show crossings (fun s : PinSet => s true) pinStep emptyPin [true] = 1
    decide

/-- **Both per-stream optima are zero** — the number a scalar grade would carry
for each stream, and hence `0 + 0 = 0` for the pair. -/
theorem pin_stream_optima_zero :
    optimum pinSpace pinTrueProfile = 0 ∧ optimum pinSpace pinFalseProfile = 0 := by
  constructor
  · have h1 : optimum pinSpace pinTrueProfile ≤ pinTrueProfile pinFreeingTrue :=
      optimum_le_of_mem pinFreeingTrue_mem
    have h2 : pinTrueProfile pinFreeingTrue = 0 := pin_streams_free.1
    omega
  · have h1 : optimum pinSpace pinFalseProfile ≤ pinFalseProfile pinFreeingFalse :=
      optimum_le_of_mem pinFreeingFalse_mem
    have h2 : pinFalseProfile pinFreeingFalse = 0 := pin_streams_free.2
    omega

/-- ⚠ **The composed profile is positive at EVERY strategy** — `Cost.no_seam_frees_both`
as a statement about the composition. There is no admissible strategy, in any
segment type and any universe, under which both streams run free; so the
per-stream sum of minima (`0`) is a cost **nobody can pay**. This is the
unsoundness of the scalar grade exhibited, not merely bounded. -/
theorem pin_indep_min_unpayable {Seg : Type v} [DecidableEq Seg]
    (τ : Strategy pinInv Seg) : 0 < (pinTrueProfile ⊗ pinFalseProfile) τ := by
  have h := no_seam_frees_both τ.seam τ.valid
  show 0 < crossings τ.seam pinStep emptyPin [true] + crossings τ.seam pinStep emptyPin [false]
  by_cases h1 : crossings τ.seam pinStep emptyPin [true] = 0
  · by_cases h2 : crossings τ.seam pinStep emptyPin [false] = 0
    · exact absurd ⟨h1, h2⟩ h
    · omega
  · omega

/-- **The floor survives every enlargement of the strategy space.** The composed
optimum is at least one for *every* admissible space over *every* segment type
(with `DecidableEq`, the binder `crossings` carries) in *every* universe —
because the positivity above is pointwise and universal. So the strictness below
is not an artefact of listing only two seams: no catalogue of seams, however
large, rescues the scalar grade here. -/
theorem pin_composed_floor_universal {Seg : Type v} [DecidableEq Seg]
    (A : Admissible (Strategy pinInv Seg)) :
    1 ≤ optimum A (pinTrueProfile ⊗ pinFalseProfile) :=
  le_optimum (fun τ _ => pin_indep_min_unpayable τ)

/-- ⚠ **THE STRICT WITNESS — the scalar coordination grade is refuted.**

Two workloads, each costing **zero** under some valid seam
(`pin_stream_optima_zero`), whose composition costs **at least one** under every
shared strategy (`pin_composed_floor_universal`). So

    optimum (P₁ ⊗ P₂)  >  optimum P₁ + optimum P₂

and `opt_compose_ge_sum_opt` is not a triviality: the gap it allows is realised
by two one-op streams over a two-element pin set. A grade of the refuted scalar
kind would have accepted `session @ ≤ 0` for this pair — each stream's best seam
is free — for a session in which every coherent schedule coordinates. -/
theorem pin_opt_compose_strict :
    optimum pinSpace pinTrueProfile + optimum pinSpace pinFalseProfile
      < optimum pinSpace (pinTrueProfile ⊗ pinFalseProfile) := by
  have h := pin_stream_optima_zero
  have hfloor := pin_composed_floor_universal pinSpace
  omega

/-- **Floor and achievement meet: the pin session costs exactly one.** The
composed optimum is not merely positive — it is `1`, paid by either seam (each
frees one stream and charges the other, `pin_streams_pay`). So the gap between
the scalar grade and the truth on this workload is exactly `0` against `1`: not
a slack bound, a wrong number. -/
theorem pin_session_costs_exactly_one :
    optimum pinSpace (pinTrueProfile ⊗ pinFalseProfile) = 1 := by
  have hle : optimum pinSpace (pinTrueProfile ⊗ pinFalseProfile)
      ≤ (pinTrueProfile ⊗ pinFalseProfile) pinFreeingTrue :=
    optimum_le_of_mem pinFreeingTrue_mem
  have h1 : pinTrueProfile pinFreeingTrue = 0 := pin_streams_free.1
  have h2 : pinFalseProfile pinFreeingTrue = 1 := pin_streams_pay.1
  have hval : (pinTrueProfile ⊗ pinFalseProfile) pinFreeingTrue
      = pinTrueProfile pinFreeingTrue + pinFalseProfile pinFreeingTrue := rfl
  have hge := pin_composed_floor_universal pinSpace
  omega

/-- The same witness read as the failure of the equality condition of §3: the
pin workload has **no common minimizer**, which is exactly the hypothesis
`opt_compose_eq_sum_opt_of_common_optimum` needs and the one a scalar grade
assumes without saying so. -/
theorem pin_no_common_optimum (τ : Strategy pinInv Bool) (hτ : τ ∈ pinSpace.toList) :
    ¬ (pinTrueProfile τ = optimum pinSpace pinTrueProfile
        ∧ pinFalseProfile τ = optimum pinSpace pinFalseProfile) := by
  intro ⟨h1, h2⟩
  have heq := opt_compose_eq_sum_opt_of_common_optimum pinSpace
    pinTrueProfile pinFalseProfile hτ h1 h2
  have hstrict := pin_opt_compose_strict
  omega

/-! ## §6. The readings, side by side

The scalar grade's number, the profile's number, and the gap between them — each
a term rather than a slogan. -/

/-- What a scalar grade reports for the pin session: zero. -/
example : optimum pinSpace pinTrueProfile + optimum pinSpace pinFalseProfile = 0 := by
  have h := pin_stream_optima_zero
  omega

/-- What the session actually costs: exactly one. By
`pin_composed_floor_universal`, no larger catalogue of seams goes lower. -/
example : optimum pinSpace (pinTrueProfile ⊗ pinFalseProfile) = 1 :=
  pin_session_costs_exactly_one

/-- And the composed optimum is a cost some single admissible strategy pays —
the discipline's soundness, at the witness. -/
example : ∃ τ ∈ pinSpace.toList,
    optimum pinSpace (pinTrueProfile ⊗ pinFalseProfile)
      = pinTrueProfile τ + pinFalseProfile τ :=
  optimum_compose_achieved pinSpace pinTrueProfile pinFalseProfile

end Uwueave.CoordEffect
