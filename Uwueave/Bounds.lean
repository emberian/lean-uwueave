/-
# Uwueave.Bounds — the modal bound and the quantitative bound, composed.

Two lower bounds were built in this tree by different hands and never touched.

  * **Modal** (`Necessity.lean`): a `ReachableClash` — two successful local runs
    from a common ancestor whose join is illegal — refutes `IsCFCS`. *Zero
    coordination is impossible.*
  * **Quantitative** (`Cost.lean`): `ClashBlocks` — a stream carved into blocks
    whose endpoints clash — forces `bs.length ≤ crossings σ` under **every** seam
    in **every** universe. *The count is at least this.*

This file composes them, and the composition is not a formality: the two models
carve "reachable clash" differently, they agree in one direction only, and the
direction they fail in is the one a checker would want.

## What is proved here

**§2–3 — the bridge, and THE COMPOSED THEOREM.** A `Cost` clash block *is* a
`Necessity` partition scenario: block `b` from `s` accuses the pair
`(s, run step s b)`, which is the fork where one replica idles (`opsx = []`) and
the other runs the block. So from one nonempty clash decomposition:

    coordination_necessary_and_costly :
      Realizes impl step s b → ClashBlocks I step s (b :: bs) →
        ¬ IsCFCS impl I ∧ ¬ IConfluent I
          ∧ ∀ {Seg} [DecidableEq Seg] (σ), SegmentedIConfluent σ I →
              (b :: bs).length ≤ crossings σ step s (b :: bs).flatten

`Realizes` is the whole of the compatibility the two models need: `Cost` prices a
**total** `step`, `Necessity` quantifies over **partial** `tryApply`, and
`Realizes impl step s b` says this implementation can actually commit the block.
`totalImpl` realizes everything, so the hypothesis is discharged for free on the
canonical lift.

**§4 — ⚠ ZERO IS NOT THE MODAL CASE, and this is the file's main finding.** One
direction holds: a realizing CFCS implementation admits no nonempty clash
decomposition (`no_clashBlock_of_cfcs`). The converse is **false**, with a
witness this repo already owns. `Cost.pinStep` is inflationary, so
`clashBlocks_nil_of_inflationary` kills *every* clash decomposition of *every*
pin stream — the per-stream floor is zero and no positive `ForcedFloor` exists at
all — and yet `pinInv` admits a reachable clash (pin `true` ∥ pin `false`), so
**no implementation that can perform the two pins is CFCS**
(`no_pin_capable_impl_is_cfcs`; the hypotheses are "the implementation does its
job", so this is not an artefact of `totalImpl` being careless — it is not even
locally safe, and `pinImpl_not_locallySafe` says so out loud, while the
refutation runs through the *merge* clause and covers locally safe shapes too).
`zero_floor_licenses_cfcs_false` refutes the licensing claim in general, in the
shape `Budget.lower_bound_does_not_license_acceptance` uses, and it quantifies
over implementations rather than fixing one.

The mechanism, exactly: **`ClashBlocks` is a SEQUENTIAL clash** (a state against
its own successor along one stream) and **`ReachableClash` is a CONCURRENT one**
(two states on divergent streams). Every sequential clash is a concurrent one —
idle one side, §2 — and no converse exists, because comparable states on an
inflationary run never clash while divergent ones do.

**§5 — the family, modally flat.** `Budget` proved the floor is not a function:
one workload carries `ForcedFloor _ 1` and `ForcedFloor _ 3` and *which member
you hold decides the budget verdict*. Modally the family is flat: **any** positive
member refutes CFCS (`not_cfcs_of_positive_forcedFloor`), no supremum is needed,
and a finer carving refutes nothing harder — `budget_forced_one`, the member
`lower_bound_does_not_license_acceptance` punishes as useless, already gives the
same `¬ IsCFCS` as `budget_forced_three`.

**§6 — where `Cost` DOES refine `Necessity`: the session, not the stream.** A
fork clash cannot be free under any valid seam — if both runs cost zero the
endpoints share a fiber and the seam certifies their merge
(`fork_clash_charges_the_pair`). The charge lands on the **sum**, which is why
the per-stream floor of §4 cannot see it. In `CoordEffect`'s language, a
reachable clash puts the composed session's optimum at ≥ 1 over every admissible
space at every segment type in every universe. `CoordEffect.pin_composed_floor_universal`
falls out as the instance at `pinClash` — its strict witness is a *corollary of
the modal model*, which is the contact this file was looking for.

**§7 — the Live/LatticeOnly axis, both halves.**

  * The reassuring half, proved: `clashBlocks_accuse_only_occupied` — every state
    a clash decomposition accuses is `run step s p` for a **prefix** `p` of the
    stream. A forced floor never charges for a state the workload's own run does
    not occupy. The only unoccupied state is the illegal merge, which is what the
    coordination event prevents.
  * ⚠ The warning half, also proved: occupancy is only as sound as `step`.
    `Cost`'s workload model is a total order of ops with **no happens-before
    constraint**, while `CausalReach`'s unreachability results are constraints on
    `hb`. `ewWorkload` is a legal `Budget.Workload` carrying
    `ForcedFloor _ 1` whose accused pair is exactly the element-wide OR-Set pair
    **no cut of `ewH` reaches**, and
    `ew_rejected_at_zero_over_unreachable_pair` runs it through
    `Budget.rejected_sound`: *no plan fits, in any universe*, over a pair no
    history produces. `RunLegal` checks that occupied states are **legal**; no
    field checks that they are **reachable**, because the cost model has no `hb`
    to check them against.
  * And separately: seam validity is charged lattice-wide even where reachability
    is not. `latticeOnly_clash_still_separated` — every valid seam for presence
    must put the two unreachable states in different fibers, because
    `SegmentedIConfluent` quantifies over all legal states. An unreachable clash
    cannot raise a **floor**; it can still shrink the space of admissible plans.

## Non-claims, labelled

  * ⟨scope⟩ **`Realizes` is a hypothesis, not a construction.** Nothing here
    builds an implementation from a `step` other than `totalImpl`, whose
    `tryApply` never aborts. A partial implementation that aborts inside the
    block does not realize it and the composed theorem says nothing about it —
    correctly: it cannot perform the workload being priced.
  * ⟨scope⟩ **`totalImpl` is not asserted `LocallySafe`.** It usually is not
    (`Budget`'s `RunLegal` scope note is the same observation), and the composed
    theorem does not need it: `ReachableClash` refutes the *merge* clause.
  * ⟨TERMINAL for this file⟩ **Crossings are not meetings**, inherited whole from
    `Cost.lean` and `CoordEffect.lean`. Every `Nat` here is a seam crossing on a
    replica's stream; nothing in this file models attendance or coalescing.
  * ⟨UNDONE⟩ **No exact modal/quantitative correspondence is claimed or
    available.** §4 is a proof that none exists at zero for the per-stream
    measure, and §6 is a one-directional bridge at the session level. What a
    quantity whose zero *is* the modal zero would look like — a fork-aware floor,
    minimized over seams globally — is not defined here.
  * ⟨scope⟩ **`[DecidableEq Seg]`** on every seam, inherited from
    `Cost.crossings`. The `∀ σ` floors are not vacuous over an empty class:
    `id_segmented` shows the identity seam is always valid, and
    `ew_teleport_floor_inhabited` instantiates the §7 floor at it — through
    `orsetDecEq`, a classical instance used to instantiate, never to compute.
-/
import Uwueave.Necessity
import Uwueave.Budget
import Uwueave.CoordEffect
import Uwueave.CausalReach

namespace Uwueave.Bounds

open Uwueave Uwueave.Catalog Uwueave.Segmented Uwueave.ORSet
open Uwueave.Cost Uwueave.Budget Uwueave.CoordEffect

universe u v w

/-! ## §1. The bridge — one model's total step as the other's implementation

`Cost` measures a **total** `step : S → Op → S`. `Necessity` quantifies over
**partial** `tryApply : Op → S → Option S`, where `none` is a local abort. The
two talk through `Realizes`: the implementation can actually commit the stream
`Cost` is pricing, and lands where the total step says. -/

/-- The `Cost` model's total local transition, read as a `Necessity`
implementation: every op commits, at the state `step` computes. (`Impl.tryApply`
takes the op first and the state second; `step` the other way round.) -/
def totalImpl {S : Type u} {Op : Type w} (step : S → Op → S) : Necessity.Impl S Op where
  tryApply := fun o s => some (step s o)

/-- An implementation **realizes** the stream `w` from `s` against `step` when
the whole stream commits locally and lands exactly where the total transition
says. This is the entire compatibility the two models need in order to compose:
a `Cost` workload prices a trajectory, and `Realizes` is the statement that this
implementation can *perform* it. -/
def Realizes {S : Type u} {Op : Type w} (impl : Necessity.Impl S Op)
    (step : S → Op → S) (s : S) (w : List Op) : Prop :=
  Necessity.RunsTo impl s (Cost.run step s w) w

/-- The total lift realizes every stream from every state — it has no abort. So
every composed statement below is available unconditionally at `totalImpl`, and
the `Realizes` hypothesis exists only to let *other* implementations in. -/
theorem totalImpl_realizes {S : Type u} {Op : Type w} (step : S → Op → S) :
    ∀ (s : S) (w : List Op), Realizes (totalImpl step) step s w := by
  intro s w
  induction w generalizing s with
  | nil => rfl
  | cons o w ih => exact ih (step s o)

/-- Under the total lift the two models' `run`s agree: a successful `Necessity`
run lands exactly at `Cost.run`. This is what lets a `ReachableClash` stated in
the necessity model be *counted* in the cost model. -/
theorem runsTo_totalImpl_eq {S : Type u} {Op : Type w} {step : S → Op → S}
    {s x : S} {w : List Op} (h : Necessity.RunsTo (totalImpl step) s x w) :
    x = Cost.run step s w := by
  induction w generalizing s with
  | nil => exact (Option.some.inj h).symm
  | cons o w ih => exact ih h

/-- **Every "for every seam" statement below is inhabited.** The identity seam is
always valid: same fiber means *equal states*, and a state merged with itself is
itself. Operationally it is the maximally expensive plan — coordinate on every
state change — and it is what stops the universally-quantified floors of `Cost`
(and their instantiations here) from being vacuously true over an empty class of
seams. -/
theorem id_segmented {S : Type u} [MergeState S] (I : Invariant S) :
    SegmentedIConfluent (id : S → S) I := by
  intro x y h hx _
  have hxy : x = y := h
  subst hxy
  rw [merge_idem]
  exact ⟨hx, rfl⟩

/-! ## §2. A sequential clash IS a partition scenario

`Cost.ClashBlocks` accuses the pair `(s, run step s b)` — a state and its own
successor along one stream. `Necessity.ReachableClash` wants two states on
divergent runs from a common ancestor. The first is an instance of the second:
one replica idles. -/

/-- **The head of a clash decomposition is a reachable clash.** Common legal
ancestor `s`; replica A runs the empty stream and stays at `s`; replica B commits
the block and reaches `run step s b`; their join is illegal — which is exactly
what the block asserts.

The `Realizes` hypothesis is load-bearing and minimal: replica B must be able to
commit the block. -/
def reachableClash_of_clashBlock {S : Type u} {Op : Type w} [MergeState S]
    {I : Invariant S} {step : S → Op → S} {s : S} {b : List Op}
    {bs : List (List Op)} (impl : Necessity.Impl S Op)
    (hreal : Realizes impl step s b)
    (h : Cost.ClashBlocks I step s (b :: bs)) :
    Necessity.ReachableClash impl I :=
  let h' : I s ∧ I (Cost.run step s b) ∧ ¬ I (s ⊔ Cost.run step s b)
      ∧ Cost.ClashBlocks I step (Cost.run step s b) bs := h
  { base := s
    x := s
    y := Cost.run step s b
    opsx := []
    opsy := b
    hbase := h'.1
    hx_run := rfl
    hy_run := hreal
    hx := h'.1
    hy := h'.2.1
    hbad := h'.2.2.1 }

/-- **The modal half.** A realizable clash block refutes coordination-free
convergent safety for that implementation, and refutes the lattice judgement
outright. -/
theorem not_cfcs_of_clashBlock {S : Type u} {Op : Type w} [MergeState S]
    {I : Invariant S} {step : S → Op → S} {s : S} {b : List Op}
    {bs : List (List Op)} (impl : Necessity.Impl S Op)
    (hreal : Realizes impl step s b)
    (h : Cost.ClashBlocks I step s (b :: bs)) :
    ¬ Necessity.IsCFCS impl I ∧ ¬ IConfluent I :=
  Necessity.necessity (reachableClash_of_clashBlock impl hreal h)

/-- The lattice half needs no implementation at all: a clash block's two
endpoints are legal states whose merge is not. -/
theorem not_iconfluent_of_clashBlock {S : Type u} {Op : Type w} [MergeState S]
    {I : Invariant S} {step : S → Op → S} {s : S} {b : List Op}
    {bs : List (List Op)} (h : Cost.ClashBlocks I step s (b :: bs)) :
    ¬ IConfluent I :=
  let h' : I s ∧ I (Cost.run step s b) ∧ ¬ I (s ⊔ Cost.run step s b)
      ∧ Cost.ClashBlocks I step (Cost.run step s b) bs := h
  fun hI => h'.2.2.1 (hI s (Cost.run step s b) h'.1 h'.2.1)

/-! ## §3. THE COMPOSED THEOREM -/

/-- **THE COMPOSED BOUND.** One nonempty clash decomposition, two verdicts that
were never before stated together:

  * **modal** — no coordination-free convergent safe implementation exists among
    those that can perform the block, and the invariant fails I-confluence;
  * **quantitative** — every implementation pays at least `(b :: bs).length`
    coordination events, under every seam, at every segment type, in every
    universe.

The hypotheses are exactly the two models' own: `Realizes` for the modal half
(the implementation must be able to commit the block) and nothing extra for the
quantitative half (`Cost.coordination_forced` needs only the decomposition). -/
theorem coordination_necessary_and_costly {S : Type u} {Op : Type w} [MergeState S]
    {I : Invariant S} {step : S → Op → S} {s : S} {b : List Op}
    {bs : List (List Op)} (impl : Necessity.Impl S Op)
    (hreal : Realizes impl step s b)
    (hcl : Cost.ClashBlocks I step s (b :: bs)) :
    ¬ Necessity.IsCFCS impl I
      ∧ ¬ IConfluent I
      ∧ ∀ {Seg : Type v} [DecidableEq Seg] (σ : S → Seg),
          SegmentedIConfluent σ I →
          (b :: bs).length ≤ Cost.crossings σ step s (b :: bs).flatten := by
  refine ⟨(not_cfcs_of_clashBlock impl hreal hcl).1, not_iconfluent_of_clashBlock hcl, ?_⟩
  intro Seg _ σ hseg
  exact Cost.coordination_forced hcl σ hseg

/-- The composed bound at the canonical lift, with no hypothesis left to
discharge: a clash decomposition alone gives both verdicts. -/
theorem coordination_necessary_and_costly_total {S : Type u} {Op : Type w}
    [MergeState S] {I : Invariant S} {step : S → Op → S} {s : S} {b : List Op}
    {bs : List (List Op)} (hcl : Cost.ClashBlocks I step s (b :: bs)) :
    ¬ Necessity.IsCFCS (totalImpl step) I
      ∧ ¬ IConfluent I
      ∧ ∀ {Seg : Type v} [DecidableEq Seg] (σ : S → Seg),
          SegmentedIConfluent σ I →
          (b :: bs).length ≤ Cost.crossings σ step s (b :: bs).flatten :=
  coordination_necessary_and_costly (totalImpl step) (totalImpl_realizes step s b) hcl

/-- The two halves at their coarsest common reading: the modal verdict says the
count cannot be zero, and the quantitative one says it is at least one. Same
workload, same hypothesis, two languages. -/
theorem cannot_be_free_and_costs_at_least_one {S : Type u} {Seg : Type v}
    {Op : Type w} [MergeState S] [DecidableEq Seg] {I : Invariant S}
    {step : S → Op → S} {s : S} {b : List Op} {bs : List (List Op)}
    {σ : S → Seg} (hseg : SegmentedIConfluent σ I)
    (hcl : Cost.ClashBlocks I step s (b :: bs)) :
    ¬ Necessity.IsCFCS (totalImpl step) I
      ∧ 1 ≤ Cost.crossings σ step s (b :: bs).flatten := by
  refine ⟨(not_cfcs_of_clashBlock (totalImpl step) (totalImpl_realizes step s b) hcl).1, ?_⟩
  have h := Cost.coordination_forced hcl σ hseg
  have hlen : (b :: bs).length = bs.length + 1 := rfl
  omega

/-! ## §4. ⚠ ZERO IS NOT THE MODAL CASE

Does the quantitative bound degenerate to the modal one at zero — is "floor 0"
the same judgement as "CFCS is possible"? **No.** One direction holds and the
other is refutable on a witness this repo already owns. -/

/-- **The direction that holds.** A realizing implementation that *is* CFCS
admits no nonempty clash decomposition — so wherever the modal verdict is
"possible", every forced floor collapses. Above zero the two bounds agree. -/
theorem no_clashBlock_of_cfcs {S : Type u} {Op : Type w} [MergeState S]
    {I : Invariant S} {step : S → Op → S} {impl : Necessity.Impl S Op}
    (hcfcs : Necessity.IsCFCS impl I) {s : S} {b : List Op} {bs : List (List Op)}
    (hreal : Realizes impl step s b) : ¬ Cost.ClashBlocks I step s (b :: bs) :=
  fun hcl => (not_cfcs_of_clashBlock impl hreal hcl).1 hcfcs

/-! ### The witness that the converse fails

`Cost.pinStep` is inflationary, so `Cost.clashBlocks_nil_of_inflationary` empties
**every** clash decomposition of **every** pin stream: no positive `ForcedFloor`
exists for any pin workload. And yet the two one-op streams fork into an illegal
merge. -/

/-- The pin implementation of `Cost` §9 in the necessity model. Pinning always
commits — there is no local check that could fail, which is exactly the
problem. -/
def pinImpl : Necessity.Impl PinSet Bool := totalImpl pinStep

theorem pinInv_emptyPin : pinInv emptyPin := by
  intro m n hm _
  simp [emptyPin] at hm

/-- One pin from nothing is legal: the only pinned node is the one just added. -/
theorem pinInv_pinOne (b : Bool) : pinInv (pinStep emptyPin b) := by
  intro m n hm hn
  revert hm hn
  cases m <;> cases n <;> cases b <;> decide

/-- Two pins from nothing merge to a state pinning both — the uniqueness ceiling
broken at the join, with both sides legal. -/
theorem pin_join_bad : ¬ pinInv (pinStep emptyPin true ⊔ pinStep emptyPin false) := by
  intro h
  exact absurd (h true false (by decide) (by decide)) (by decide)

/-- **The concurrent clash the per-stream floor cannot see.** Empty ─pin true→,
empty ─pin false→, join pins two nodes. Both runs commit; only the merge
breaks. -/
def pinClash : Necessity.ReachableClash pinImpl pinInv where
  base := emptyPin
  x := pinStep emptyPin true
  y := pinStep emptyPin false
  opsx := [true]
  opsy := [false]
  hbase := pinInv_emptyPin
  hx_run := totalImpl_realizes pinStep emptyPin [true]
  hy_run := totalImpl_realizes pinStep emptyPin [false]
  hx := pinInv_pinOne true
  hy := pinInv_pinOne false
  hbad := pin_join_bad

theorem pin_not_cfcs : ¬ Necessity.IsCFCS pinImpl pinInv :=
  Necessity.reachable_clash_refutes_cfcs pinClash

/-- **No implementation that can pin at all is CFCS.** The refutation is not
about `totalImpl` being careless: *any* `impl` whose local rule commits `[true]`
from nothing and commits `[false]` from nothing is refuted, because the failure
is at the merge clause and both runs are individually legal. The hypotheses are
exactly "the implementation does its job"; an implementation that refuses to pin
anything is CFCS and useless. -/
theorem no_pin_capable_impl_is_cfcs (impl : Necessity.Impl PinSet Bool)
    (hT : Necessity.RunsTo impl emptyPin (pinStep emptyPin true) [true])
    (hF : Necessity.RunsTo impl emptyPin (pinStep emptyPin false) [false]) :
    ¬ Necessity.IsCFCS impl pinInv :=
  Necessity.reachable_clash_refutes_cfcs
    { base := emptyPin
      x := pinStep emptyPin true
      y := pinStep emptyPin false
      opsx := [true]
      opsy := [false]
      hbase := pinInv_emptyPin
      hx_run := hT
      hy_run := hF
      hx := pinInv_pinOne true
      hy := pinInv_pinOne false
      hbad := pin_join_bad }

/-- ⚠ The total lift of `pinStep` is not even locally safe — a second pin from a
one-pin state breaks the ceiling on one replica. That is deliberately *not* what
refutes CFCS above: `reachable_clash_refutes_cfcs` goes through the merge clause,
and `no_pin_capable_impl_is_cfcs` covers locally safe implementations too (the
insert-or-abort shape of `Necessity` §6 is one). -/
theorem pinImpl_not_locallySafe : ¬ Necessity.LocallySafe pinImpl pinInv := by
  intro h
  have hbad := h false (pinStep emptyPin true) (pinStep (pinStep emptyPin true) false)
    rfl (pinInv_pinOne true)
  exact absurd (hbad true false (by decide) (by decide)) (by decide)

/-- ⚠ **ZERO IS NOT THE MODAL CASE — the witness.** Every clash decomposition of
every pin stream is empty (left), so no positive forced floor exists for any pin
workload and the quantitative bound says nothing at all; and yet **no**
implementation able to perform the two pins is coordination-free convergent safe
(right).

`Cost` therefore does **not** refine `Necessity` at zero on the per-stream
measure. Reading "the forced floor is 0" as "coordination-freedom is available"
is unsound, and this is the pair that makes it so. -/
theorem zero_floor_does_not_imply_cfcs :
    (∀ (s : PinSet) (bs : List (List Bool)),
        Cost.ClashBlocks pinInv pinStep s bs → bs = [])
      ∧ ∀ impl : Necessity.Impl PinSet Bool,
          Necessity.RunsTo impl emptyPin (pinStep emptyPin true) [true] →
          Necessity.RunsTo impl emptyPin (pinStep emptyPin false) [false] →
          ¬ Necessity.IsCFCS impl pinInv :=
  ⟨fun _ _ h => clashBlocks_nil_of_inflationary pinStep_inflationary h,
   no_pin_capable_impl_is_cfcs⟩

/-- The licensing claim, in the strongest form anyone would want it: *a workload
no clash decomposition can carve admits some implementation that can run it and
is coordination-free convergent safe.* Quantified over implementations rather
than fixed at `totalImpl`, so the refutation cannot be dismissed as an artefact
of a careless lift; restricted to `Type`-level states and ops, which only
strengthens it. -/
def ZeroFloorLicensesCFCS : Prop :=
  ∀ {S Op : Type} [MergeState S] (I : Invariant S) (step : S → Op → S) (s : S),
    (∀ bs : List (List Op), Cost.ClashBlocks I step s bs → bs = []) →
      ∃ impl : Necessity.Impl S Op,
        (∀ w : List Op, Realizes impl step s w) ∧ Necessity.IsCFCS impl I

/-- ⚠ **The licensing claim is false**, in the shape
`Budget.lower_bound_does_not_license_acceptance` uses for the acceptance claim.
A lower bound of zero is not a permission; on the pin it is not even evidence,
because the clash it must see is a *fork* and the measure only looks along one
stream. -/
theorem zero_floor_licenses_cfcs_false : ¬ ZeroFloorLicensesCFCS := by
  intro h
  obtain ⟨impl, hreal, hcfcs⟩ := h pinInv pinStep emptyPin
    (fun _ hcl => clashBlocks_nil_of_inflationary pinStep_inflationary hcl)
  exact no_pin_capable_impl_is_cfcs impl (hreal [true]) (hreal [false]) hcfcs

/-- **The mismatch, named.** `ClashBlocks` is a *sequential* clash — a state
against its own successor along one stream — and `ReachableClash` is a
*concurrent* one — two states on divergent streams. §2 sends the first to the
second; nothing sends the second to the first, and the obstruction is exactly
inflation: comparable states never clash (left conjunct, via
`clashBlocks_nil_of_inflationary`), divergent ones do (right). -/
theorem sequential_clash_strictly_weaker_than_concurrent :
    Inflationary pinStep
      ∧ (∀ (s : PinSet) (bs : List (List Bool)),
          Cost.ClashBlocks pinInv pinStep s bs → bs = [])
      ∧ ¬ Necessity.IsCFCS pinImpl pinInv
      ∧ ¬ IConfluent pinInv :=
  ⟨pinStep_inflationary,
   fun _ _ h => clashBlocks_nil_of_inflationary pinStep_inflationary h,
   pin_not_cfcs,
   Necessity.reachable_clash_not_iconfluent pinClash⟩

/-- The refutation is not about `totalImpl`: no pin-capable implementation, of
any shape, escapes. -/
example : ∀ impl : Necessity.Impl PinSet Bool,
    Necessity.RunsTo impl emptyPin (pinStep emptyPin true) [true] →
    Necessity.RunsTo impl emptyPin (pinStep emptyPin false) [false] →
    ¬ Necessity.IsCFCS impl pinInv :=
  zero_floor_does_not_imply_cfcs.2

/-! ## §5. The floor family, modally

`Budget` proved "the floor" is not a function: one workload carries
`ForcedFloor _ 1` and `ForcedFloor _ 3`, and *which member you hold* decides the
budget verdict — that asymmetry is `lower_bound_does_not_license_acceptance`.
The modal question is whether the family matters there too. It does not. -/

/-- **Any positive member of the family refutes CFCS.** No supremum is needed and
none is computed: a positive forced floor means *some* carving is nonempty, and
its head block is already a partition scenario.

The hypothesis quantifies over streams from the workload's start because the
carving is existentially bound inside `ForcedFloor` — there is no name for "the
head block" to realize. `totalImpl` discharges it for every stream at once. -/
theorem not_cfcs_of_positive_forcedFloor {S : Type u} {Op : Type w} [MergeState S]
    {wl : Workload S Op} {n : Nat} (hf : ForcedFloor wl n) (hn : 0 < n)
    (impl : Necessity.Impl S Op)
    (hreal : ∀ b : List Op, Realizes impl wl.step wl.start b) :
    ¬ Necessity.IsCFCS impl wl.I := by
  obtain ⟨bs, hcl, _, hlen⟩ := hf
  cases bs with
  | nil => simp at hlen; omega
  | cons b bs' => exact (not_cfcs_of_clashBlock impl (hreal b) hcl).1

/-- The same, at the canonical lift. -/
theorem not_cfcs_of_positive_forcedFloor_total {S : Type u} {Op : Type w}
    [MergeState S] {wl : Workload S Op} {n : Nat} (hf : ForcedFloor wl n)
    (hn : 0 < n) : ¬ Necessity.IsCFCS (totalImpl wl.step) wl.I :=
  not_cfcs_of_positive_forcedFloor hf hn (totalImpl wl.step)
    (fun b => totalImpl_realizes wl.step wl.start b)

/-- The **coarse** floor of `Budget` §6 — the member that is useless for a budget
check, since it fits a budget of 1 that no plan can pay — already refutes
coordination-freedom. -/
theorem budget_coarse_floor_refutes_cfcs :
    ¬ Necessity.IsCFCS (totalImpl budgetWorkload.step) budgetWorkload.I :=
  not_cfcs_of_positive_forcedFloor_total budget_forced_one (by decide)

/-- The **sharp** floor refutes exactly the same proposition. -/
theorem budget_sharp_floor_refutes_cfcs :
    ¬ Necessity.IsCFCS (totalImpl budgetWorkload.step) budgetWorkload.I :=
  not_cfcs_of_positive_forcedFloor_total budget_forced_three (by decide)

/-- ⚠ **The family is quantitatively sharp and modally flat.** Both members are
real forced floors (first conjunct). Quantitatively they are not
interchangeable: only the sharp one refuses every plan at budget 2 (second
conjunct — `Budget.rejected_sound`), and taking the coarse one as "the" floor is
the error `lower_bound_does_not_license_acceptance` punishes. Modally they are
interchangeable: the coarse one already yields the refutation (third conjunct),
and a finer carving cannot refute it harder, because there is nothing stronger
than `¬ IsCFCS` to conclude.

So the answer to "does some carving's positive floor suffice, or do you need the
sup?" is **some suffices** — and the supremum, which `Budget` records as not a
function, is not needed for the modal verdict at all. -/
theorem family_sharp_quantitatively_flat_modally.{v'} :
    (ForcedFloor budgetWorkload 1 ∧ ForcedFloor budgetWorkload 3)
      ∧ (∀ P : Plan.{0, v', 0} budgetWorkload, ¬ (P.cost ≤ 2))
      ∧ ¬ Necessity.IsCFCS (totalImpl budgetWorkload.step) budgetWorkload.I :=
  ⟨⟨budget_forced_one, budget_forced_three⟩,
   rejected_sound budget_forced_three (by decide),
   budget_coarse_floor_refutes_cfcs⟩

/-! ## §6. Where `Cost` DOES refine `Necessity` — the session, not the stream

§4 showed the per-stream floor is blind to a fork. `CoordEffect` composes streams
pointwise and defers minimization; that is exactly the level at which the modal
verdict reappears as a number. -/

/-- **A fork clash charges the pair, under every valid seam.** If both runs cost
zero crossings, both endpoints sit in the start's fiber, hence in each other's —
and a valid seam certifies fibered merges, contradicting the clash. So the *sum*
is positive even though each summand may be zero, which is precisely why §4's
per-stream floor cannot see it.

This generalizes `Cost.no_seam_frees_both` from the pin instance to any two runs
from a common ancestor whose join is illegal. -/
theorem fork_clash_charges_the_pair {S : Type u} {Seg : Type v} {Op : Type w}
    [MergeState S] [DecidableEq Seg] {I : Invariant S} {σ : S → Seg}
    {step : S → Op → S} (hseg : SegmentedIConfluent σ I) {base : S}
    {opsx opsy : List Op}
    (hx : I (Cost.run step base opsx)) (hy : I (Cost.run step base opsy))
    (hbad : ¬ I (Cost.run step base opsx ⊔ Cost.run step base opsy)) :
    0 < Cost.crossings σ step base opsx + Cost.crossings σ step base opsy := by
  by_cases h1 : Cost.crossings σ step base opsx = 0
  · by_cases h2 : Cost.crossings σ step base opsy = 0
    · have e1 := Cost.sigma_const_of_crossings_eq_zero h1
      have e2 := Cost.sigma_const_of_crossings_eq_zero h2
      exact absurd (hseg _ _ (e1.trans e2.symm) hx hy).1 hbad
    · omega
  · omega

/-- The "generalizes" claim above, discharged rather than asserted:
`Cost.no_seam_frees_both` is the pin instance of `fork_clash_charges_the_pair`.
-/
theorem no_seam_frees_both_of_fork_clash {Seg : Type v} [DecidableEq Seg]
    (σ : PinSet → Seg) (hseg : SegmentedIConfluent σ pinInv) :
    ¬ (Cost.crossings σ pinStep emptyPin [true] = 0
        ∧ Cost.crossings σ pinStep emptyPin [false] = 0) := by
  intro ⟨h1, h2⟩
  have h := fork_clash_charges_the_pair (σ := σ) (step := pinStep)
    (base := emptyPin) (opsx := [true]) (opsy := [false])
    hseg (pinInv_pinOne true) (pinInv_pinOne false) pin_join_bad
  omega

/-- **THE COMPOSED BOUND, CONCURRENT FORM.** A reachable clash refutes CFCS and
the lattice judgement (modal), *and* charges at least one crossing to the two
streams together under every valid seam (quantitative) — in the regime where
each stream's own forced floor is zero and §3's bound is silent. -/
theorem reachable_clash_costs_the_session {S : Type u} {Seg : Type v} {Op : Type w}
    [MergeState S] [DecidableEq Seg] {I : Invariant S} {step : S → Op → S}
    (c : Necessity.ReachableClash (totalImpl step) I) {σ : S → Seg}
    (hseg : SegmentedIConfluent σ I) :
    ¬ Necessity.IsCFCS (totalImpl step) I
      ∧ ¬ IConfluent I
      ∧ 0 < Cost.crossings σ step c.base c.opsx
              + Cost.crossings σ step c.base c.opsy := by
  refine ⟨(Necessity.necessity c).1, (Necessity.necessity c).2, ?_⟩
  have ex : Cost.run step c.base c.opsx = c.x := (runsTo_totalImpl_eq c.hx_run).symm
  have ey : Cost.run step c.base c.opsy = c.y := (runsTo_totalImpl_eq c.hy_run).symm
  refine fork_clash_charges_the_pair hseg ?_ ?_ ?_
  · rw [ex]; exact c.hx
  · rw [ey]; exact c.hy
  · rw [ex, ey]; exact c.hbad

/-- **The modal verdict as a session budget.** A reachable clash puts the
composed profile's optimum at ≥ 1 over **every** admissible strategy space, at
every segment type, in every universe. This is the refinement §4 denied at the
stream level, recovered at the session level: `Cost` (through `CoordEffect`) does
bound `Necessity` from below — just not one stream at a time. -/
theorem reachable_clash_floor_le_session_optimum {S : Type u} {Seg : Type v}
    {Op : Type w} [MergeState S] [DecidableEq Seg] {I : Invariant S}
    {step : S → Op → S} (c : Necessity.ReachableClash (totalImpl step) I)
    (A : Admissible (Strategy I Seg)) :
    1 ≤ optimum A (streamProfile (I := I) step c.base c.opsx
                    ⊗ streamProfile (I := I) step c.base c.opsy) := by
  refine le_optimum (fun τ _ => ?_)
  have h := (reachable_clash_costs_the_session c τ.valid).2.2
  show 1 ≤ Cost.crossings τ.seam step c.base c.opsx
            + Cost.crossings τ.seam step c.base c.opsy
  omega

/-- **`CoordEffect`'s strict witness, as a corollary of the modal model.**
`pin_composed_floor_universal` was proved from `Cost.no_seam_frees_both`; here it
falls out of `pinClash` — the same reachable clash that refutes CFCS. The scalar
coordination grade's unsoundness and the impossibility of coordination-freedom
are one fact read in two languages. -/
theorem pin_session_floor_from_the_clash {Seg : Type v} [DecidableEq Seg]
    (A : Admissible (Strategy pinInv Seg)) :
    1 ≤ optimum A (pinTrueProfile ⊗ pinFalseProfile) :=
  reachable_clash_floor_le_session_optimum pinClash A

/-! ## §7. The Live / LatticeOnly axis, priced

`Necessity` demands a *reachable* clash; `CausalReach` supplies the reachability
theory and its dichotomy (tag-scoped rem ⇒ Live, element-wide rem after full
observation ⇒ unreachable). The question this file owes: can a forced floor
charge coordination for a state nothing reaches? -/

/-- **Every state a clash decomposition accuses is occupied by the workload's own
run.** For each block `b` of the carving there is a **prefix** `p` of the stream
such that the accused pair is `(run step s p, run step s (p ++ b))` — both legal,
their merge illegal.

So within the cost model the answer is **no**: a positive forced floor never
charges for an unoccupied state. The one state no execution occupies is the
illegal merge itself, which is what the coordination event exists to prevent. -/
theorem clashBlocks_accuse_only_occupied {S : Type u} {Op : Type w} [MergeState S]
    {I : Invariant S} {step : S → Op → S} :
    ∀ (s : S) (bs : List (List Op)), Cost.ClashBlocks I step s bs →
      ∀ b ∈ bs, ∃ p r : List Op,
        p ++ b ++ r = bs.flatten
          ∧ I (Cost.run step s p)
          ∧ I (Cost.run step s (p ++ b))
          ∧ ¬ I (Cost.run step s p ⊔ Cost.run step s (p ++ b)) := by
  intro s bs
  induction bs generalizing s with
  | nil => intro _ b hb; cases hb
  | cons b0 bs ih =>
      intro h b hb
      have h' : I s ∧ I (Cost.run step s b0) ∧ ¬ I (s ⊔ Cost.run step s b0)
          ∧ Cost.ClashBlocks I step (Cost.run step s b0) bs := h
      rcases List.mem_cons.mp hb with rfl | hb'
      · exact ⟨[], bs.flatten, by simp, h'.1, h'.2.1, h'.2.2.1⟩
      · obtain ⟨p, r, hpr, h1, h2, h3⟩ := ih (Cost.run step s b0) h'.2.2.2 b hb'
        refine ⟨b0 ++ p, r, ?_, ?_, ?_, ?_⟩
        · rw [List.flatten_cons, ← hpr]
          simp [List.append_assoc]
        · rw [Cost.run_append]; exact h1
        · rw [List.append_assoc, Cost.run_append]; exact h2
        · rw [Cost.run_append, List.append_assoc, Cost.run_append]; exact h3

/-- **A valid seam must separate every clash pair — reachable or not.**
`SegmentedIConfluent` quantifies over *all* legal states, so reachability buys a
plan nothing here: an unreachable clash still shrinks the space of admissible
seams, and therefore can raise every *achievable* cost even though it cannot
raise a floor. -/
theorem valid_seam_separates_clash {S : Type u} {Seg : Type v} [MergeState S]
    {I : Invariant S} {σ : S → Seg} (hseg : SegmentedIConfluent σ I) {x y : S}
    (hx : I x) (hy : I y) (hbad : ¬ I (x ⊔ y)) : σ x ≠ σ y :=
  fun he => hbad (hseg x y he hx hy).1

/-! ### The element-wide OR-Set pair, which no cut reaches -/

theorem ew_present_L : Present CausalReach.ewClashL 0 :=
  ⟨1, by decide, by decide⟩

theorem ew_present_R : Present CausalReach.ewClashR 0 :=
  ⟨2, by decide, by decide⟩

/-- The two unreachable states merge to one that holds nothing: tag 1 is tombed
by the right, tag 2 by the left, and no other tag was ever added. -/
theorem ew_merge_not_present :
    ¬ Present (CausalReach.ewClashL ⊔ CausalReach.ewClashR) 0 := by
  intro ⟨t, hadd, htomb⟩
  match t with
  | 0 => simp [CausalReach.ewClashL, CausalReach.ewClashR, gset_mem_merge] at hadd
  | 1 => simp [CausalReach.ewClashL, CausalReach.ewClashR, gset_mem_merge] at htomb
  | 2 => simp [CausalReach.ewClashL, CausalReach.ewClashR, gset_mem_merge] at htomb
  | _ + 3 => simp [CausalReach.ewClashL, CausalReach.ewClashR, gset_mem_merge] at hadd

theorem ew_merge_not_present' :
    ¬ Present (CausalReach.ewClashR ⊔ CausalReach.ewClashL) 0 := by
  rw [merge_comm]
  exact ew_merge_not_present

/-- **A LatticeOnly clash is charged against every plan, though never against a
floor.** No cut of the element-wide history interprets to either state (second
and third conjuncts, `CausalReach`'s own theorems) — and yet every valid seam for
presence must put them in different fibers (first conjunct). Reachability
constrains what a *workload* can occupy; seam validity is a lattice-wide
obligation. The two are charged in different places, and only the first is
visible to `coordination_forced`. -/
theorem latticeOnly_clash_still_separated {Seg : Type v}
    (σ : ORSet Nat Nat → Seg)
    (hseg : SegmentedIConfluent σ (fun s : ORSet Nat Nat => Present s 0)) :
    σ CausalReach.ewClashL ≠ σ CausalReach.ewClashR
      ∧ (¬ ∃ c : CausalReach.Cut CausalReach.ewH,
            CausalReach.ewInterp c = CausalReach.ewClashL)
      ∧ (¬ ∃ c : CausalReach.Cut CausalReach.ewH,
            CausalReach.ewInterp c = CausalReach.ewClashR) :=
  ⟨valid_seam_separates_clash hseg ew_present_L ew_present_R ew_merge_not_present,
   CausalReach.ew_clashL_unreachable, CausalReach.ew_clashR_unreachable⟩

/-- The statement above is not vacuous: instantiated at the always-valid identity
seam it says the two unreachable states differ, which they do. -/
theorem ewClashL_ne_ewClashR : CausalReach.ewClashL ≠ CausalReach.ewClashR :=
  latticeOnly_clash_still_separated id (id_segmented _) |>.1

/-! ### ⚠ …and occupancy is only as sound as `step`

`clashBlocks_accuse_only_occupied` says a floor accuses states the *run* passes
through. But `Cost`'s workload is a **total order of ops with no happens-before
constraint**, while `CausalReach`'s unreachability results are constraints on
`hb`. Whether the states a `step` produces are ones the protocol could produce is
a property of `step` alone — and nothing in `Cost` or `Budget` checks it. -/

/-- A one-op transition that simply moves to the element-wide clash state. It is
a deliberate teleport: the point is that **the theory accepts it**, not that it
models anything. -/
def ewStep (_ : ORSet Nat Nat) (_ : Unit) : ORSet Nat Nat := CausalReach.ewClashL

/-- The carving: one block, whose endpoints are the two states no cut reaches. -/
theorem ew_teleport_clashBlocks :
    Cost.ClashBlocks (fun s : ORSet Nat Nat => Present s 0) ewStep
      CausalReach.ewClashR [[()]] :=
  ⟨ew_present_R, ew_present_L, ew_merge_not_present', trivial⟩

/-- ⚠ **A positive forced floor over a pair no history reaches.** Every valid
seam for presence pays at least one crossing on this workload — a real instance
of `coordination_forced` — and its accused pair is exactly
`CausalReach.ewClashL` / `ewClashR`, which
`orset_reachability_depends_on_remove_shape` proves unreachable under the
element-wide protocol.

The floor is a true theorem about the `step` it was given. The gap is that
`Cost`'s stream model has no `hb`, so it cannot distinguish a `step` the protocol
admits from one it does not; a floor priced against an unfaithful `step` is a
coordination charge for a state nothing reaches. That check is the modeller's,
and it is not in the theory. -/
theorem ew_teleport_floor_is_one :
    ∀ {Seg : Type v} [DecidableEq Seg] (σ : ORSet Nat Nat → Seg),
      SegmentedIConfluent σ (fun s : ORSet Nat Nat => Present s 0) →
      1 ≤ Cost.crossings σ ewStep CausalReach.ewClashR [()] := by
  intro Seg _ σ hseg
  have h := Cost.coordination_forced
    (I := fun s : ORSet Nat Nat => Present s 0) ew_teleport_clashBlocks σ hseg
  simpa using h

/-- Classical decidable equality on OR-Sets. Used only to *instantiate* the
universally-quantified floor above at a concrete seam — never to compute a
crossing count anyone runs. -/
noncomputable def orsetDecEq : DecidableEq (ORSet Nat Nat) :=
  fun a b => Classical.propDecidable (a = b)

/-- **The teleport floor is inhabited, not vacuous.** At the identity seam the
floor of `ew_teleport_floor_is_one` is an actual crossing count, and it is
positive — a coordination event charged against a pair of states no cut of the
element-wide history reaches. -/
theorem ew_teleport_floor_inhabited :
    1 ≤ @Cost.crossings (ORSet Nat Nat) (ORSet Nat Nat) Unit orsetDecEq
          id ewStep CausalReach.ewClashR [()] :=
  @ew_teleport_floor_is_one (ORSet Nat Nat) orsetDecEq id (id_segmented _)

/-- The teleport, as a `Budget` session: the run occupies `ewClashR` then
`ewClashL`, both legal for presence. -/
def ewWorkload : Workload (ORSet Nat Nat) Unit where
  I := fun s => Present s 0
  step := ewStep
  start := CausalReach.ewClashR
  ops := [()]
  legal := ⟨ew_present_R, ew_present_L⟩

/-- …and it carries a genuine `Budget.ForcedFloor` of one. -/
theorem ew_forced_floor_one : ForcedFloor ewWorkload 1 :=
  ⟨[[()]], ew_teleport_clashBlocks, rfl, rfl⟩

/-- ⚠ **THE SHOUT: the checker rejects a session over a pair no history
reaches.** `Budget.rejected_sound` turns the floor above into "no plan fits, in
any universe" at budget 0 — a hard refusal justified entirely by the clash
between `CausalReach.ewClashL` and `ewClashR`, which
`orset_reachability_depends_on_remove_shape` proves unreachable under the
element-wide protocol.

Nothing is wrong with `rejected_sound`: it is a true theorem about the `step` it
was handed. What is missing is any obligation on `Workload.step` to be
protocol-realizable. `RunLegal` checks that the occupied states are **legal**; no
field checks that they are **reachable**, because `Cost`'s stream model has no
happens-before relation to check them against. Reachability lives in
`CausalReach` and is not a hypothesis of any cost result in this tree. -/
theorem ew_rejected_at_zero_over_unreachable_pair.{v'} :
    (∀ P : Plan.{0, v', 0} ewWorkload, ¬ (P.cost ≤ 0))
      ∧ (¬ ∃ c : CausalReach.Cut CausalReach.ewH,
            CausalReach.ewInterp c = CausalReach.ewClashL)
      ∧ (¬ ∃ c : CausalReach.Cut CausalReach.ewH,
            CausalReach.ewInterp c = CausalReach.ewClashR) :=
  ⟨rejected_sound ew_forced_floor_one (by decide),
   CausalReach.ew_clashL_unreachable, CausalReach.ew_clashR_unreachable⟩

/-- The verdict itself, as a term. -/
def ewRejectedAtZero : BudgetVerdict.{0, 0, 0} ewWorkload 0 :=
  .rejected 1 ew_forced_floor_one (by decide)

/-! ## §8. The readings, side by side

The four verdicts this file settles, each a term rather than a slogan. -/

/-- **Composed:** one clash decomposition gives both bounds at once. -/
example : ¬ Necessity.IsCFCS (totalImpl (reallocStep 10)) (BudgetInv 10)
    ∧ ¬ IConfluent (BudgetInv 10)
    ∧ ∀ {Seg : Type} [DecidableEq Seg] (σ : Segmented.QuotaState → Seg),
        SegmentedIConfluent σ (BudgetInv 10) →
        3 ≤ Cost.crossings σ (reallocStep 10) budgetStart budgetW :=
  coordination_necessary_and_costly_total budget_clashBlocks

/-- **Zero does not degenerate:** floor silent, coordination still impossible for
every implementation that can perform the two pins. -/
example : ¬ Necessity.IsCFCS pinImpl pinInv :=
  zero_floor_does_not_imply_cfcs.2 pinImpl
    (totalImpl_realizes pinStep emptyPin [true])
    (totalImpl_realizes pinStep emptyPin [false])

/-- **The family is modally flat:** the coarse floor already refutes. -/
example : ¬ Necessity.IsCFCS (totalImpl budgetWorkload.step) budgetWorkload.I :=
  budget_coarse_floor_refutes_cfcs

/-- **The session sees what the stream cannot:** the pin clash, as a budget. -/
example : 1 ≤ optimum pinSpace (pinTrueProfile ⊗ pinFalseProfile) :=
  pin_session_floor_from_the_clash pinSpace

/-! ### Inhabitation checks — the hypotheses above are occupied -/

/-- `no_clashBlock_of_cfcs`'s hypothesis class is inhabited: `Necessity`'s own
satisfiability witness is a CFCS implementation. So the collapse direction is a
statement about something, not a vacuous implication. -/
example (α : Type) [DecidableEq α] :
    Necessity.IsCFCS (Necessity.gsetAddImpl α) (fun _ : GSet α => True) :=
  Necessity.gset_true_is_cfcs α

/-- `clashBlocks_accuse_only_occupied` on the budget workload: each of its three
re-allocation blocks is accused at a prefix of the stream, with both accused
states on the run. -/
example : ∀ b ∈ budgetBlocks, ∃ p r : List Nat,
    p ++ b ++ r = budgetBlocks.flatten
      ∧ BudgetInv 10 (Cost.run (reallocStep 10) budgetStart p)
      ∧ BudgetInv 10 (Cost.run (reallocStep 10) budgetStart (p ++ b))
      ∧ ¬ BudgetInv 10 (Cost.run (reallocStep 10) budgetStart p
            ⊔ Cost.run (reallocStep 10) budgetStart (p ++ b)) :=
  clashBlocks_accuse_only_occupied budgetStart budgetBlocks budget_clashBlocks

/-- ⚠ **Live and LatticeOnly, priced the same.** The budget workload's floor is
charged against states its own run occupies; the teleport workload's floor is
charged against a pair no cut reaches. Both are `ForcedFloor`s, and no theorem in
`Cost` or `Budget` tells them apart. -/
example : ForcedFloor budgetWorkload 3 ∧ ForcedFloor ewWorkload 1 :=
  ⟨budget_forced_three, ew_forced_floor_one⟩

end Uwueave.Bounds
