/-
# Uwueave.EndpointResidual — endpoint-only finite-run recovery and merge synthesis.

`DeltaRecoveryOn` identifies one admitted operation from one endpoint.  A
finite branch needs more: its endpoint must determine a finite composite effect,
and an endpoint-only residual must be admitted and legal after a canonical
ordering of the sibling endpoints.  `FiniteRunDecoder` and
`EndpointResidualSynthesis` state exactly those two sufficient hypotheses.

The construction below is state-only at merge time.  Lists occur only as the
finite decoded/residual programs returned by the hypotheses; no patch is
carried into `merge3`.
-/
import Uwueave.CompositeDelta

namespace Uwueave.EndpointResidual

open Uwueave Uwueave.Ancestral Uwueave.Necessity
open Uwueave.Recoverable Uwueave.CompositeDelta

universe u v

variable {S : Type u} {Op : Type v}

/-- Endpoint recovery for arbitrary finite runs. Besides reaching the same
endpoint, the selected patch denotes the same total composite effect as every
admitted patch producing that endpoint. The second field is what rules out
cyclic endpoint ambiguity. -/
structure FiniteRunDecoder (g : Guarded S Op) where
  reconstruct : S → S → Patch Op
  endpoint_complete : ∀ (l x : S), Reachable g.impl l x →
    (reconstruct l x).Admitted g l ∧ (reconstruct l x).exec g l = x
  effect_complete : ∀ (l : S) (patch : Patch Op), patch.Admitted g l →
    (reconstruct l (patch.exec g l)).effect g = patch.effect g

/-- The additional endpoint residual law sufficient to synthesize a legal
merge. The tie-break canonically orders both callers' endpoints. For legal,
reachable, non-fast-forward branches the returned finite residual is admitted
after the first ordered endpoint and its result is legal. -/
structure EndpointResidualSynthesis (g : Guarded S Op) (I : Invariant S)
    (tie : TieBreak S) extends FiniteRunDecoder g where
  residual : S → S → S → Patch Op
  residual_admitted : ∀ (l x y : S), I l → I x → I y →
    Reachable g.impl l x → Reachable g.impl l y → x ≠ l → y ≠ l →
    (residual l (tie.pair x y).1 (tie.pair x y).2).Admitted g
      (tie.pair x y).1
  residual_faithful : ∀ (l x y : S), I l → I x → I y →
    Reachable g.impl l x → Reachable g.impl l y → x ≠ l → y ≠ l →
    (residual l (tie.pair x y).1 (tie.pair x y).2).effect g =
      (reconstruct l (tie.pair x y).2).effect g
  residual_legal : ∀ (l x y : S), I l → I x → I y →
    Reachable g.impl l x → Reachable g.impl l y → x ≠ l → y ≠ l →
    I ((residual l (tie.pair x y).1 (tie.pair x y).2).exec g
      (tie.pair x y).1)

/-- The synthesized merge consumes only the ancestor and two endpoints.
Fast-forward is explicit; otherwise both replicas use the same canonical pair
and the same residual program. -/
def mergeEndpoints [DecidableEq S] {g : Guarded S Op} {I : Invariant S}
    {tie : TieBreak S} (E : EndpointResidualSynthesis g I tie)
    (l x y : S) : S :=
  if x = l then y
  else if y = l then x
  else
    (E.residual l (tie.pair x y).1 (tie.pair x y).2).exec g
      (tie.pair x y).1

theorem mergeEndpoints_comm [DecidableEq S] {g : Guarded S Op}
    {I : Invariant S} {tie : TieBreak S}
    (E : EndpointResidualSynthesis g I tie) (l x y : S) :
    mergeEndpoints E l x y = mergeEndpoints E l y x := by
  unfold mergeEndpoints
  by_cases hx : x = l
  · by_cases hy : y = l
    · rw [if_pos hx, if_pos hy, hx, hy]
    · rw [if_pos hx, if_neg hy, if_pos hx]
  · by_cases hy : y = l
    · rw [if_neg hx, if_pos hy, if_pos hy]
    · rw [if_neg hx, if_neg hy, if_neg hy, if_neg hx, tie.pair_comm]

theorem mergeEndpoints_fastforward [DecidableEq S] {g : Guarded S Op}
    {I : Invariant S} {tie : TieBreak S}
    (E : EndpointResidualSynthesis g I tie) (l y : S) :
    mergeEndpoints E l l y = y := by
  simp [mergeEndpoints]

/-- The endpoint-only ancestral merge. -/
def ancestralMerge [DecidableEq S] {g : Guarded S Op} {I : Invariant S}
    {tie : TieBreak S} (E : EndpointResidualSynthesis g I tie) :
    AncestralMerge S where
  merge3 := mergeEndpoints E
  comm := mergeEndpoints_comm E
  fastforward := mergeEndpoints_fastforward E

/-- The selected residual really is a successful finite continuation from the
first canonically ordered endpoint. -/
theorem residual_reachable [DecidableEq S] {g : Guarded S Op}
    {I : Invariant S} {tie : TieBreak S}
    (E : EndpointResidualSynthesis g I tie)
    (l x y : S) (hl : I l) (hx : I x) (hy : I y)
    (hrx : Reachable g.impl l x) (hry : Reachable g.impl l y)
    (hnx : x ≠ l) (hny : y ≠ l) :
    Reachable g.impl (tie.pair x y).1
      ((E.residual l (tie.pair x y).1 (tie.pair x y).2).exec g
        (tie.pair x y).1) := by
  exact ⟨E.residual l (tie.pair x y).1 (tie.pair x y).2,
    Patch.runsTo_of_admitted g _ _
      (E.residual_admitted l x y hl hx hy hrx hry hnx hny)⟩

/-- Away from fast-forward, the synthesized merge is exactly a finite
serialization: replay the endpoint-decoded second branch after the first
canonically ordered endpoint. -/
theorem mergeEndpoints_eq_reconstructed_serialization [DecidableEq S]
    {g : Guarded S Op} {I : Invariant S} {tie : TieBreak S}
    (E : EndpointResidualSynthesis g I tie)
    (l x y : S) (hl : I l) (hx : I x) (hy : I y)
    (hrx : Reachable g.impl l x) (hry : Reachable g.impl l y)
    (hnx : x ≠ l) (hny : y ≠ l) :
    mergeEndpoints E l x y =
      (E.reconstruct l (tie.pair x y).2).exec g (tie.pair x y).1 := by
  unfold mergeEndpoints
  rw [if_neg hnx, if_neg hny]
  exact congrFun (E.residual_faithful l x y hl hx hy hrx hry hnx hny)
    (tie.pair x y).1

/-- The sufficient hypotheses produce a legal merge for all finite reachable
branches, with no `StepGenerated` restriction. -/
theorem ancestralConfluent [DecidableEq S] {g : Guarded S Op}
    {I : Invariant S} {tie : TieBreak S}
    (E : EndpointResidualSynthesis g I tie) :
    AncestralConfluent (ancestralMerge E) g.impl I := by
  intro l x y hl hx hy hrx hry
  show I (mergeEndpoints E l x y)
  unfold mergeEndpoints
  by_cases hxl : x = l
  · rw [if_pos hxl]
    exact hy
  · rw [if_neg hxl]
    by_cases hyl : y = l
    · rw [if_pos hyl]
      exact hx
    · rw [if_neg hyl]
      exact E.residual_legal l x y hl hx hy hrx hry hxl hyl

theorem legal_merge_exists [DecidableEq S] {g : Guarded S Op}
    {I : Invariant S} {tie : TieBreak S}
    (E : EndpointResidualSynthesis g I tie) :
    ∃ M : AncestralMerge S, AncestralConfluent M g.impl I :=
  ⟨ancestralMerge E, ancestralConfluent E⟩

/-! ## Positive multi-step fixture: unbounded increments -/

def incrementOps : Guarded Nat Unit where
  guard := fun _ _ => true
  eff := fun _ state => state + 1

theorem increment_exec (state : Nat) (patch : Patch Unit) :
    patch.exec incrementOps state = state + patch.length := by
  induction patch generalizing state with
  | nil => simp [Patch.exec]
  | cons _ tail ih =>
      change Patch.exec incrementOps (state + 1) tail =
        state + (tail.length + 1)
      rw [ih]
      omega

theorem increment_admitted (state : Nat) (patch : Patch Unit) :
    patch.Admitted incrementOps state := by
  induction patch generalizing state with
  | nil => trivial
  | cons _ tail ih => exact ⟨rfl, ih (state + 1)⟩

theorem increment_reachable_le {l x : Nat} :
    Reachable incrementOps.impl l x → l ≤ x := by
  rintro ⟨patch, hrun⟩
  have hend := (Patch.admitted_of_runsTo incrementOps l x patch hrun).2
  rw [increment_exec] at hend
  omega

def incrementDecoder : FiniteRunDecoder incrementOps where
  reconstruct l x := List.replicate (x - l) ()
  endpoint_complete := by
    intro l x hreachable
    have hle := increment_reachable_le hreachable
    refine ⟨increment_admitted _ _, ?_⟩
    rw [increment_exec, List.length_replicate]
    omega
  effect_complete := by
    intro l patch _
    funext state
    simp only [Patch.effect, increment_exec, List.length_replicate]
    omega

theorem natTie_pair_ordered (x y : Nat) :
    (natTie.pair x y).1 ≤ (natTie.pair x y).2 := by
  unfold natTie TieBreak.ofKey TieBreak.pair
  by_cases hxy : x ≤ y
  · rw [if_pos (decide_eq_true hxy)]
    exact hxy
  · rw [if_neg (by simpa using hxy)]
    omega

def incrementEndpointSynthesis :
    EndpointResidualSynthesis incrementOps (fun _ => True) natTie where
  toFiniteRunDecoder := incrementDecoder
  residual := fun ancestor _ second => List.replicate (second - ancestor) ()
  residual_admitted := by
    intro _ _ _ _ _ _ _ _ _ _
    exact increment_admitted _ _
  residual_faithful := by
    intro l x y _ _ _ _ _ _ _
    funext state
    simp [Patch.effect, increment_exec, incrementDecoder]
  residual_legal := by
    intros
    trivial

theorem increment_multi_step_fixture :
    Reachable incrementOps.impl 0 2 ∧
    Reachable incrementOps.impl 0 3 ∧
    (ancestralMerge incrementEndpointSynthesis).merge3 0 2 3 = 5 ∧
    (incrementEndpointSynthesis.residual 0
      (natTie.pair 2 3).1 (natTie.pair 2 3).2).length = 3 := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · refine ⟨[(), ()], ?_⟩
    simpa [increment_exec] using
      Patch.runsTo_of_admitted incrementOps 0 [(), ()]
        (increment_admitted 0 [(), ()])
  · refine ⟨[(), (), ()], ?_⟩
    simpa [increment_exec] using
      Patch.runsTo_of_admitted incrementOps 0 [(), (), ()]
        (increment_admitted 0 [(), (), ()])

theorem increment_all_finite_runs_merge_legally :
    AncestralConfluent (ancestralMerge incrementEndpointSynthesis)
      incrementOps.impl (fun _ => True) :=
  ancestralConfluent incrementEndpointSynthesis

/-! ## `DeltaRecoveryOn` is insufficient for finite endpoint recovery -/

/-- A fixed point at `0` and a two-cycle between `1` and `2`. -/
def twist (state : Nat) : Nat :=
  if state = 1 then 2 else if state = 2 then 1 else state

def cyclicOps : Guarded Nat Unit where
  guard := fun _ _ => true
  eff := fun _ => twist

/-- One-step recovery is easy because there is only one operation. -/
def cyclicDeltaRecoveryOn : DeltaRecoveryOn cyclicOps where
  recover := fun _ _ => twist
  spec := by intros; rfl

theorem cyclic_one_and_two_steps_same_endpoint :
    (Patch.exec cyclicOps 0 [()] = 0) ∧
    (Patch.exec cyclicOps 0 [(), ()] = 0) := by
  decide

theorem cyclic_one_and_two_steps_different_effect :
    (Patch.effect cyclicOps [()] 1 = 2) ∧
    (Patch.effect cyclicOps [(), ()] 1 = 1) := by
  decide

/-- The required separation: admitted one- and two-step runs have the same
endpoints at `0` but different composite effects elsewhere. Hence no endpoint
decoder can satisfy finite-run effect completeness, even though
`DeltaRecoveryOn` exists. -/
theorem deltaRecoveryOn_insufficient_for_finite_runs :
    Nonempty (DeltaRecoveryOn cyclicOps) ∧
      ¬ Nonempty (FiniteRunDecoder cyclicOps) := by
  refine ⟨⟨cyclicDeltaRecoveryOn⟩, ?_⟩
  rintro ⟨decoder⟩
  have hone := decoder.effect_complete 0 [()]
    (by simp [Patch.Admitted, cyclicOps])
  have htwo := decoder.effect_complete 0 [(), ()]
    (by simp [Patch.Admitted, cyclicOps])
  have hendOne : Patch.exec cyclicOps 0 [()] = 0 :=
    cyclic_one_and_two_steps_same_endpoint.1
  have hendTwo : Patch.exec cyclicOps 0 [(), ()] = 0 :=
    cyclic_one_and_two_steps_same_endpoint.2
  rw [hendOne] at hone
  rw [hendTwo] at htwo
  have heffects : Patch.effect cyclicOps [()] =
      Patch.effect cyclicOps [(), ()] :=
    hone.symm.trans htwo
  have hatOne := congrFun heffects 1
  have hbad : (2 : Nat) = 1 :=
    cyclic_one_and_two_steps_different_effect.1.symm.trans
      (hatOne.trans cyclic_one_and_two_steps_different_effect.2)
  omega

end Uwueave.EndpointResidual
