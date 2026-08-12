/-
# Uwueave.Specification — histories with arbitrary refined outcomes.

`IConfluent` classifies a predicate on a mergeable state.  That is the exact
answer when a history has only one observable outcome: legal or illegal.  A
language specification usually has a wider codomain.  One execution can permit
several renderings, schedules, repairs, return values, or externally visible
traces, and one such outcome can be a more precise implementation of another.

This module is the first outcome-valued rung.  A `Specification H O` is the set
of outcomes admitted at each execution/history `H`; `OutcomePreorder O` declares
which outcomes refine which.  Its algebraic coordination-free judgement says
that any outcomes independently admitted at two histories have a common
refinement admitted after the histories merge.

The main result is the exact decomposition

    coordination-free  ↔  history-monotone ∧ fiber-directed

for total specifications.  Totality is used only from left to right, when an
arbitrary extension must supply a second outcome.  The converse needs no
totality.  `invariant_coordinationFree_iff` then recovers this repository's
`IConfluent` judgement exactly by taking the outcome type to be `Unit` with
equality refinement.

The boundaries are proved rather than left in prose:

* the empty specification is vacuously coordination-free but not non-vacuous;
* a total, refinement-closed, history-monotone specification with two
  incompatible Boolean outcomes is not coordination-free, so monotonicity
  alone cannot replace fiber directedness;
* the grow-set invariant "zero is absent" is I-confluent but its singleton-
  outcome specification is not history-monotone.  `IConfluent` asks about the
  merge of two *legal* histories, while history monotonicity asks about every
  extension, including illegal ones.

⟨TERMINAL⟩ This is an algebraic compatibility judgement over a supplied history
join.  It does not model operation reachability, network liveness, observation
equivalence, or the existence of a distributed implementation.  Those require
the additional hypotheses carried by `Necessity`, `CausalReach`, and the history
modules; no modal implementation claim is manufactured here.

⟨DONE for typed snapshot expressions; still open for general histories⟩
`Preo.DerivedProgram.Program.specification` now quotes an intrinsically typed
`Preo.Expr` evaluation into `Specification` and proves totality.  It deliberately
does not manufacture a refinement relation or a coordination-free verdict.
Operation/history syntax beyond one typed environment evaluation remains a
separate language problem.
-/
import Uwueave.Catalog

namespace Uwueave.Specification

open Uwueave Uwueave.Catalog

universe u v

/-! ## §1. Outcome refinement and specifications -/

/-- A declared refinement preorder on outcomes.  `refines concrete abstract`
means that `concrete` makes at least the commitments made by `abstract`.
Antisymmetry is deliberately absent: observationally equivalent outcomes may
refine one another without being definitionally equal. -/
structure OutcomePreorder (O : Type v) where
  /-- The refinement relation, oriented concrete-to-abstract. -/
  refines : O → O → Prop
  /-- Every outcome refines itself. -/
  refl : ∀ o, refines o o
  /-- Refinement composes. -/
  trans : ∀ {a b c}, refines a b → refines b c → refines a c

/-- A specification maps each execution/history to its set of admitted
outcomes.  Sets are predicates so the definition needs no external library. -/
abbrev Specification (H : Type u) (O : Type v) := H → O → Prop

/-- Implementation specification `P` refines contract `Q` when each outcome
admitted by `P` refines some outcome admitted by `Q`, at the same history. -/
def SpecRefines {H : Type u} {O : Type v} (R : OutcomePreorder O)
    (P Q : Specification H O) : Prop :=
  ∀ h o, P h o → ∃ q, Q h q ∧ R.refines o q

/-- Specification refinement is reflexive. -/
theorem specRefines_refl {H : Type u} {O : Type v} (R : OutcomePreorder O)
    (P : Specification H O) : SpecRefines R P P := by
  intro h o ho
  exact ⟨o, ho, R.refl o⟩

/-- Specification refinement is transitive. -/
theorem specRefines_trans {H : Type u} {O : Type v} {R : OutcomePreorder O}
    {P Q T : Specification H O}
    (hPQ : SpecRefines R P Q) (hQT : SpecRefines R Q T) :
    SpecRefines R P T := by
  intro h o ho
  obtain ⟨q, hq, hoq⟩ := hPQ h o ho
  obtain ⟨t, ht, hqt⟩ := hQT h q hq
  exact ⟨t, ht, R.trans hoq hqt⟩

/-- Admissibility is closed under making an outcome more precise.  This is a
useful property, but it is not baked into `Specification`: a policy may admit
an abstract answer while forbidding a more revealing one. -/
def RefinementClosed {H : Type u} {O : Type v} (R : OutcomePreorder O)
    (P : Specification H O) : Prop :=
  ∀ h o o', P h o → R.refines o' o → P h o'

/-- Every history admits at least one outcome.  This rules out vacuous safety
obtained by specifying no behavior. -/
def Total {H : Type u} {O : Type v} (P : Specification H O) : Prop :=
  ∀ h, ∃ o, P h o

/-- At least one history/outcome pair is admitted.  `Total` is stronger; this
weaker predicate is useful for stating the minimum non-vacuity bar. -/
def Nonvacuous {H : Type u} {O : Type v} (P : Specification H O) : Prop :=
  ∃ h o, P h o

/-- A total specification is non-vacuous when there is at least one history. -/
theorem Total.nonvacuous {H : Type u} {O : Type v} {P : Specification H O}
    (ht : Total P) (h : H) : Nonvacuous P := by
  obtain ⟨o, ho⟩ := ht h
  exact ⟨h, o, ho⟩

/-! ## §2. The two ingredients of outcome coordination-freedom -/

/-- **History monotonicity.** Extending a history never strands an admitted
outcome: the extension admits some refinement of it.  The extension order is
the order induced by the history join. -/
def HistoryMonotone {H : Type u} {O : Type v} [MergeState H]
    (R : OutcomePreorder O) (P : Specification H O) : Prop :=
  ∀ h k o, h ⊑ k → P h o → ∃ o', P k o' ∧ R.refines o' o

/-- **Fiber directedness.** Any two outcomes admitted at one history have a
common admitted refinement.  This is the compatibility condition that plain
history monotonicity does not express. -/
def FiberDirected {H : Type u} {O : Type v} (R : OutcomePreorder O)
    (P : Specification H O) : Prop :=
  ∀ h a b, P h a → P h b →
    ∃ c, P h c ∧ R.refines c a ∧ R.refines c b

/-- **Outcome-valued coordination-freedom.** Independently admitted outcomes
remain jointly implementable after their histories merge: the merged history
admits a common refinement of both.

This is an algebraic judgement only.  In particular, the name does not assert
operation reachability, availability, convergence in time, or an implementation
existence theorem. -/
def CoordinationFree {H : Type u} {O : Type v} [MergeState H]
    (R : OutcomePreorder O) (P : Specification H O) : Prop :=
  ∀ h k a b, P h a → P k b →
    ∃ c, P (h ⊔ k) c ∧ R.refines c a ∧ R.refines c b

/-- Binary coordination-freedom forces every outcome fiber to be directed.
This direction needs no totality because both inputs are already supplied. -/
theorem coordinationFree_fiberDirected {H : Type u} {O : Type v}
    [MergeState H] {R : OutcomePreorder O} {P : Specification H O}
    (hcf : CoordinationFree R P) : FiberDirected R P := by
  intro h a b ha hb
  obtain ⟨c, hc, hca, hcb⟩ := hcf h h a b ha hb
  exact ⟨c, by simpa only [merge_idem] using hc, hca, hcb⟩

/-- A total coordination-free specification is monotone along every history
extension.  Totality supplies an outcome at the larger history with which the
smaller history's outcome can be reconciled. -/
theorem coordinationFree_historyMonotone {H : Type u} {O : Type v}
    [MergeState H] {R : OutcomePreorder O} {P : Specification H O}
    (ht : Total P) (hcf : CoordinationFree R P) : HistoryMonotone R P := by
  intro h k o hle ho
  obtain ⟨ok, hok⟩ := ht k
  obtain ⟨c, hc, hco, _⟩ := hcf h k o ok ho hok
  change h ⊔ k = k at hle
  rw [hle] at hc
  exact ⟨c, hc, hco⟩

/-- History monotonicity and directed outcome fibers are sufficient for binary
coordination-freedom.  The two outcomes first transport to the merged history;
directedness reconciles them there. -/
theorem historyMonotone_and_fiberDirected_coordinationFree
    {H : Type u} {O : Type v} [MergeState H]
    {R : OutcomePreorder O} {P : Specification H O}
    (hm : HistoryMonotone R P) (hd : FiberDirected R P) :
    CoordinationFree R P := by
  intro h k a b ha hb
  obtain ⟨a', ha', hara⟩ := hm h (h ⊔ k) a (le_merge_left h k) ha
  obtain ⟨b', hb', hbrb⟩ := hm k (h ⊔ k) b (le_merge_right h k) hb
  obtain ⟨c, hc, hca', hcb'⟩ := hd (h ⊔ k) a' b' ha' hb'
  exact ⟨c, hc, R.trans hca' hara, R.trans hcb' hbrb⟩

/-- **Exact decomposition for total specifications.** Coordination-freedom is
history monotonicity plus directed compatibility of each outcome fiber. -/
theorem coordinationFree_iff_historyMonotone_and_fiberDirected
    {H : Type u} {O : Type v} [MergeState H]
    {R : OutcomePreorder O} {P : Specification H O} (ht : Total P) :
    CoordinationFree R P ↔ HistoryMonotone R P ∧ FiberDirected R P := by
  constructor
  · intro hcf
    exact ⟨coordinationFree_historyMonotone ht hcf,
      coordinationFree_fiberDirected hcf⟩
  · intro h
    exact historyMonotone_and_fiberDirected_coordinationFree h.1 h.2

/-! ## §3. The exact `IConfluent` instance -/

/-- Equality is the discrete refinement preorder. -/
def equalityRefinement (O : Type v) : OutcomePreorder O where
  refines := Eq
  refl := Eq.refl
  trans := Eq.trans

/-- Turn an invariant into a singleton-outcome specification.  The outcome has
no information; admissibility is exactly legality of the history state. -/
def invariantSpec {S : Type u} (I : Invariant S) : Specification S Unit :=
  fun s _ => I s

/-- **Exact bridge.** The existing lattice `IConfluent` story is precisely the
singleton-outcome instance of outcome-valued coordination-freedom.  Neither
direction needs reachability or totality. -/
theorem invariant_coordinationFree_iff {S : Type u} [MergeState S]
    (I : Invariant S) :
    CoordinationFree (equalityRefinement Unit) (invariantSpec I) ↔
      IConfluent I := by
  constructor
  · intro hcf x y hx hy
    obtain ⟨_, hxy, _, _⟩ := hcf x y () () hx hy
    exact hxy
  · intro hic x y _ _ hx hy
    exact ⟨(), hic x y hx hy, rfl, rfl⟩

/-- Upward closure asks legality to survive every extension, even an extension
that was not itself legal.  This is strictly stronger than I-confluence. -/
def UpwardClosed {S : Type u} [MergeState S] (I : Invariant S) : Prop :=
  ∀ x y, x ⊑ y → I x → I y

/-- For singleton outcomes, history monotonicity is exactly upward closure of
the invariant, not I-confluence. -/
theorem invariant_historyMonotone_iff {S : Type u} [MergeState S]
    (I : Invariant S) :
    HistoryMonotone (equalityRefinement Unit) (invariantSpec I) ↔
      UpwardClosed I := by
  constructor
  · intro hm x y hxy hx
    obtain ⟨_, hy, _⟩ := hm x y () hxy hx
    exact hy
  · intro hup x y _ hxy hx
    exact ⟨(), hup x y hxy hx, rfl⟩

/-- Singleton outcome fibers are always directed.  Consequently all of the
substance of their binary judgement lies in legality after merging histories. -/
theorem invariant_fiberDirected {S : Type u} (I : Invariant S) :
    FiberDirected (equalityRefinement Unit) (invariantSpec I) := by
  intro h _ _ hh _
  exact ⟨(), hh, rfl, rfl⟩

/-! ## §4. A genuinely outcome-valued positive model -/

/-- Grow-set outcomes refine one another by containing no more observations:
the concrete outcome may reveal a subset of what the abstract one reveals. -/
def subsetRefinement (α : Type) : OutcomePreorder (GSet α) where
  refines a b := ∀ x, a x = true → b x = true
  refl _ _ hx := hx
  trans hab hbc x hx := hbc x (hab x hx)

/-- A history admits every grow-set observation contained in it. -/
def observationSpec (α : Type) : Specification (GSet α) (GSet α) :=
  fun history outcome => ∀ x, outcome x = true → history x = true

/-- Observation specifications are total: revealing nothing is always an
admitted outcome. -/
theorem observationSpec_total (α : Type) : Total (observationSpec α) := by
  intro _
  exact ⟨fun _ => false, by intro x hx; simp at hx⟩

/-- Observation admissibility is closed under revealing less. -/
theorem observationSpec_refinementClosed (α : Type) :
    RefinementClosed (subsetRefinement α) (observationSpec α) := by
  intro h o o' ho href x hx
  exact ho x (href x hx)

/-- **Nontrivial arbitrary-outcome instance.** Intersecting two observations is
a common refinement, and anything observed on the left already survives the
merged history. -/
theorem observationSpec_coordinationFree (α : Type) :
    CoordinationFree (subsetRefinement α) (observationSpec α) := by
  intro h k a b ha hb
  refine ⟨fun x => a x && b x, ?_, ?_, ?_⟩
  · intro x hx
    have hx' : a x = true ∧ b x = true := by simpa using hx
    rw [gset_mem_merge]
    simp [ha x hx'.1]
  · intro x hx
    have hx' : a x = true ∧ b x = true := by simpa using hx
    exact hx'.1
  · intro x hx
    have hx' : a x = true ∧ b x = true := by simpa using hx
    exact hx'.2

/-- The positive model meets the strong non-vacuity bar at every history. -/
theorem observationSpec_nonvacuous (α : Type) (h : GSet α) :
    Nonvacuous (observationSpec α) :=
  (observationSpec_total α).nonvacuous h

/-! ## §5. Concrete boundaries and refutations -/

/-- The one-point history lattice used by the outcome-compatibility examples. -/
instance instMergeStateUnitHistory : MergeState Unit where
  merge _ _ := ()
  merge_comm _ _ := rfl
  merge_assoc _ _ _ := rfl
  merge_idem _ := rfl

/-- The empty specification admits no behavior. -/
def emptySpec : Specification Unit Bool := fun _ _ => False

/-- **Vacuity witness.** With no admitted input outcomes, the binary judgement
holds without proving any behavior possible. -/
theorem emptySpec_coordinationFree :
    CoordinationFree (equalityRefinement Bool) emptySpec := by
  intro _ _ _ _ ha _
  exact False.elim ha

/-- The vacuity witness fails even the weakest non-vacuity requirement. -/
theorem emptySpec_not_nonvacuous : ¬ Nonvacuous emptySpec := by
  intro h
  obtain ⟨_, _, hfalse⟩ := h
  exact hfalse

/-- Both Boolean outcomes are admitted at the sole history. -/
def branchingBoolSpec : Specification Unit Bool := fun _ _ => True

/-- The incompatible Boolean specification is total. -/
theorem branchingBoolSpec_total : Total branchingBoolSpec := by
  intro _
  exact ⟨false, trivial⟩

/-- It is also refinement-closed under equality. -/
theorem branchingBoolSpec_refinementClosed :
    RefinementClosed (equalityRefinement Bool) branchingBoolSpec := by
  intro _ _ _ _ _
  trivial

/-- It is history-monotone: the only history extension changes nothing. -/
theorem branchingBoolSpec_historyMonotone :
    HistoryMonotone (equalityRefinement Bool) branchingBoolSpec := by
  intro _ _ o _ _
  exact ⟨o, trivial, rfl⟩

/-- **Monotonicity is not coordination-freedom.** `true` and `false` are both
locally admitted but have no common equality refinement.  This remains a
counterexample even though the specification is total and refinement-closed. -/
theorem branchingBoolSpec_not_coordinationFree :
    ¬ CoordinationFree (equalityRefinement Bool) branchingBoolSpec := by
  intro hcf
  obtain ⟨o, _, hot, hof⟩ := hcf () () true false trivial trivial
  have htf : true = false := hot.symm.trans hof
  exact Bool.noConfusion htf

/-- Empty grow-set history. -/
def emptyNatSet : GSet Nat := fun _ => false

/-- The grow-set history containing exactly zero. -/
def zeroNatSet : GSet Nat := fun n => n == 0

/-- The empty history extends to the history containing zero. -/
theorem emptyNatSet_le_zeroNatSet : emptyNatSet ⊑ zeroNatSet := by
  change (fun n => emptyNatSet n || zeroNatSet n) = zeroNatSet
  funext n
  simp [emptyNatSet]

/-- The empty history satisfies "zero is absent". -/
theorem emptyNatSet_zero_absent : emptyNatSet 0 = false := rfl

/-- The extended history does not satisfy "zero is absent". -/
theorem zeroNatSet_zero_present : zeroNatSet 0 = true := by decide

/-- The invariant "zero is absent" is I-confluent: union cannot introduce zero
when neither input contains it. -/
theorem zeroAbsent_iconfluent :
    IConfluent (S := GSet Nat) (fun s => s 0 = false) :=
  gset_notmem_iconfluent 0

/-- **I-confluence does not imply history monotonicity.** Extending the empty
grow-set with zero is an illegal extension.  I-confluence never promised to
preserve invariants against merging with an illegal state. -/
theorem zeroAbsent_not_historyMonotone :
    ¬ HistoryMonotone (equalityRefinement Unit)
      (invariantSpec (S := GSet Nat) (fun s => s 0 = false)) := by
  intro hm
  obtain ⟨_, hbad, _⟩ := hm emptyNatSet zeroNatSet ()
    emptyNatSet_le_zeroNatSet emptyNatSet_zero_absent
  change zeroNatSet 0 = false at hbad
  rw [zeroNatSet_zero_present] at hbad
  exact Bool.noConfusion hbad

end Uwueave.Specification
