/-
# Uwueave.StatusEffects — six-status effects, inferred over finite reach

`ResultStatus.Capability` is intentionally small: three independent flags and
a hand-written admission table.  That was enough to separate declarations from
evaluations, but it loses correlations.  In particular, “may produce a closed
fork” and “may produce an open fork” cannot be stated separately.

This module supplies the promised replacement without changing that historical
API.  It erases a value-carrying status to one of six `Shape`s, orders those
shapes by refinement, and defines an effect as a downward-closed set of shapes.
Downsets have honest bottom, top, meet and join operations; no nonexistent join
is invented on the six shapes themselves.

The second half closes the other explicit boundary in `RenderSix`: its original
soundness contract constrains only `exact`, `absent`, and `pending`.  `TotalSoundEvaluator6`
adds exact evidence/settledness clauses for `provisional`, `forkedClosed`, and
`forkedOpen`, projects back to the original contract, and is inhabited by
`ResultStatus.statusOf`.  The fixtures end with a one-cell liar that satisfies
the old contract and is rejected by the total one.

No hidden resolution bit appears in the query surface.  A descriptor carries
either `preserveFork` or a named policy term, so selection remains visible in
the operation that requests it.
-/
import Uwueave.RenderSix

namespace Uwueave.StatusEffects

open Uwueave Uwueave.Catalog
open Uwueave.ResultStatus (Status statusOf)

/-! ## 1. The refinement basis -/

/-- The value-erased shape of the full six-status result space. -/
inductive Shape where
  | exact
  | provisional
  | forkedClosed
  | forkedOpen
  | absent
  | pending
  deriving DecidableEq, Repr

/-- Erase only the payload; no status cell is folded into another. -/
def shapeOf {α : Type} : Status α → Shape
  | .exact _ => .exact
  | .provisional _ => .provisional
  | .forkedClosed => .forkedClosed
  | .forkedOpen => .forkedOpen
  | .absent => .absent
  | .pending => .pending

/-- `a ⊑ b` means that `a` is a refinement of the effectful shape `b`.

`exact` is the pure successful result.  Opening a result or changing its
plurality adds an effect.  Thus the two open corners retain both closed and
open refinements, while `pending` and `forkedOpen` remain incomparable. -/
def Refines : Shape → Shape → Prop
  | .exact, _ => True
  | .provisional, .provisional => True
  | .provisional, .pending => True
  | .provisional, .forkedOpen => True
  | .forkedClosed, .forkedClosed => True
  | .forkedClosed, .forkedOpen => True
  | .forkedOpen, .forkedOpen => True
  | .absent, .absent => True
  | .absent, .pending => True
  | .pending, .pending => True
  | _, _ => False

infix:50 " ⊑ₛ " => Refines

theorem refines_refl (a : Shape) : a ⊑ₛ a := by
  cases a <;> trivial

theorem refines_trans {a b c : Shape} (hab : a ⊑ₛ b) (hbc : b ⊑ₛ c) :
    a ⊑ₛ c := by
  cases a <;> cases b <;> cases c <;> simp_all [Refines]

theorem refines_antisymm {a b : Shape} (hab : a ⊑ₛ b) (hba : b ⊑ₛ a) :
    a = b := by
  cases a <;> cases b <;> simp_all [Refines]

/-! ## 2. Capabilities are downsets, and downsets form a lattice -/

/-- A six-status effect is exactly a downward-closed set of status shapes. -/
structure Effect where
  Allows : Shape → Prop
  downward : ∀ {a b}, a ⊑ₛ b → Allows b → Allows a

/-- Effect subsumption is set inclusion. -/
def Effect.LE (a b : Effect) : Prop := ∀ sh, a.Allows sh → b.Allows sh

infix:50 " ⊑ₑ " => Effect.LE

theorem Effect.le_refl (a : Effect) : a ⊑ₑ a := fun _ h => h

theorem Effect.le_trans {a b c : Effect} (hab : a ⊑ₑ b) (hbc : b ⊑ₑ c) :
    a ⊑ₑ c := fun sh h => hbc sh (hab sh h)

theorem Effect.ext {a b : Effect} (h : ∀ sh, a.Allows sh ↔ b.Allows sh) : a = b := by
  cases a with
  | mk aa ad =>
      cases b with
      | mk ba bd =>
          have hf : aa = ba := funext fun sh => propext (h sh)
          subst ba
          rfl

theorem Effect.le_antisymm {a b : Effect} (hab : a ⊑ₑ b) (hba : b ⊑ₑ a) :
    a = b :=
  Effect.ext (fun sh => ⟨hab sh, hba sh⟩)

/-- The impossible effect. -/
def bottom : Effect where
  Allows := fun _ => False
  downward := fun _ h => False.elim h

/-- The unconstrained effect. -/
def top : Effect where
  Allows := fun _ => True
  downward := fun _ _ => True.intro

/-- Conjunction is the meet of two downsets. -/
def meet (a b : Effect) : Effect where
  Allows := fun sh => a.Allows sh ∧ b.Allows sh
  downward := fun h hab => ⟨a.downward h hab.1, b.downward h hab.2⟩

/-- Union is the join of two downsets.  Correlations are retained: no
component-wise Boolean widening occurs. -/
def join (a b : Effect) : Effect where
  Allows := fun sh => a.Allows sh ∨ b.Allows sh
  downward := fun h hab => hab.elim (fun ha => Or.inl (a.downward h ha))
    (fun hb => Or.inr (b.downward h hb))

theorem bottom_le (a : Effect) : bottom ⊑ₑ a := fun _ h => False.elim h
theorem le_top (a : Effect) : a ⊑ₑ top := fun _ _ => True.intro
theorem meet_le_left (a b : Effect) : meet a b ⊑ₑ a := fun _ h => h.1
theorem meet_le_right (a b : Effect) : meet a b ⊑ₑ b := fun _ h => h.2
theorem le_meet {a b c : Effect} (hab : a ⊑ₑ b) (hac : a ⊑ₑ c) :
    a ⊑ₑ meet b c := fun sh h => ⟨hab sh h, hac sh h⟩
theorem le_join_left (a b : Effect) : a ⊑ₑ join a b := fun _ h => Or.inl h
theorem le_join_right (a b : Effect) : b ⊑ₑ join a b := fun _ h => Or.inr h
theorem join_le {a b c : Effect} (hac : a ⊑ₑ c) (hbc : b ⊑ₑ c) :
    join a b ⊑ₑ c := fun sh h => h.elim (hac sh) (hbc sh)

/-- The downset operations are distributive; this is the lattice law the base
six-point preorder itself cannot honestly provide. -/
theorem meet_join_distrib (a b c : Effect) :
    meet a (join b c) = join (meet a b) (meet a c) := by
  apply Effect.ext
  intro sh
  constructor
  · rintro ⟨ha, hb | hc⟩
    · exact Or.inl ⟨ha, hb⟩
    · exact Or.inr ⟨ha, hc⟩
  · rintro (⟨ha, hb⟩ | ⟨ha, hc⟩)
    · exact ⟨ha, Or.inl hb⟩
    · exact ⟨ha, Or.inr hc⟩

/-! ### Exact adapter from the historical flags -/

/-- The historical admission table, factored through a six-way shape. -/
def legacyAllows (c : ResultStatus.Capability) : Shape → Prop
  | .exact => True
  | .provisional => c.mayOpen = true
  | .forkedClosed => c.mayFork = true
  | .forkedOpen => c.mayFork = true ∧ c.mayOpen = true
  | .absent => c.mayBeEmpty = true
  | .pending => c.mayBeEmpty = true ∧ c.mayOpen = true

/-- Every old three-flag capability embeds as a downset. -/
def fromLegacy (c : ResultStatus.Capability) : Effect where
  Allows := legacyAllows c
  downward := by
    intro a b hab hb
    cases a <;> cases b <;> simp_all [Refines, legacyAllows]

/-- The adapter is exact on every value-carrying status, not merely sound in
one direction. -/
theorem fromLegacy_matches {α : Type} (c : ResultStatus.Capability)
    (st : Status α) :
    (fromLegacy c).Allows (shapeOf st) ↔ c.Admits st := by
  cases st <;> simp [fromLegacy, legacyAllows, shapeOf, ResultStatus.Capability.Admits]

/-! ## 3. Least inference over an explicit finite reach -/

/-- An evaluator is supported when every status observed in the supplied finite
reach is admitted by the effect. -/
def Supports {S β : Type} (eff : Effect) (reach : List S)
    (peval : S → Status β) : Prop :=
  ∀ s, s ∈ reach → eff.Allows (shapeOf (peval s))

/-- The least effect supported by a finite reach: the downward closure of the
shapes actually observed there. -/
def infer {S β : Type} (reach : List S) (peval : S → Status β) : Effect where
  Allows := fun sh => ∃ s, s ∈ reach ∧ sh ⊑ₛ shapeOf (peval s)
  downward := fun h ⟨s, hs, hshape⟩ => ⟨s, hs, refines_trans h hshape⟩

theorem infer_sound {S β : Type} (reach : List S) (peval : S → Status β) :
    Supports (infer reach peval) reach peval := by
  intro s hs
  exact ⟨s, hs, refines_refl _⟩

theorem infer_least {S β : Type} {reach : List S} {peval : S → Status β}
    {eff : Effect} (h : Supports eff reach peval) : infer reach peval ⊑ₑ eff := by
  rintro sh ⟨s, hs, href⟩
  exact eff.downward href (h s hs)

/-- The inference theorem packages both obligations expected of a language
elaborator: the returned effect checks, and every other checking effect
subsumes it. -/
theorem infer_is_least {S β : Type} (reach : List S) (peval : S → Status β) :
    Supports (infer reach peval) reach peval
      ∧ ∀ eff, Supports eff reach peval → infer reach peval ⊑ₑ eff :=
  ⟨infer_sound reach peval, fun _ => infer_least⟩

/-! ## 4. Query descriptors retain resolution as syntax -/

/-- Fork handling is not a Boolean.  Either alternatives remain visible, or a
named policy term is retained in the descriptor. -/
inductive Resolution (S β : Type) where
  | preserveFork
  | byPolicy (name : String) (policy : S → Option β)

/-- An operation/query descriptor owns the evaluator, its answer relation, and
the explicit resolution decision. -/
structure QueryDescriptor (S β : Type) where
  answer : S → GSet β
  evaluate : S → Status β
  resolution : Resolution S β

/-- Inferred capability of a described query on a concrete finite reach. -/
def QueryDescriptor.inferOn {S β : Type} (q : QueryDescriptor S β)
    (reach : List S) : Effect := infer reach q.evaluate

/-! ## 5. Total soundness for all six cells -/

/-- At least two distinct answers are present. -/
def HasFork {S β : Type} (answer : S → GSet β) (s : S) : Prop :=
  ∃ a b, answer s a = true ∧ answer s b = true ∧ a ≠ b

/-- The six-cell extension of `RenderSix.SoundEvaluator6`.  `Settled` is a
named proposition supplied by the query model; it is never inferred from a
hidden flag. -/
structure TotalSoundEvaluator6 {S β : Type} (F : Evidence.Future S)
    (answer : S → GSet β) (Settled : S → Prop) (peval : S → Status β) : Prop where
  core : RenderSix.SoundEvaluator6 F answer peval
  exact_settled : ∀ s v, peval s = Status.exact v → Settled s
  provisional_correct : ∀ s v, peval s = Status.provisional v →
    answer s v = true ∧ Holes.SealsTo (answer s) v ∧ ¬ Settled s
  forkedClosed_correct : ∀ s, peval s = Status.forkedClosed →
    HasFork answer s ∧ Settled s
  forkedOpen_correct : ∀ s, peval s = Status.forkedOpen →
    HasFork answer s ∧ ¬ Settled s
  absent_settled : ∀ s, peval s = Status.absent → Settled s
  pending_open : ∀ s, peval s = Status.pending → ¬ Settled s

/-- Exact projection back to the historical three-cell contract. -/
theorem TotalSoundEvaluator6.toSoundEvaluator6 {S β : Type} {F : Evidence.Future S}
    {answer : S → GSet β} {Settled : S → Prop} {peval : S → Status β}
    (h : TotalSoundEvaluator6 F answer Settled peval) :
    RenderSix.SoundEvaluator6 F answer peval := h.core

/-! ### The three missing inversions, now stated exactly -/

theorem values_of_statusOf_provisional {β : Type}
    {e : Evidence.ResultEvidence β} {v : β}
    (h : statusOf e = Status.provisional v) :
    Evidence.values e v = true ∧ Holes.SealsTo (Evidence.values e) v
      ∧ ¬ Evidence.Closed e := by
  by_cases hu : ∃ a, Evidence.values e a = true ∧
      ∀ b, Evidence.values e b = true → b = a
  · by_cases hc : Evidence.Closed e
    · rw [ResultStatus.statusOf, dif_pos hu, if_pos hc] at h
      exact absurd h (ResultStatus.status_ne_of_tag (by simp [ResultStatus.statusTag]))
    · rw [ResultStatus.statusOf, dif_pos hu, if_neg hc] at h
      injection h with hv
      obtain ⟨hm, hs⟩ := Classical.choose_spec hu
      exact ⟨hv ▸ hm, fun b hb => hv ▸ hs b hb, hc⟩
  · by_cases hne : ∃ a, Evidence.values e a = true
    · by_cases hc : Evidence.Closed e
      · rw [ResultStatus.statusOf, dif_neg hu, if_pos hne, if_pos hc] at h
        exact absurd h (ResultStatus.status_ne_of_tag (by simp [ResultStatus.statusTag]))
      · rw [ResultStatus.statusOf, dif_neg hu, if_pos hne, if_neg hc] at h
        exact absurd h (ResultStatus.status_ne_of_tag (by simp [ResultStatus.statusTag]))
    · by_cases hc : Evidence.Closed e
      · rw [ResultStatus.statusOf, dif_neg hu, if_neg hne, if_pos hc] at h
        exact absurd h (ResultStatus.status_ne_of_tag (by simp [ResultStatus.statusTag]))
      · rw [ResultStatus.statusOf, dif_neg hu, if_neg hne, if_neg hc] at h
        exact absurd h (ResultStatus.status_ne_of_tag (by simp [ResultStatus.statusTag]))

/-- Non-uniqueness plus a witness produces two distinct witnesses. -/
theorem two_of_nonunique {β : Type} {p : β → Bool}
    (hne : ∃ a, p a = true)
    (hnu : ¬ ∃ a, p a = true ∧ ∀ b, p b = true → b = a) :
    ∃ a b, p a = true ∧ p b = true ∧ a ≠ b := by
  obtain ⟨a, ha⟩ := hne
  have hex : ∃ b, p b = true ∧ b ≠ a := by
    apply Classical.byContradiction
    intro hn
    apply hnu
    refine ⟨a, ha, ?_⟩
    intro b hb
    apply Classical.byContradiction
    intro hba
    exact hn ⟨b, hb, hba⟩
  obtain ⟨b, hb, hba⟩ := hex
  exact ⟨a, b, ha, hb, fun hab => hba hab.symm⟩

theorem values_of_statusOf_forkedClosed {β : Type}
    {e : Evidence.ResultEvidence β} (h : statusOf e = Status.forkedClosed) :
    HasFork Evidence.values e ∧ Evidence.Closed e := by
  by_cases hu : ∃ a, Evidence.values e a = true ∧
      ∀ b, Evidence.values e b = true → b = a
  · by_cases hc : Evidence.Closed e
    · rw [ResultStatus.statusOf, dif_pos hu, if_pos hc] at h
      exact absurd h (ResultStatus.status_ne_of_tag (by simp [ResultStatus.statusTag]))
    · rw [ResultStatus.statusOf, dif_pos hu, if_neg hc] at h
      exact absurd h (ResultStatus.status_ne_of_tag (by simp [ResultStatus.statusTag]))
  · by_cases hne : ∃ a, Evidence.values e a = true
    · by_cases hc : Evidence.Closed e
      · exact ⟨two_of_nonunique hne hu, hc⟩
      · rw [ResultStatus.statusOf, dif_neg hu, if_pos hne, if_neg hc] at h
        exact absurd h (ResultStatus.status_ne_of_tag (by simp [ResultStatus.statusTag]))
    · by_cases hc : Evidence.Closed e
      · rw [ResultStatus.statusOf, dif_neg hu, if_neg hne, if_pos hc] at h
        exact absurd h (ResultStatus.status_ne_of_tag (by simp [ResultStatus.statusTag]))
      · rw [ResultStatus.statusOf, dif_neg hu, if_neg hne, if_neg hc] at h
        exact absurd h (ResultStatus.status_ne_of_tag (by simp [ResultStatus.statusTag]))

theorem values_of_statusOf_forkedOpen {β : Type}
    {e : Evidence.ResultEvidence β} (h : statusOf e = Status.forkedOpen) :
    HasFork Evidence.values e ∧ ¬ Evidence.Closed e := by
  by_cases hu : ∃ a, Evidence.values e a = true ∧
      ∀ b, Evidence.values e b = true → b = a
  · by_cases hc : Evidence.Closed e
    · rw [ResultStatus.statusOf, dif_pos hu, if_pos hc] at h
      exact absurd h (ResultStatus.status_ne_of_tag (by simp [ResultStatus.statusTag]))
    · rw [ResultStatus.statusOf, dif_pos hu, if_neg hc] at h
      exact absurd h (ResultStatus.status_ne_of_tag (by simp [ResultStatus.statusTag]))
  · by_cases hne : ∃ a, Evidence.values e a = true
    · by_cases hc : Evidence.Closed e
      · rw [ResultStatus.statusOf, dif_neg hu, if_pos hne, if_pos hc] at h
        exact absurd h (ResultStatus.status_ne_of_tag (by simp [ResultStatus.statusTag]))
      · exact ⟨two_of_nonunique hne hu, hc⟩
    · by_cases hc : Evidence.Closed e
      · rw [ResultStatus.statusOf, dif_neg hu, if_neg hne, if_pos hc] at h
        exact absurd h (ResultStatus.status_ne_of_tag (by simp [ResultStatus.statusTag]))
      · rw [ResultStatus.statusOf, dif_neg hu, if_neg hne, if_neg hc] at h
        exact absurd h (ResultStatus.status_ne_of_tag (by simp [ResultStatus.statusTag]))

/-- `statusOf` discharges the total contract; the three new clauses come from
the exact inversions immediately above, not from assumptions about a renderer. -/
theorem statusOf_totalSound6 {β : Type} [DecidableEq β] [Inhabited β] :
    TotalSoundEvaluator6 (Evidence.SealedFuture (α := β)) Evidence.values
      Evidence.Closed statusOf where
  core := RenderSix.statusOf_sound6
  exact_settled := fun _ _ h => (RenderSix.values_of_statusOf_exact h).2.2
  provisional_correct := fun _ _ h => values_of_statusOf_provisional h
  forkedClosed_correct := fun _ h => values_of_statusOf_forkedClosed h
  forkedOpen_correct := fun _ h => values_of_statusOf_forkedOpen h
  absent_settled := fun _ h => (RenderSix.values_of_statusOf_absent h).2
  pending_open := fun _ h => (RenderSix.values_of_statusOf_pending h).2

/-! ## 6. Fixtures: correlations, explicit resolution, and a rejected lie -/

abbrev EState := Evidence.ResultEvidence Holes.Val

noncomputable def provisionalEffect : Effect :=
  infer [Evidence.openW] (statusOf : EState → Status Holes.Val)

noncomputable def forkedClosedEffect : Effect :=
  infer [Evidence.forkedClosedW] (statusOf : EState → Status Holes.Val)

noncomputable def forkedOpenEffect : Effect :=
  infer [Evidence.forkedOpenW] (statusOf : EState → Status Holes.Val)

/-- The three cells that the old flags correlated only accidentally now infer
three distinct capabilities. -/
theorem inferred_effects_distinguish_the_missing_cells :
    provisionalEffect.Allows .provisional
      ∧ ¬ provisionalEffect.Allows .forkedClosed
      ∧ forkedClosedEffect.Allows .forkedClosed
      ∧ ¬ forkedClosedEffect.Allows .provisional
      ∧ forkedOpenEffect.Allows .forkedOpen
      ∧ forkedOpenEffect.Allows .provisional
      ∧ forkedOpenEffect.Allows .forkedClosed := by
  simp [provisionalEffect, forkedClosedEffect, forkedOpenEffect, infer,
    ResultStatus.statusOf_openW, ResultStatus.statusOf_forkedClosedW,
    ResultStatus.statusOf_forkedOpenW, shapeOf, Refines]

/-- This correlation is the concrete expressiveness gain: single answers may
remain provisional and forks may occur, but every fork must already be closed. -/
noncomputable def openSinglesClosedForks : Effect :=
  join provisionalEffect forkedClosedEffect

theorem correlated_effect_excludes_open_fork :
    openSinglesClosedForks.Allows .provisional
      ∧ openSinglesClosedForks.Allows .forkedClosed
      ∧ ¬ openSinglesClosedForks.Allows .forkedOpen := by
  simp [openSinglesClosedForks, join, provisionalEffect, forkedClosedEffect,
    infer, ResultStatus.statusOf_openW, ResultStatus.statusOf_forkedClosedW,
    shapeOf, Refines]

/-- No assignment of the three independent flags denotes that correlated
effect: provisional forces `mayOpen`, a closed fork forces `mayFork`, and the
old table then admits an open fork. -/
theorem correlated_effect_has_no_legacy_encoding :
    ¬ ∃ c : ResultStatus.Capability,
      ∀ sh, (fromLegacy c).Allows sh ↔ openSinglesClosedForks.Allows sh := by
  rintro ⟨c, hc⟩
  have hp : c.mayOpen = true := by
    have h := (hc Shape.provisional).mpr correlated_effect_excludes_open_fork.1
    exact h
  have hf : c.mayFork = true := by
    have h := (hc Shape.forkedClosed).mpr correlated_effect_excludes_open_fork.2.1
    exact h
  have hfo : openSinglesClosedForks.Allows Shape.forkedOpen :=
    (hc Shape.forkedOpen).mp ⟨hf, hp⟩
  exact correlated_effect_excludes_open_fork.2.2 hfo

noncomputable def exposedForkQuery : QueryDescriptor EState Holes.Val where
  answer := Evidence.values
  evaluate := statusOf
  resolution := .preserveFork

noncomputable def aliceResolvedQuery : QueryDescriptor EState Holes.Val where
  answer := Evidence.values
  evaluate := statusOf
  resolution := .byPolicy "by-source/alice" (ResultStatus.bySource Evidence.alice)

/-- Resolution constructors are observably different; no Boolean default can
silently turn the exposing query into the selecting query. -/
theorem explicit_resolution_is_load_bearing :
    exposedForkQuery.resolution ≠ aliceResolvedQuery.resolution := by
  intro h
  cases h

/-- A one-cell state space used to exhibit the exact gap between the two
contracts. -/
inductive One where | state

def oneFuture : Evidence.Future One := fun _ _ => True
noncomputable def oneAnswer : One → GSet Holes.Val :=
  fun _ => Evidence.values Evidence.forkedClosedW

/-- The liar reports `forkedOpen` over evidence that is in fact a closed fork. -/
def closedForkAsOpen : One → Status Holes.Val := fun _ => Status.forkedOpen

/-- The historical contract has no fork clause, so the lie inhabits it. -/
theorem closedForkAsOpen_old_sound :
    RenderSix.SoundEvaluator6 oneFuture oneAnswer closedForkAsOpen where
  exact_correct := by intros; contradiction
  exact_final := by intros; contradiction
  absent_correct := by intros; contradiction
  absent_final := by intros; contradiction
  pending_escapable := by intros; contradiction

/-- The total contract rejects that evaluator in exactly the false open cell. -/
theorem closedForkAsOpen_not_total :
    ¬ TotalSoundEvaluator6 oneFuture oneAnswer (fun _ => True) closedForkAsOpen := by
  intro h
  exact (h.forkedOpen_correct One.state rfl).2 True.intro

/-- Exact adapter summary: inference is least, `statusOf` satisfies all six
clauses, the total contract projects to `SoundEvaluator6`, and the old contract
alone admits the closed/open-fork lie. -/
theorem six_status_marker_closure :
    Supports provisionalEffect [Evidence.openW]
        (statusOf : EState → Status Holes.Val)
      ∧ TotalSoundEvaluator6 (Evidence.SealedFuture (α := Holes.Val))
          Evidence.values Evidence.Closed statusOf
      ∧ RenderSix.SoundEvaluator6 (Evidence.SealedFuture (α := Holes.Val))
          Evidence.values statusOf
      ∧ RenderSix.SoundEvaluator6 oneFuture oneAnswer closedForkAsOpen
      ∧ ¬ TotalSoundEvaluator6 oneFuture oneAnswer (fun _ => True) closedForkAsOpen :=
  ⟨infer_sound _ _, statusOf_totalSound6,
   statusOf_totalSound6.toSoundEvaluator6, closedForkAsOpen_old_sound,
   closedForkAsOpen_not_total⟩

end Uwueave.StatusEffects
