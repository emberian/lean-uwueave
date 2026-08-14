/-
# Uwueave.GluingExtensions — keyed holes, a computed dual H¹, and fill provenance.

This module implements the three extensions deliberately left outside
`Gluing`.  They remain separate constructions: a keyed family reports a
verdict for each named hole; the finite Boolean triangle computes an actual
cohomology relation rather than renaming divergence; and provenanced fills
record which authors survive in a glue.
-/
import Uwueave.Gluing

namespace Uwueave.GluingExtensions

open Uwueave Uwueave.Catalog Uwueave.Gluing

universe u v

/-! ## 1. Keyed hole families -/

/-- A document-level family of independently named guarded holes. -/
abbrev KeyedFamily (K : Type v) (S : Type u) [MergeState S] :=
  K → GuardedHole S

/-- A verdict is retained at every key; evidence is not collapsed to one
document-wide Boolean. -/
abbrev KeyedVerdicts {K : Type v} {S : Type u} [MergeState S]
    (family : KeyedFamily K S) :=
  ∀ key, HoleVerdict (family key)

/-- Every pointwise-spanning family has a pointwise-total verdict family. -/
noncomputable def keyedVerdictsOfSpanning {K : Type v} {S : Type u}
    [MergeState S] (family : KeyedFamily K S)
    (spanning : ∀ key, Spanning (family key)) : KeyedVerdicts family :=
  fun key => Classical.choice (holeVerdict_total (family key) (spanning key))

/-- Two concrete keys with different answers. -/
def exampleFamily : KeyedFamily Bool (GSet Nat)
  | false => anchorHole
  | true => exclusiveHole

def exampleVerdicts : KeyedVerdicts exampleFamily
  | false => anchorVerdict
  | true => exclusiveVerdict

theorem example_anchor_is_glued :
    HoleVerdict.isGlued (exampleVerdicts false) = true := rfl

theorem example_exclusive_is_clash :
    HoleVerdict.isGlued (exampleVerdicts true) = false := rfl

/-! ## 2. A finite dual-H¹ computation

The complex is the boundary of a triangle with coefficients in `Bool`, viewed
as F₂. A 0-cochain is a vertex labelling; its coboundary records the xor across
each edge. Two 1-cochains are cohomologous exactly when they differ by one of
the eight enumerated coboundaries. The xor around the cycle is the computed
H¹ class. -/

structure TriangleGauge where
  v0 : Bool
  v1 : Bool
  v2 : Bool
deriving DecidableEq

structure TriangleCochain where
  e01 : Bool
  e12 : Bool
  e20 : Bool
deriving DecidableEq

/-- All finite 0-cochains, explicitly. -/
def triangleGauges : List TriangleGauge :=
  [ { v0 := false, v1 := false, v2 := false }
  , { v0 := false, v1 := false, v2 := true }
  , { v0 := false, v1 := true,  v2 := false }
  , { v0 := false, v1 := true,  v2 := true }
  , { v0 := true,  v1 := false, v2 := false }
  , { v0 := true,  v1 := false, v2 := true }
  , { v0 := true,  v1 := true,  v2 := false }
  , { v0 := true,  v1 := true,  v2 := true } ]

def TriangleCochain.add (left right : TriangleCochain) : TriangleCochain where
  e01 := left.e01 ^^ right.e01
  e12 := left.e12 ^^ right.e12
  e20 := left.e20 ^^ right.e20

/-- The genuine degree-zero coboundary on the triangle. -/
def coboundary (gauge : TriangleGauge) : TriangleCochain where
  e01 := gauge.v0 ^^ gauge.v1
  e12 := gauge.v1 ^^ gauge.v2
  e20 := gauge.v2 ^^ gauge.v0

/-- Gauge orbit of a 1-cochain. -/
def gaugeOrbit (cochain : TriangleCochain) : List TriangleCochain :=
  triangleGauges.map fun gauge => cochain.add (coboundary gauge)

/-- Equality in the finite H¹ quotient. -/
def Cohomologous (left right : TriangleCochain) : Prop :=
  right ∈ gaugeOrbit left

instance (left right : TriangleCochain) : Decidable (Cohomologous left right) :=
  inferInstanceAs (Decidable (right ∈ gaugeOrbit left))

/-- Holonomy is the dual H¹ classifier. -/
def dualH1 (cochain : TriangleCochain) : Bool :=
  cochain.e01 ^^ cochain.e12 ^^ cochain.e20

theorem coboundary_dualH1_zero (gauge : TriangleGauge) :
    dualH1 (coboundary gauge) = false := by
  cases gauge with
  | mk v0 v1 v2 => cases v0 <;> cases v1 <;> cases v2 <;> decide

/-- The computation: the quotient has exactly the two Boolean holonomy
classes. This is an iff over the enumerated coboundary action. -/
theorem cohomologous_iff_dualH1_eq (left right : TriangleCochain) :
    Cohomologous left right ↔ dualH1 left = dualH1 right := by
  cases left with
  | mk l01 l12 l20 =>
      cases right with
      | mk r01 r12 r20 =>
          cases l01 <;> cases l12 <;> cases l20 <;>
            cases r01 <;> cases r12 <;> cases r20 <;> decide

def trivialCochain : TriangleCochain := ⟨false, false, false⟩
def obstructedCochain : TriangleCochain := ⟨true, false, false⟩

theorem trivial_dualH1 : dualH1 trivialCochain = false := rfl
theorem obstructed_dualH1 : dualH1 obstructedCochain = true := rfl

theorem two_distinct_dualH1_classes :
    ¬ Cohomologous trivialCochain obstructedCochain := by
  rw [cohomologous_iff_dualH1_eq]
  decide

/-! ## 3. Fill-provenance semantics -/

/-- A fill contribution carries its author separately from its state patch. -/
structure ProvenancedFill (Actor : Type v) (S : Type u) where
  author : Actor
  patch : S

def authorSet {Actor : Type v} [DecidableEq Actor] (author : Actor) : GSet Actor :=
  fun candidate => decide (candidate = author)

/-- Apply a contribution while retaining its author as monotone provenance. -/
def applyProvenanced {Actor : Type v} [DecidableEq Actor]
    {S : Type u} [MergeState S] (base : S) (fill : ProvenancedFill Actor S) :
    S × GSet Actor :=
  (base ⊔ fill.patch, authorSet fill.author)

/-- Glue two independently applied contributions. -/
def glueProvenanced {Actor : Type v} [DecidableEq Actor]
    {S : Type u} [MergeState S] (leftBase rightBase : S)
    (left right : ProvenancedFill Actor S) : S × GSet Actor :=
  applyProvenanced leftBase left ⊔ applyProvenanced rightBase right

theorem glueProvenanced_state {Actor : Type v} [DecidableEq Actor]
    {S : Type u} [MergeState S] (leftBase rightBase : S)
    (left right : ProvenancedFill Actor S) :
    (glueProvenanced leftBase rightBase left right).1 =
      (leftBase ⊔ left.patch) ⊔ (rightBase ⊔ right.patch) := rfl

theorem glueProvenanced_observes_left {Actor : Type v} [DecidableEq Actor]
    {S : Type u} [MergeState S] (leftBase rightBase : S)
    (left right : ProvenancedFill Actor S) :
    (glueProvenanced leftBase rightBase left right).2 left.author = true := by
  change (decide (left.author = left.author) ||
    decide (left.author = right.author)) = true
  simp

theorem glueProvenanced_observes_right {Actor : Type v} [DecidableEq Actor]
    {S : Type u} [MergeState S] (leftBase rightBase : S)
    (left right : ProvenancedFill Actor S) :
    (glueProvenanced leftBase rightBase left right).2 right.author = true := by
  change (decide (right.author = left.author) ||
    decide (right.author = right.author)) = true
  simp

theorem glueProvenanced_excludes_stranger {Actor : Type v} [DecidableEq Actor]
    {S : Type u} [MergeState S] (leftBase rightBase : S)
    (left right : ProvenancedFill Actor S) (stranger : Actor)
    (hneLeft : stranger ≠ left.author) (hneRight : stranger ≠ right.author) :
    (glueProvenanced leftBase rightBase left right).2 stranger = false := by
  change (decide (stranger = left.author) ||
    decide (stranger = right.author)) = false
  simp [hneLeft, hneRight]

/-- Provenance does not weaken the original gluing guard: its state projection
is exactly the original glue. -/
theorem glueProvenanced_guard {S : Type u} [MergeState S]
    (h : GuardedHole S) (hg : Glues h)
    {Actor : Type v} [DecidableEq Actor]
    {x y : S} {left right : ProvenancedFill Actor S}
    (hleft : h.Admissible x left.patch)
    (hright : h.Admissible y right.patch)
    (hdiv : Divergent (x ⊔ left.patch) (y ⊔ right.patch)) :
    h.guard (glueProvenanced x y left right).1 := by
  rw [glueProvenanced_state]
  exact hg x left.patch y right.patch hleft hright hdiv

def aliceFill : ProvenancedFill (Fin 3) (GSet Nat) :=
  ⟨0, gsetOf [0]⟩

def bobFill : ProvenancedFill (Fin 3) (GSet Nat) :=
  ⟨1, gsetOf [2]⟩

theorem two_authors_and_no_stranger :
    (glueProvenanced (gsetOf []) (gsetOf []) aliceFill bobFill).2 0 = true ∧
    (glueProvenanced (gsetOf []) (gsetOf []) aliceFill bobFill).2 1 = true ∧
    (glueProvenanced (gsetOf []) (gsetOf []) aliceFill bobFill).2 2 = false := by
  decide

end Uwueave.GluingExtensions
