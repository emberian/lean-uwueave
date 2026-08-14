/-
# Uwueave.FiniteCertificateClassifier -- exact certificates on an explicit scope

`CertificateScope.Residual` is deliberately semantic: its future carrier may
be infinite and neither residual equality nor key sufficiency need be
decidable.  This file supplies the finite counterpart without weakening that
boundary.  A caller gives the complete list of worlds it intends to inspect.
The compiler enumerates the residual image inside exactly that list and checks
every equal-key pair in exactly that list.

The word "finite" is load-bearing.  `sufficientB_eq_true_iff` is an exact iff
for `SufficientKeyWithin`, not for carrier-wide `SufficientKey`.  The global
bridge needs carrier coverage.  Endpoint coverage alone supports the narrower
bridge for a fixed residual pair; full carrier coverage implies it.  The final
Bool fixture shows why some coverage premise is indispensable: a singleton
scope can accept a constant key while that key remains globally insufficient.

No completeness of a deployment inventory, persistence of the inventory, or
authenticity of its members is claimed here.
-/
import Uwueave.CertificateScope

namespace Uwueave.FiniteCertificateClassifier

open Uwueave.CertificateScope

universe u v w

/-! ## 1. Exact residual enumeration -/

/-- A finite residual specification.  `worlds` is data supplied by the caller,
not an assertion that the list covers the carrier or any future relation. -/
structure Spec (W : Type u) (R : Type v) where
  worlds : List W
  eval : W → R
  future : W → W → Prop
  futureDecidable : ∀ w t, Decidable (future w t)

attribute [instance] Spec.futureDecidable

/-- The semantic residual restricted to the explicitly enumerated worlds. -/
def ResidualWithin {W : Type u} {R : Type v} (spec : Spec W R)
    (w : W) (r : R) : Prop :=
  ∃ t ∈ spec.worlds, spec.future w t ∧ spec.eval t = r

/-- The residual image, with duplicates removed.  Its order is the first
occurrence order of `spec.worlds`; no hash or quotient representation is used. -/
def Spec.residualResults {W : Type u} {R : Type v} [BEq R] [LawfulBEq R]
    (spec : Spec W R) (w : W) : List R :=
  ((spec.worlds.filter fun t => decide (spec.future w t)).map spec.eval).eraseDups

/-- **Exact residual enumeration.** Membership in the computed list is iff the
restricted semantic residual, including both the scope and future premises. -/
theorem mem_residualResults_iff {W : Type u} {R : Type v}
    [BEq R] [LawfulBEq R] (spec : Spec W R) (w : W) (r : R) :
    r ∈ spec.residualResults w ↔ ResidualWithin spec w r := by
  simp [Spec.residualResults, ResidualWithin, and_assoc]

/-- Equality of finite residuals in pointwise semantic form. -/
def ResidualEqWithin {W : Type u} {R : Type v} (spec : Spec W R)
    (x y : W) : Prop :=
  ∀ r, ResidualWithin spec x r ↔ ResidualWithin spec y r

/-- Executable equality of residual *sets*.  Comparing the result lists
directly would be too strong: two origins may encounter the same result set in
different enumeration orders. -/
def Spec.residualEqB {W : Type u} {R : Type v} [BEq R] [LawfulBEq R]
    (spec : Spec W R) (x y : W) : Bool :=
  (spec.residualResults x).all (spec.residualResults y).contains &&
    (spec.residualResults y).all (spec.residualResults x).contains

/-- Boolean residual equality is exact for the pointwise scoped relation. -/
theorem residualEqB_eq_true_iff {W : Type u} {R : Type v}
    [BEq R] [LawfulBEq R] (spec : Spec W R) (x y : W) :
    spec.residualEqB x y = true ↔ ResidualEqWithin spec x y := by
  simp only [Spec.residualEqB, Bool.and_eq_true, List.all_eq_true,
    List.contains_iff_mem]
  constructor
  · rintro ⟨hxy, hyx⟩ r
    rw [← mem_residualResults_iff spec x r,
      ← mem_residualResults_iff spec y r]
    exact ⟨hxy r, hyx r⟩
  · intro h
    constructor
    · intro r hr
      exact (mem_residualResults_iff spec y r).mpr
        ((h r).mp ((mem_residualResults_iff spec x r).mp hr))
    · intro r hr
      exact (mem_residualResults_iff spec x r).mpr
        ((h r).mpr ((mem_residualResults_iff spec y r).mp hr))

/-! ## 2. Exact finite key-sufficiency classifier -/

/-- A key is sufficient **within this enumerated scope** when every enumerated
equal-key pair has equal residuals relative to the same enumerated scope. -/
def Spec.SufficientKeyWithin {W : Type u} {R : Type v} (spec : Spec W R)
    {K : Type w} (key : W → K) : Prop :=
  ∀ x ∈ spec.worlds, ∀ y ∈ spec.worlds,
    key x = key y → ResidualEqWithin spec x y

/-- Executable all-pairs classifier for `SufficientKeyWithin`.  The quadratic
pair scan is intentional and visible; residual construction itself scans the
world list once for each endpoint. -/
def Spec.sufficientB {W : Type u} {R : Type v} [BEq R] [LawfulBEq R]
    (spec : Spec W R) {K : Type w} [BEq K] (key : W → K) : Bool :=
  spec.worlds.all fun x =>
    spec.worlds.all fun y =>
      if key x == key y then spec.residualEqB x y
      else true

/-- **Classifier exactness.** The Boolean says true iff the scoped semantic
key-sufficiency proposition says true. -/
theorem sufficientB_eq_true_iff {W : Type u} {R : Type v}
    [BEq R] [LawfulBEq R] (spec : Spec W R)
    {K : Type w} [BEq K] [LawfulBEq K] (key : W → K) :
    spec.sufficientB key = true ↔ spec.SufficientKeyWithin key := by
  simp only [Spec.sufficientB, List.all_eq_true, beq_iff_eq]
  constructor
  · intro h x hx y hy hkey
    have hpair := h x hx y hy
    simp [hkey] at hpair
    exact (residualEqB_eq_true_iff spec x y).mp hpair
  · intro h x hx y hy
    by_cases hkey : key x = key y
    · simp [hkey, (residualEqB_eq_true_iff spec x y).mpr (h x hx y hy hkey)]
    · simp [hkey]

/-! ## 3. Coverage is the only bridge to the global residual -/

/-- Every carrier world is present as an origin in the finite scope.  This is
possible only for a genuinely finite/enumerated carrier and is never inferred
from the list itself. -/
def Spec.CoversOrigins {W : Type u} {R : Type v} (spec : Spec W R) : Prop :=
  ∀ w, w ∈ spec.worlds

/-- Every semantic future endpoint is present in the finite scope. -/
def Spec.CoversFutures {W : Type u} {R : Type v} (spec : Spec W R) : Prop :=
  ∀ w t, spec.future w t → t ∈ spec.worlds

/-- Full carrier coverage automatically covers every future endpoint.  The two
premises are intentionally not presented as independent obligations. -/
theorem coversFutures_of_coversOrigins {W : Type u} {R : Type v}
    (spec : Spec W R) (coverage : spec.CoversOrigins) :
    spec.CoversFutures :=
  fun _ t _ => coverage t

/-- Under endpoint coverage, the finite residual and the global residual are
pointwise identical at any origin. -/
theorem residualWithin_iff_residual_of_coverage {W : Type u} {R : Type v}
    (spec : Spec W R) (coverage : spec.CoversFutures) (w : W) (r : R) :
    ResidualWithin spec w r ↔ Residual spec.eval spec.future w r := by
  constructor
  · rintro ⟨t, _, ht, rfl⟩
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨t, coverage w t ht, ht, rfl⟩

/-- A scoped residual equality transports to the global residual only when
future coverage is supplied. -/
theorem residualEq_of_within_of_coverage {W : Type u} {R : Type v}
    (spec : Spec W R) (coverage : spec.CoversFutures) {x y : W}
    (h : ResidualEqWithin spec x y) :
    ResidualEq spec.eval spec.future x y := by
  intro r
  rw [← residualWithin_iff_residual_of_coverage spec coverage x r,
    ← residualWithin_iff_residual_of_coverage spec coverage y r]
  exact h r

/-- **Honest global bridge.** A finite acceptance result yields carrier-wide
`SufficientKey` only with explicit coverage of the whole carrier.  That one
premise supplies both the key-pair origins and their future endpoints. -/
theorem sufficientKey_of_within_of_coverage {W : Type u} {R : Type v}
    (spec : Spec W R) {K : Type w} (key : W → K)
    (coverage : spec.CoversOrigins)
    (h : spec.SufficientKeyWithin key) :
    SufficientKey key spec.eval spec.future := by
  intro x y hkey
  exact residualEq_of_within_of_coverage spec
    (coversFutures_of_coversOrigins spec coverage)
    (h x (coverage x) y (coverage y) hkey)

/-! ## 4. Singleton scopes do not imply global sufficiency -/

private def boolEqFuture (x y : Bool) : Prop := x = y

private instance (x y : Bool) : Decidable (boolEqFuture x y) :=
  inferInstanceAs (Decidable (x = y))

private def singletonSpec : Spec Bool Bool where
  worlds := [false]
  eval := id
  future := boolEqFuture
  futureDecidable := fun _ _ => inferInstance

private def constantKey (_ : Bool) : Unit := ()

/-- **Finite-local does not imply global.** The singleton scope accepts a
constant key exactly, yet the omitted `true` world has a different global
residual.  Coverage, not optimism, is what licenses §3's bridge. -/
theorem singleton_scope_cannot_prove_global :
    singletonSpec.sufficientB constantKey = true ∧
      ¬ SufficientKey constantKey id boolEqFuture := by
  constructor
  · decide
  · intro h
    have hres := h false true rfl false
    have hleft : Residual id boolEqFuture false false :=
      ⟨false, rfl, rfl⟩
    obtain ⟨t, ht, heval⟩ := (hres.mp hleft)
    exact Bool.noConfusion (ht.trans heval)

end Uwueave.FiniteCertificateClassifier
