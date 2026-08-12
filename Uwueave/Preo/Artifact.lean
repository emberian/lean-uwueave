/-
# Uwueave.Preo.Artifact — checked origins and a neutral first-order boundary

The public umbrella preserves the original Artifact API. ArtifactData is the
minimal data-only leaf; ArtifactChecked supplies the one-way proof-indexed
constructors; ArtifactDiagnostics retains the existing Repr instances. The
closed examples remain here so existing imports and declaration names do not
change.
-/
import Uwueave.Preo.ArtifactData
import Uwueave.Preo.ArtifactChecked
import Uwueave.Preo.ArtifactDiagnostics

namespace Uwueave.Preo.Artifact

open Uwueave

set_option autoImplicit false

universe u

/-! ## §6. Non-vacuous closed examples -/

namespace Examples

def natCodec : FirstOrderCodec Nat where
  encode value := [value]
  decode
    | [value] => some value
    | _ => none
  decode_encode := by intro value; rfl

def declaration : CheckedDeclaration Nat :=
  CheckedDeclaration.ofState ⟨100⟩ 200 1

def field : CheckedField Nat :=
  CheckedField.ofCarrier declaration ⟨101⟩ 10 200

def always : Invariant Nat := fun _ => True

def alwaysVerdict : Spec.Verdict always :=
  .free (fun _ _ _ _ => trivial)

def invariant : CheckedInvariant always :=
  CheckedInvariant.ofVerdict declaration ⟨102⟩ 200 alwaysVerdict natCodec

def encodeBoolSet (state : Catalog.GSet Bool) : List Nat :=
  [if state false then 1 else 0, if state true then 1 else 0]

def decodeBoolSet : List Nat → Option (Catalog.GSet Bool)
  | [left, right] => some (fun key => if key then right != 0 else left != 0)
  | _ => none

theorem decodeBoolSet_encodeBoolSet (state : Catalog.GSet Bool) :
    decodeBoolSet (encodeBoolSet state) = some state := by
  apply congrArg some
  funext key
  cases key
  · cases h : state false <;> simp_all
  · cases h : state true <;> simp_all

def boolSetCodec : FirstOrderCodec (Catalog.GSet Bool) :=
  ⟨encodeBoolSet, decodeBoolSet, decodeBoolSet_encodeBoolSet⟩

def atMostOneBool : Invariant (Catalog.GSet Bool) :=
  fun state => state false = true → state true = true → False

def leftBool : Catalog.GSet Bool := fun key => key == false

def rightBool : Catalog.GSet Bool := fun key => key == true

def atMostOneBoolVerdict : Spec.Verdict atMostOneBool :=
  .clash leftBool rightBool (by simp [atMostOneBool, leftBool])
    (by simp [atMostOneBool, rightBool]) (by
    intro merged
    exact merged rfl rfl)

def clashingInvariant : CheckedInvariant atMostOneBool :=
  CheckedInvariant.ofVerdict declaration ⟨106⟩ 201 atMostOneBoolVerdict boolSetCodec

def forward : Evidence.Future Nat := fun before after => before ≤ after

def future : CheckedFuture forward :=
  CheckedFuture.ofRelation declaration ⟨103⟩ 200 300

def session : CheckedSession Scheduling.oneCrossingPeerSession :=
  CheckedSession.ofSession declaration ⟨104⟩

def plan : CheckedPlan session Scheduling.oneCrossingPeerPlan :=
  CheckedPlan.ofPlan ⟨105⟩

def budget : CheckedBudget session Scheduling.oneCrossingPeerPlan
    Scheduling.peerOnlyLimits :=
  CheckedBudget.ofProfileUpperBound plan Scheduling.oneCrossingPeerProfileUpperBound
    rfl ⟨107⟩

def bundle : Artifact :=
  (((((((Artifact.ofDeclaration declaration).addField field).addInvariant invariant).addInvariant
    clashingInvariant).addFuture future).addSession session).addPlan plan).addBudget budget

/-- All seven declaration surfaces are present; this is not an empty-list
roundtrip dressed up as an acceptance test. -/
example : bundle.fields.length = 1
    ∧ bundle.invariants.length = 2
    ∧ bundle.futures.length = 1
    ∧ bundle.sessions.length = 1
    ∧ bundle.plans.length = 1
    ∧ bundle.budgets.length = 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Both verdict constructors were eliminated from checked terms, not supplied
to the artifact constructor; the clash retains its two runnable witnesses. -/
example : bundle.invariants.map InvariantArtifact.verdict =
    [.free, .clash [1, 0] [0, 1]] := rfl

/-- The plan export retains the real action and its multi-currency profile. -/
example : bundle.plans.map (fun p => (p.actions.length, p.profile)) =
    [(1, [(.peerBarrier, 1), (.arbiterCut, 0), (.networkRound, 0),
      (.userPrompt, 0), (.rollback, 0)])] := rfl

/-- The checked budget names that exact session and plan, preserves all five
promised limits, and records the same exact five-currency realized profile. -/
example : bundle.budgets =
    [⟨⟨107⟩, ⟨104⟩, ⟨105⟩,
      [(.peerBarrier, 1), (.arbiterCut, 0), (.networkRound, 0),
       (.userPrompt, 0), (.rollback, 0)],
      [(.peerBarrier, 1), (.arbiterCut, 0), (.networkRound, 0),
       (.userPrompt, 0), (.rollback, 0)]⟩] := rfl

/-- Whole-bundle canonical roundtrip, with every list nonempty. -/
example : bundle.canonicalEncoding.decode = bundle :=
  ArtifactEncoding.decode_canonicalEncoding bundle

end Examples

end Uwueave.Preo.Artifact
