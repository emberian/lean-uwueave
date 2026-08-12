/-
# Uwueave.Preo.ProjectionV1Examples — checked V1 examples

Worked semantic values and adversarial refusals are opt-in so the production
validator and renderer do not import the proof-indexed `Export` layer. The
declarations retain their historical `ProjectionV1.Examples` names, but a
direct `import ProjectionV1` no longer brings them into scope; import this
module explicitly. Exact renderer strings live one layer higher in
`ProjectionV1Fixtures`.
-/
import Uwueave.Preo.ProjectionV1
import Uwueave.Preo.Export

namespace Uwueave.Preo.ProjectionV1

open Uwueave.Preo
open Uwueave.Preo.Artifact

set_option autoImplicit false

namespace Examples


private def validationError? {alpha : Type} :
    ValidationResult alpha → Option ValidationError
  | .ok _ => none
  | .error error => some error

/-- Deliberately finite test policy.  Production hosts must choose their own
limits instead of treating these example values as protocol constants. -/
def config : ValidationConfig where
  bounds := {
    maxFields := 8
    maxInvariants := 8
    maxFutures := 8
    maxSessions := 8
    maxPlans := 8
    maxObligationsPerSession := 8
    maxActionsPerPlan := 8
    maxProfileEntriesPerPlan := 5
    maxParticipantsPerDemand := 8
    maxWitnessWords := 8 }

def emptyConfig : ValidationConfig where
  bounds := {
    maxFields := 0
    maxInvariants := 0
    maxFutures := 0
    maxSessions := 0
    maxPlans := 0
    maxObligationsPerSession := 0
    maxActionsPerPlan := 0
    maxProfileEntriesPerPlan := 0
    maxParticipantsPerDemand := 0
    maxWitnessWords := 0 }

def emptyProjection : Projection :=
  Projection.ofEncoding {
    declaration := ⟨1, 2, 3⟩
    fields := []
    invariants := []
    futures := []
    sessions := []
    plans := []
    budgets := [] }

def artifactExample : Projection :=
  let encoding := Artifact.Examples.bundle.canonicalEncoding
  Projection.ofEncoding { encoding with budgets := [] }

def exportExample : Projection :=
  let encoding := Export.Examples.bundle.project.encoding
  Projection.ofEncoding { encoding with budgets := [] }

def rendererDemand : DemandArtifact where
  currency := .peerBarrier
  participants := [0, 1]
  scope := 7
  epoch := 3
  evidence := .named 11
  round := 0
  barrier := 5

def rendererProfile : List (Currency × Nat) :=
  [(.peerBarrier, 1), (.arbiterCut, 0), (.networkRound, 0),
   (.userPrompt, 0), (.rollback, 0)]

/-- A compact first-order fixture spelling every renderer shape explicitly.
It is still raw input and must pass `validate` before the public renderer can
consume it. -/
def rendererFixture : Projection :=
  Projection.ofEncoding {
    declaration := ⟨100, 200, 1⟩
    fields := [⟨101, 100, 10, 200, none⟩]
    invariants := [⟨102, 100, 200, .free⟩, ⟨106, 100, 201, .clash [1, 0] [0, 1]⟩]
    futures := [⟨103, 100, 200, 300⟩]
    sessions := [⟨104, 100, 1, [⟨.crossing 0, rendererDemand⟩]⟩]
    plans := [⟨105, 104, [rendererDemand], rendererProfile⟩]
    budgets := [] }
theorem artifact_example_validates :
    (validate config artifactExample).isOk = true := by decide

/-- The proof-indexed export example includes a certified ERA future and a
real protocol elaboration. -/
theorem export_example_validates :
    (validate config exportExample).isOk = true := by decide

theorem renderer_fixture_validates :
    (validate config rendererFixture).isOk = true := by decide

def duplicateField : Projection :=
  let encoding := artifactExample.encoding
  { artifactExample with encoding :=
      { encoding with fields := encoding.fields ++ encoding.fields } }

theorem duplicate_field_refused : validationError? (validate config duplicateField) =
    some (.duplicateStableId .field 101) := by decide

def budgetBearingArtifactExample : Projection :=
  Projection.ofEncoding Artifact.Examples.bundle.canonicalEncoding

/-- V1's generated Rust contract predates budget rows.  New encodings must use
the version that specifies their shape instead of silently dropping them. -/
theorem nonempty_budgets_refused :
    validationError? (validate config budgetBearingArtifactExample) =
      some (.budgetsNotSupported 1) := by decide

/-- The public raw-input convenience path preserves the refusal; it has no
fallback constructor with which to invoke `renderRustSource`. -/
theorem duplicate_field_cannot_reach_renderer :
    validationError? (validateAndRender config duplicateField) =
      some (.duplicateStableId .field 101) := by decide

def wrongFieldDeclaration : Projection :=
  let encoding := artifactExample.encoding
  { artifactExample with encoding :=
      { encoding with fields := encoding.fields.map fun field =>
          { field with declarationId := 999 } } }

theorem wrong_field_declaration_refused :
    validationError? (validate config wrongFieldDeclaration) =
    some (.wrongDeclarationReference .field 101 100 999) := by decide

def danglingPlan : Projection :=
  let encoding := artifactExample.encoding
  { artifactExample with encoding :=
      { encoding with plans := encoding.plans.map fun plan =>
          { plan with sessionId := 999 } } }

theorem dangling_plan_session_refused : validationError? (validate config danglingPlan) =
    some (.danglingPlanSession 105 999) := by decide

def outOfRangeCrossing : Projection :=
  let encoding := artifactExample.encoding
  { artifactExample with encoding :=
      { encoding with sessions := encoding.sessions.map fun session =>
          { session with crossings := 0 } } }

theorem out_of_range_crossing_refused :
    validationError? (validate config outOfRangeCrossing) =
    some (.crossingIndexOutOfRange 104 0 0 0) := by decide

def nonCanonicalProfile : Projection :=
  let encoding := artifactExample.encoding
  { artifactExample with encoding :=
      { encoding with plans := encoding.plans.map fun plan =>
          { plan with profile := [] } } }

theorem noncanonical_profile_refused :
    validationError? (validate config nonCanonicalProfile) =
    some (.nonCanonicalPlanProfile 105 []) := by decide

def zeroFieldBound : ValidationConfig :=
  { config with bounds := { config.bounds with maxFields := 0 } }

theorem field_bound_enforced :
    validationError? (validate zeroFieldBound artifactExample) =
    some (.listTooLarge .fields 1 0) := by decide

def oneWitnessWordBound : ValidationConfig :=
  { config with bounds := { config.bounds with maxWitnessWords := 1 } }

theorem witness_bound_enforced :
    validationError? (validate oneWitnessWordBound artifactExample) =
    some (.listTooLarge (.clashWitness 106 .left) 2 1) := by decide

def zeroObligationBound : ValidationConfig :=
  { config with bounds := { config.bounds with maxObligationsPerSession := 0 } }

theorem obligation_bound_enforced :
    validationError? (validate zeroObligationBound artifactExample) =
    some (.listTooLarge (.sessionObligations 104) 1 0) := by decide

def wrongSchema : Projection :=
  { artifactExample with schema := "uwueave/preo-projection/v2" }

theorem wrong_schema_refused : validationError? (validate config wrongSchema) =
    some (.wrongSchema schema "uwueave/preo-projection/v2") := by decide

theorem wrong_schema_cannot_reach_renderer :
    validationError? (validateAndRender config wrongSchema) =
      some (.wrongSchema schema "uwueave/preo-projection/v2") := by decide


end Examples

end Uwueave.Preo.ProjectionV1
