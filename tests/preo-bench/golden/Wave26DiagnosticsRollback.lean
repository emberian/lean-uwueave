import Uwueave.Preo.StateProgramSurfaceTests
import Uwueave.Preo.PlanningSurface
import Uwueave.Preo.ArtifactV3Surface
import Uwueave.Preo.Quickstart

namespace PreoBench.Golden.Wave26DiagnosticsRollback

open Uwueave Uwueave.Preo
open Uwueave.Preo.StateProgramSurface.Tests
open Uwueave.Preo.Planning.Examples

/- A required projection fails after earlier generated declarations were
attempted. Reusing the identical prefix below is the whole-command rollback
gate. -/
/--
error: Type mismatch
  appProject
has type
  AppState → Expr.Env AppSchema
but is expected to have type
  State → Expr.Env Schema
-/
#guard_msgs (error, substring := true) in
preo_program ReusedProgram over {
  state := AppState,
  schema := [.nat],
  project := appProject,
  reach := [start],
  raw := .natSucc (.field 0),
  futureId := "bad-projection",
  resolution := .preserveFork,
  policy := natPolicy }

preo_program ReusedProgram over {
  state := AppState,
  schema := AppSchema,
  project := appProject,
  reach := [start],
  raw := .natSucc (.field 0),
  futureId := "bench/wave26/reused",
  resolution := .preserveFork,
  policy := natPolicy }

theorem reused_program_exact :
    ReusedProgram.StateReach = [start]
      ∧ ReusedProgram.Result.futureId = "bench/wave26/reused" :=
  ⟨rfl, rfl⟩

/- A protocol lookup fails after bounded-universe declarations were attempted.
The exact planning prefix is then reusable. -/
/--
error: Unknown identifier `ProtocolSurface.DoesNotExist.Session`
-/
#guard_msgs in
preo_plan ReusedPlan for ProtocolSurface.DoesNotExist over
    (Planning.sharedBudgetPromise fourTokenSpace.budget) := {
  actions := scheduleRefusalProblem.actionUniverse.actions,
  maxChoices := 2,
  problem := scheduleRefusalProblem
} result

preo_plan ReusedPlan for ProtocolSurface.NativeCoalescing over
    (Planning.sharedBudgetPromise fourTokenSpace.budget) := {
  actions := scheduleRefusalProblem.actionUniverse.actions,
  maxChoices := 2,
  problem := scheduleRefusalProblem
} result

theorem reused_plan_exact :
    Planning.Result.refusalKind? ReusedPlan.Result =
      some Planning.Result.RefusalKind.schedule := by decide

/- Observation attachment has no command transaction, but its boundary remains
proof carrying and rejects a caller-refuted world/state pair. -/
def Boundary : ResultProgram.ObservationBoundary AppState AppState where
  Authentic := Eq

theorem observation_refuses_wrong_state :
    ¬ ∃ observed : ResultProgram.ObservedReport Boundary
        ReusedProgram.Result ReusedProgram.Carrier,
      observed.world = later ∧ observed.report.checked.state = start :=
  ResultProgram.ObservedReport.refuses_inauthentic later start (by
    change later ≠ start
    decide)

/- The V3 surface accepts only the exact observed/certified family. A record
with the same projections lacks authenticity and independent running reach;
after refusal, the complete export prefix must be reusable. -/
def WorldBoundary : ResultProgram.ObservationBoundary
    Quickstart.AppWorld Quickstart.AppState where
  Authentic := fun world state => world.state = state
def RunningReach : List Quickstart.AppWorld := [Quickstart.startWorld]
def ExactObserved :
    ObservedBoundResult.ObservedCertifiedReport WorldBoundary
      Quickstart.worldBinding RunningReach Quickstart.queryKey
      Quickstart.QueryAccepted Quickstart.startIndex :=
  ObservedBoundResult.attachAtWorld WorldBoundary Quickstart.worldBinding
    RunningReach Quickstart.startIndex rfl
    (by change Quickstart.startWorld ∈ [Quickstart.startWorld]; simp)
    (by change Quickstart.startWorld ∈ [Quickstart.startWorld]; simp)
    Quickstart.QueryCertificate

structure Lookalike where
  binding : BoundResult.WorldBinding Quickstart.QueryFuture Quickstart.Journey.Result
  index : Future.WorldIndex Quickstart.appWorldModel
  report : Quickstart.worldBinding.CertifiedReport Quickstart.queryKey
    Quickstart.QueryAccepted Quickstart.startIndex
  certificate : Future.CheckedCertificate Quickstart.QueryFuture
    Quickstart.worldBinding.declaration.answer Quickstart.queryKey
    Quickstart.QueryAccepted Quickstart.startIndex

def FakeObserved : Lookalike where
  binding := Quickstart.worldBinding
  index := Quickstart.startIndex
  report := Quickstart.certifiedStartReport
  certificate := Quickstart.QueryCertificate

/--
error: preo_export_v3: the observed input is not an exact `ObservedBoundResult.ObservedCertifiedReport`
-/
#guard_msgs (error, substring := true) in
preo_export_v3 ReusedExport from Quickstart.Journey := {
  base := Quickstart.baseArtifact, futureDecl := Quickstart.QueryFuture,
  binding := Quickstart.worldBinding, index := Quickstart.startIndex,
  observed := FakeObserved, certificate := Quickstart.QueryCertificate,
  plan := Quickstart.artifactPlan, budget := Quickstart.artifactBudget,
  query := Quickstart.checkedQuery, future := Quickstart.artifactFuture,
  world := Quickstart.checkedWorld, resolutionId := fun _ => ⟨0⟩,
  surfaceId := Quickstart.StableId.surface, reasonId := fun _ => ⟨0⟩,
  certificateId := Quickstart.StableId.certificate,
  branch := Quickstart.exactStartBranch, maxWork := 64,
  config := Quickstart.validationConfig }

preo_export_v3 ReusedExport from Quickstart.Journey := {
  base := Quickstart.baseArtifact, futureDecl := Quickstart.QueryFuture,
  binding := Quickstart.worldBinding, index := Quickstart.startIndex,
  observed := ExactObserved, certificate := Quickstart.QueryCertificate,
  plan := Quickstart.artifactPlan, budget := Quickstart.artifactBudget,
  query := Quickstart.checkedQuery, future := Quickstart.artifactFuture,
  world := Quickstart.checkedWorld, resolutionId := fun _ => ⟨0⟩,
  surfaceId := Quickstart.StableId.surface, reasonId := fun _ => ⟨0⟩,
  certificateId := Quickstart.StableId.certificate,
  branch := Quickstart.exactStartBranch, maxWork := 64,
  config := Quickstart.validationConfig }

theorem reused_export_exact :
    ReusedExport.Encoding = Quickstart.v3Artifact
      ∧ ReusedExport.ObservedReport = ExactObserved := ⟨rfl, rfl⟩

end PreoBench.Golden.Wave26DiagnosticsRollback
