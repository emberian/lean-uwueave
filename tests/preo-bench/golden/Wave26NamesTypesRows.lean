import Uwueave.Preo.StateProgramSurfaceTests
import Uwueave.Preo.PlanningSurface
import Uwueave.Preo.Quickstart
import Uwueave.Preo.ProjectionV3
import Uwueave.Preo.ArtifactV3Surface

namespace PreoBench.Golden.Wave26NamesTypesRows

open Uwueave Uwueave.Preo
open Uwueave.Preo.StateProgramSurface.Tests
open Uwueave.Preo.Planning.Examples

namespace Inspector

open Lean Elab Command Meta

private def canonicalType (name : Name) : CommandElabM String :=
  liftTermElabM do
    let type := (← getConstInfo name).type
    let rendered := (← withOptions (fun opts =>
      opts.setBool `pp.universes true
        |>.setBool `pp.explicit true
        |>.setBool `pp.fullNames true
        |>.set `pp.width (100000 : Nat)) <| ppExpr type).pretty
    return (rendered.replace "\n" " ").replace "\t" " "

private def isPublicName : Name → Bool
  | .anonymous => true
  | .str parent component => isPublicName parent &&
      !(component.startsWith "_") && !(component.startsWith "eq_")
  | .num _ _ => false

syntax (name := wave26Inspect) "#wave26_inspect " ident : command

@[command_elab wave26Inspect]
def elabWave26Inspect : CommandElab := fun stx => do
  let targetStx := stx.getArgs.back!
  unless targetStx.isIdent do
    throwErrorAt targetStx "#wave26_inspect: expected a declaration prefix"
  let fullPrefix := (← getCurrNamespace) ++ targetStx.getId
  let env ← getEnv
  let names := env.constants.toList.filterMap (fun (name, _) =>
    if fullPrefix.isPrefixOf name && isPublicName name then some name else none)
    |>.toArray |>.qsort Name.lt
  for name in names do
    logInfo m!"CONST\t{name}\t{← canonicalType name}"

end Inspector

open Inspector

preo_program ProgramGolden over {
  state := AppState,
  schema := AppSchema,
  project := appProject,
  reach := [start, later],
  raw := .natSucc (.field 0),
  futureId := "bench/wave26/program",
  resolution := .preserveFork,
  policy := natPolicy }

preo_plan PlanGolden for ProtocolSurface.NativeFixture over
    (Planning.sharedBudgetPromise fourTokenSpace.budget) := {
  actions := nativeSurfaceActions.actions,
  maxChoices := 8,
  problem := nativeSurfaceProblem
} selected by native_protocol_surface_is_plannable

def Boundary : ResultProgram.ObservationBoundary AppState AppState where
  Authentic := Eq

def ProgramReport : ProgramGolden.Report :=
  ProgramGolden.reportAt start (by simp [ProgramGolden.StateReach])

def ObservedGolden :=
  ResultProgram.ObservedReport.attach Boundary start ProgramReport rfl

/-- The V3 command/export surface is not present at the Wave25 baseline.  This
is the paired checked-builder and production-renderer control. -/
def V3Golden : ProjectionV3.ValidationResult String :=
  ProjectionV3.validateAndRender Quickstart.validationConfig
    (ProjectionV3.Projection.ofEncoding Quickstart.v3Artifact)

def WorldBoundary : ResultProgram.ObservationBoundary
    Quickstart.AppWorld Quickstart.AppState where
  Authentic := fun world state => world.state = state

def RunningReach : List Quickstart.AppWorld := [Quickstart.startWorld]

def ObservedCertifiedGolden :
    ObservedBoundResult.ObservedCertifiedReport WorldBoundary
      Quickstart.worldBinding RunningReach Quickstart.queryKey
      Quickstart.QueryAccepted Quickstart.startIndex :=
  ObservedBoundResult.attachAtWorld WorldBoundary Quickstart.worldBinding
    RunningReach Quickstart.startIndex rfl
    (by change Quickstart.startWorld ∈ [Quickstart.startWorld]; simp)
    (by change Quickstart.startWorld ∈ [Quickstart.startWorld]; simp)
    Quickstart.QueryCertificate

preo_export_v3 ExportGolden from Quickstart.Journey := {
  base := Quickstart.baseArtifact,
  futureDecl := Quickstart.QueryFuture,
  binding := Quickstart.worldBinding,
  index := Quickstart.startIndex,
  observed := ObservedCertifiedGolden,
  certificate := Quickstart.QueryCertificate,
  plan := Quickstart.artifactPlan,
  budget := Quickstart.artifactBudget,
  query := Quickstart.checkedQuery,
  future := Quickstart.artifactFuture,
  world := Quickstart.checkedWorld,
  resolutionId := fun _ => ⟨0⟩,
  surfaceId := Quickstart.StableId.surface,
  reasonId := fun _ => ⟨0⟩,
  certificateId := Quickstart.StableId.certificate,
  branch := Quickstart.exactStartBranch,
  maxWork := 64,
  config := Quickstart.validationConfig }

namespace Rows

theorem program_state_reach : ProgramGolden.StateReach = [start, later] := rfl
theorem program_env_reach :
    ProgramGolden.EnvReach = [appProject start, appProject later] := rfl
theorem program_future_id :
    ProgramGolden.Result.futureId = "bench/wave26/program" := rfl
theorem plan_result : PlanGolden.Result = nativeSurfaceResult := rfl
theorem plan_limits :
    PlanGolden.PeerBarrierLimit = 2
      ∧ PlanGolden.ArbiterCutLimit = 0
      ∧ PlanGolden.NetworkRoundLimit = 1
      ∧ PlanGolden.UserPromptLimit = 2
      ∧ PlanGolden.RollbackLimit = 0 := by decide
theorem observed_world : ObservedGolden.world = start := rfl
theorem observed_site :
    ProgramGolden.Carrier.site ObservedGolden.report.checked.output = start :=
  ResultProgram.ObservedReport.authentic_site ObservedGolden
theorem v3_rows :
    Quickstart.v3Artifact.worlds = [Quickstart.StableId.world]
      ∧ Quickstart.v3Artifact.queries = [Quickstart.checkedQuery.toRow]
      ∧ Quickstart.v3Artifact.results = [Quickstart.resultRow]
      ∧ Quickstart.v3Artifact.certificates = [Quickstart.certificateRow] := by
  exact ⟨rfl, rfl, rfl, rfl⟩
theorem v3_validates : V3Golden.isOk = true := by decide
theorem observed_certified_exact :
    ObservedCertifiedGolden.world = Quickstart.startWorld
      ∧ ObservedCertifiedGolden.state = Quickstart.start
      ∧ ObservedCertifiedGolden.world ∈ RunningReach :=
  ⟨rfl, rfl, ObservedCertifiedGolden.reach.inRunning⟩
theorem export_encoding : ExportGolden.Encoding = Quickstart.v3Artifact := rfl
theorem export_bytes : ExportGolden.Bytes = Quickstart.v3Bytes := rfl

end Rows

#wave26_inspect ProgramGolden
#wave26_inspect PlanGolden
#wave26_inspect Boundary
#wave26_inspect ProgramReport
#wave26_inspect ObservedGolden
#wave26_inspect V3Golden
#wave26_inspect WorldBoundary
#wave26_inspect RunningReach
#wave26_inspect ObservedCertifiedGolden
#wave26_inspect ExportGolden
#wave26_inspect Rows

end PreoBench.Golden.Wave26NamesTypesRows
