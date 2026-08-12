/-
# Uwueave.Preo.Quickstart — one custom-state journey

This is an executable, user-readable path through the checked Preoscript
surfaces.  One application state is projected explicitly into a typed query
environment; the query is named as a world-indexed future and certificate;
native protocol syntax feeds finite planning and a checked five-currency
budget.  V3 export and durable inspection continue from these same values
below—there is no report-string reconciliation layer.

Every list in this file is authored analysis scope.  It is not a discovered or
authenticated deployment reach, and the durable host tests do not turn
`sync_data` into a filesystem theorem.
-/
import Uwueave.Preo.Elab
import Uwueave.Preo.StateProgramSurface
import Uwueave.Preo.ProtocolSurface
import Uwueave.Preo.PlanningSurface
import Uwueave.Preo.BoundResult
import Uwueave.Preo.ArtifactV3Checked
import Uwueave.Preo.ArtifactV3Durable
import Uwueave.Preo.ArtifactInspectionV1
import Uwueave.Preo.ProjectionV3Core

namespace Uwueave.Preo.Quickstart

open Uwueave Uwueave.Preo
open Uwueave.Preo.Planning.Examples

/-! ## 1. Application state → explicit typed environment → checked query -/

structure AppState where
  count : Nat
  enabled : Bool
  deriving DecidableEq, Repr

abbrev AppSchema : Expr.Schema := [.nat, .bool]

def project (state : AppState) : Expr.Env AppSchema :=
  .cons (t := .nat) state.count (.cons (t := .bool) state.enabled .nil)

def start : AppState := ⟨2, true⟩
def later : AppState := ⟨4, false⟩

def queryPolicy : ResultProgram.SurfacePolicy AppState Nat where
  name := "quickstart/inspectable"
  visibility := fun _ _ => .inspectable
  disclosure := fun _ _ => .shown

preo_program Journey over {
  state := AppState,
  schema := AppSchema,
  project := project,
  reach := [start, later],
  raw := .natSucc (.field 0),
  futureId := "quickstart/projected-environment-equality",
  resolution := .preserveFork,
  policy := queryPolicy }

/-- The surface value is exactly the hand-written semantic binding. -/
theorem journey_exact : Journey =
    ({ program := Journey.Program, project := project,
       stateReach := [start, later] } : StateProgram AppState AppSchema) := rfl

theorem journey_rows_exact :
    Journey.StateReach = [start, later]
      ∧ Journey.EnvReach = [project start, project later]
      ∧ Journey.Result.futureId =
        "quickstart/projected-environment-equality"
      ∧ Journey.Result.descriptor.resolution = .preserveFork := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem journey_eval_exact :
    (show Nat from Journey.Eval start) = 3 ∧
    (show Nat from Journey.Eval later) = 5 := by
  exact ⟨rfl, rfl⟩

def startReport : Journey.Report :=
  Journey.reportAt start (by simp [Journey.StateReach])

theorem start_report_is_at_checked_state :
    Journey.Carrier.site startReport.checked.output = start :=
  ResultProgram.CheckedReport.site_exact startReport.checked

/-! ## 2. The same query named at a retained world and certificate -/

structure AppWorld where
  state : AppState
  generation : Nat
  deriving DecidableEq, Repr

def appWorldModel : Future.WorldModel where
  World := AppWorld
  State := AppState
  Pool := Unit
  Frontier := Unit
  Epoch := Nat
  observe := AppWorld.state
  pool := fun _ => ()
  frontier := fun _ => ()
  epoch := AppWorld.generation

/-- The future is equality of the authored typed projection, not equality of
the whole application world. -/
def QueryFuture : Future.FutureDecl appWorldModel where
  name := "quickstart/projected-environment-equality"
  scope := .sealed
  future := fun before after => Journey.Future before.state after.state

def queryKey (_world : AppWorld) : Unit := ()
def QueryAccepted (_key : Unit) : Prop := True

def startWorld : AppWorld := ⟨start, 0⟩
def startIndex : Future.WorldIndex appWorldModel := ⟨startWorld⟩

def worldBinding : BoundResult.WorldBinding QueryFuture Journey.Result where
  worldToState := AppWorld.state
  worldReach := [startWorld]
  projectsReach := by
    intro world member
    simp only [List.mem_singleton] at member
    subst world
    change start ∈ [start, later]
    simp
  worldSound := by
    let sound := Journey.totalSound
    exact {
      core := {
        exact_correct := fun world => sound.core.exact_correct world.state
        exact_final := fun before after =>
          sound.core.exact_final before.state after.state
        absent_correct := fun world => sound.core.absent_correct world.state
        absent_final := fun before after =>
          sound.core.absent_final before.state after.state
        pending_escapable := by
          intro world pending
          simp [Journey.Result] at pending }
      exact_settled := fun world => sound.exact_settled world.state
      provisional_correct := fun world => sound.provisional_correct world.state
      forkedClosed_correct := fun world => sound.forkedClosed_correct world.state
      forkedOpen_correct := fun world => sound.forkedOpen_correct world.state
      absent_settled := fun world => sound.absent_settled world.state
      pending_correct := fun world => sound.pending_correct world.state
      pending_open := fun world => sound.pending_open world.state }

preo_certificate QueryCertificate :
    Future.CheckedCertificate QueryFuture worldBinding.declaration.answer
      queryKey QueryAccepted startIndex := by
  refine { accepted := True.intro, soundForAll := ?_ }
  intro world _ futureWorld hfuture
  change Journey.answer futureWorld.state = Journey.answer world.state
  funext value
  exact congrArg (fun output => decide (value = output))
    (congrArg Journey.Program.eval hfuture.symm)

theorem certificate_is_for_exact_future_and_world :
    QueryFuture.name = Journey.FutureId
      ∧ startIndex.world = startWorld := by
  exact ⟨rfl, rfl⟩

def certifiedStartReport :=
  worldBinding.certifiedReportAtWorld startIndex QueryCertificate (by
    change startWorld ∈ [startWorld]
    simp)

def exactStartBranch :
    BoundResult.WorldBinding.CertifiedReport.ExactBranch certifiedStartReport where
  value := Journey.Eval start
  isExact := rfl

theorem certified_report_keeps_exact_world :
    certifiedStartReport.report.checked.state = startIndex.world :=
  certifiedStartReport.world_exact

/-! ## 3. Native protocol → finite plan → one checked budget -/

preo_protocol JourneyProtocol over Unit at () :=
  .operation {
    id := 100,
    crossings := 2,
    needs := [
      { origin := .crossing(0),
        demand := {
          currency := .peerBarrier,
          participants := [0, 1],
          scope := 7,
          epoch := 3,
          evidence := .named(11),
          round := 0,
          barrier := 5 } },
      { origin := .crossing(1),
        demand := {
          currency := .peerBarrier,
          participants := [0, 1],
          scope := 7,
          epoch := 3,
          evidence := .named(11),
          round := 0,
          barrier := 5 } } ] }

theorem protocol_is_exact :
    JourneyProtocol.Session = Scheduling.coalescingSession := rfl

preo_plan JourneyPlan for JourneyProtocol over
    (Planning.sharedBudgetPromise fourTokenSpace.budget) := {
  actions := coalescingActions.actions,
  maxChoices := 2,
  problem := usableProblem
} selected by usable_result_selected

preo_budget JourneyBudget for JourneyProtocol.Elaboration : JourneyPlan.Limits :=
  JourneyPlan.ProfileUpperBound

theorem plan_and_budget_are_exact :
    JourneyPlan.Result = usableResult
      ∧ JourneyPlan.Plan.profile .peerBarrier = 1
      ∧ JourneyPlan.Plan.profile .arbiterCut = 0
      ∧ JourneyPlan.Plan.profile .networkRound = 0
      ∧ JourneyPlan.Plan.profile .userPrompt = 0
      ∧ JourneyPlan.Plan.profile .rollback = 0
      ∧ JourneyBudget = JourneyPlan.ProfileUpperBound
      ∧ JourneyPlan.RepairPrice = Repair.restrictionPrice := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, by decide⟩

/-! ## 4. The same checked values become one typed V3 artifact -/

namespace StableId

def declaration : Artifact.DeclarationId := ⟨1000⟩
def stateType : Nat := 1001
def countField : Artifact.FieldId := ⟨1002⟩
def countType : Nat := 1003
def enabledField : Artifact.FieldId := ⟨1004⟩
def enabledType : Nat := 1005
def future : Artifact.FutureId := ⟨1006⟩
def worldType : Nat := 1007
def futureRelation : Nat := 1008
def session : Artifact.SessionId := ⟨1009⟩
def plan : Artifact.PlanId := ⟨1010⟩
def budget : Artifact.BudgetId := ⟨1011⟩

def schema : ArtifactV3.SchemaId := ⟨1100⟩
def query : ArtifactV3.QueryId := ⟨1101⟩
def resultId : ArtifactV3.ResultId := ⟨1102⟩
def program : ArtifactV3.ProgramId := ⟨1103⟩
def certificate : ArtifactV3.CertificateId := ⟨1104⟩
def world : ArtifactV3.WorldId := ⟨1105⟩
def surface : ArtifactV3.SurfaceId := ⟨1106⟩

end StableId

def artifactDeclaration : Artifact.CheckedDeclaration AppState :=
  Artifact.CheckedDeclaration.ofState StableId.declaration StableId.stateType 3

def artifactCountField : Artifact.CheckedField Nat :=
  Artifact.CheckedField.ofCarrier artifactDeclaration StableId.countField 0
    StableId.countType

def artifactEnabledField : Artifact.CheckedField Bool :=
  Artifact.CheckedField.ofCarrier artifactDeclaration StableId.enabledField 0
    StableId.enabledType

def artifactFuture : Artifact.CheckedFuture QueryFuture.future :=
  Artifact.CheckedFuture.ofRelation artifactDeclaration StableId.future
    StableId.worldType StableId.futureRelation

def artifactSession : Artifact.CheckedSession JourneyProtocol.Session :=
  Artifact.CheckedSession.ofSession artifactDeclaration StableId.session

def artifactPlan : Artifact.CheckedPlan artifactSession JourneyPlan.Plan :=
  Artifact.CheckedPlan.ofPlan StableId.plan

def artifactBudget :
    Artifact.CheckedBudget artifactSession JourneyPlan.Plan JourneyPlan.Limits :=
  Artifact.CheckedBudget.ofProfileUpperBound artifactPlan JourneyBudget rfl
    StableId.budget

def baseArtifact : Artifact.Artifact :=
  let base := Artifact.Artifact.ofDeclaration artifactDeclaration
  let base := base.addField artifactCountField
  let base := base.addField artifactEnabledField
  let base := base.addFuture artifactFuture
  let base := base.addSession artifactSession
  let base := base.addPlan artifactPlan
  base.addBudget artifactBudget

theorem base_ids_exact :
    baseArtifact.declaration.id = StableId.declaration
      ∧ baseArtifact.fields.map (·.id) =
        [StableId.countField, StableId.enabledField]
      ∧ baseArtifact.futures.map (·.id) = [StableId.future]
      ∧ baseArtifact.sessions.map (·.id) = [StableId.session]
      ∧ baseArtifact.plans.map (·.id) = [StableId.plan]
      ∧ baseArtifact.budgets.map (·.id) = [StableId.budget] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def queryFieldId (position : Nat) : Artifact.FieldId :=
  if position = 0 then StableId.countField else StableId.enabledField

def checkedQuery : ArtifactV3.CheckedQuery baseArtifact Journey :=
  ArtifactV3.CheckedQuery.ofStateProgram baseArtifact Journey StableId.query
    StableId.schema StableId.resultId StableId.program queryFieldId (by
      intro position read
      change position ∈ [0] at read
      simp at read
      subst position
      rfl)

theorem checked_query_row_exact :
    checkedQuery.toRow = {
      id := StableId.query,
      schema := StableId.schema,
      «result» := StableId.resultId,
      program := StableId.program,
      reads := [StableId.countField],
      holes := [{ path := [0], field := StableId.countField, kind := .field }],
      analyses := [.mergeSafe, .monotoneSafe] } := by
  rfl

/-- Each V3 identity is first bound to the exact proof-bearing input which it
names. -/
def checkedWorld : ArtifactV3.CheckedWorld startIndex :=
  ArtifactV3.CheckedWorld.ofWorldIndex startIndex StableId.world

def checkedResolution : ArtifactV3.CheckedResolution Journey.Resolution :=
  ArtifactV3.CheckedResolution.ofResolution Journey.Resolution (fun _ => ⟨0⟩)

def checkedSurface : ArtifactV3.CheckedSurface Journey.Policy :=
  ArtifactV3.CheckedSurface.ofPolicy Journey.Policy StableId.surface (fun _ => ⟨0⟩)

def checkedResult :=
  ArtifactV3.CheckedResult.ofCertifiedReport checkedQuery artifactFuture checkedWorld
    certifiedStartReport checkedResolution checkedSurface

def resultRow : ArtifactV3.ResultRow :=
  checkedResult.toExactRow exactStartBranch

def checkedCertificate :
    ArtifactV3.CheckedCertificate
      (futureDecl := QueryFuture)
      (State := AppState) (Γ := AppSchema) (source := Journey)
      (stateResolution := Journey.Resolution)
      (name := "Uwueave.Preo.Quickstart.Journey")
      (futureName := Journey.FutureId) (stateSurface := Journey.Policy)
      (binding := worldBinding) (key := queryKey) (C := QueryAccepted)
      (index := startIndex) (future := artifactFuture) (world := checkedWorld)
      certifiedStartReport :=
  ArtifactV3.CheckedCertificate.ofCertifiedReport
    (futureDecl := QueryFuture)
    (State := AppState) (Γ := AppSchema) (source := Journey)
    (stateResolution := Journey.Resolution)
    (name := "Uwueave.Preo.Quickstart.Journey")
    (futureName := Journey.FutureId) (stateSurface := Journey.Policy)
    (binding := worldBinding) (key := queryKey) (C := QueryAccepted)
    (index := startIndex)
    (future := artifactFuture) (world := checkedWorld)
    certifiedStartReport StableId.certificate

def certificateRow : ArtifactV3.CertificateRow :=
  ArtifactV3.CheckedCertificate.toRow checkedCertificate

theorem checked_result_and_certificate_rows_exact :
    resultRow = {
      id := StableId.resultId,
      query := StableId.query,
      future := StableId.future,
      resolution := .preserveFork,
      surface := StableId.surface,
      status := .exact,
      effect := [.exact],
      visibility := .inspectable,
      disclosure := some .shown }
      ∧ certificateRow = {
        id := StableId.certificate,
        future := StableId.future,
        world := StableId.world } := by
  exact ⟨rfl, rfl⟩

/-- The aggregate is assembled only through checked append operations. -/
def v3Artifact : ArtifactV3.ArtifactV3Encoding :=
  let encoded := ArtifactV3.ArtifactV3Encoding.ofArtifact baseArtifact StableId.schema
  let encoded := encoded.addQuery checkedQuery rfl rfl
    (by intro previous member; cases member)
  let encoded := encoded.addWorld checkedWorld
    (by intro previous member; cases member)
  let encoded := encoded.addExactResult checkedResult exactStartBranch rfl rfl rfl
    (by intro previous member; cases member)
  encoded.addCertificate checkedCertificate rfl rfl
    (by intro previous member; cases member)

theorem v3_rows_exact :
    v3Artifact.base = baseArtifact.canonicalEncoding
      ∧ v3Artifact.schema = StableId.schema
      ∧ v3Artifact.worlds = [StableId.world]
      ∧ v3Artifact.queries = [checkedQuery.toRow]
      ∧ v3Artifact.results = [resultRow]
      ∧ v3Artifact.certificates = [certificateRow]
      ∧ resultRow.future = artifactFuture.id
      ∧ certificateRow.future = artifactFuture.id := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def validationConfig : ProjectionV3.ValidationConfig where
  bounds := {
    base := {
      maxFields := 2
      maxInvariants := 0
      maxFutures := 1
      maxSessions := 1
      maxPlans := 1
      maxBudgets := 1
      maxObligationsPerSession := 2
      maxActionsPerPlan := 2
      maxProfileEntriesPerPlan := 5
      maxProfileEntriesPerBudget := 5
      maxParticipantsPerDemand := 2
      maxWitnessWords := 0 }
    maxStableIdValue := 1106
    maxWorlds := 1
    maxQueries := 1
    maxResults := 1
    maxCertificates := 1
    maxReadsPerQuery := 1
    maxHolesPerQuery := 1
    maxHolePathDepth := 1
    maxAnalysesPerQuery := 2
    maxEffectShapesPerResult := 1 }

theorem v3_artifact_validates :
    (ProjectionV3.validate validationConfig
      (ProjectionV3.Projection.ofEncoding v3Artifact)).isOk = true := by
  decide

/-- These are the real version-3 durable frame bytes, not a rendered report. -/
def v3Bytes : List UInt8 := ArtifactV3Durable.projectionBytes v3Artifact

theorem v3_bytes_reopen_exact :
    ArtifactV3Durable.decodeProjection v3Bytes = some (v3Artifact, []) :=
  ArtifactV3Durable.decodeProjection_projectionBytes v3Artifact

/-- Stack-safe executable framing, proved byte-identical to `v3Bytes`. -/
def v3BytesExecutable : List UInt8 :=
  ArtifactDurable.stackSafeEncodeValue ArtifactV3Durable.artifactV3Codec
    ArtifactV3Durable.artifactV3Format v3Artifact

theorem v3_bytes_executable_exact : v3BytesExecutable = v3Bytes := by
  exact ArtifactDurable.stackSafeEncodeValue_eq _ _ _

/-- Pure diagnostic inspection decodes and validates the same durable frame.
The companion host test writes, reopens, and journals these exact bytes. -/
def inspection : Except ArtifactInspectionV1.Error Lean.Json :=
  ArtifactInspectionV1.inspectFrame {} v3BytesExecutable

end Uwueave.Preo.Quickstart
