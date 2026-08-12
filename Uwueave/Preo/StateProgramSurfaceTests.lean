/- Test-only acceptance for the standalone application-state program surface. -/
import Uwueave.Preo.StateProgramSurface

namespace Uwueave.Preo.StateProgramSurface.Tests

open Uwueave Uwueave.Preo

structure AppState where
  count : Nat
  enabled : Bool
  deriving DecidableEq

abbrev AppSchema : Expr.Schema := [.nat, .bool]

def appProject (state : AppState) : Expr.Env AppSchema :=
  .cons (t := .nat) state.count (.cons (t := .bool) state.enabled .nil)

def start : AppState := ⟨2, true⟩
def later : AppState := ⟨4, false⟩

def natPolicy : ResultProgram.SurfacePolicy AppState Nat where
  name := "journey/inspectable"
  visibility := fun _ _ => .inspectable
  disclosure := fun _ _ => .shown

preo_program Journey over {
  state := AppState,
  schema := AppSchema,
  project := appProject,
  reach := [start, later],
  raw := .natSucc (.field 0),
  futureId := "journey/projected-env-equality",
  resolution := .preserveFork,
  policy := natPolicy }

def handProgram : StateProgram AppState AppSchema where
  program := Journey.Program
  project := appProject
  stateReach := [start, later]

/-- Whole-value equality: the surface adds no hidden state or inferred reach. -/
theorem journey_is_hand_program : Journey = handProgram := rfl

example : Journey.State = AppState := rfl
example : Journey.Schema = AppSchema := rfl
example : Journey.Project = appProject := rfl
example : Journey.StateReach = [start, later] := rfl
example : Journey.EnvReach = [appProject start, appProject later] := rfl
example (env : Expr.Env AppSchema) :
    env ∈ Journey.EnvReach ↔
      ∃ state ∈ Journey.StateReach, Journey.Project state = env :=
  Journey.mem_envReach_iff env
example : Journey.Eval start = Journey.Program.eval (appProject start) := rfl
example : Journey.Result.reach = [start, later] := rfl
example : Journey.Result.descriptor.resolution = .preserveFork := rfl
example : Journey.Result.futureId = "journey/projected-env-equality" := rfl
example : Journey.Policy.name = "journey/inspectable" := rfl
example : Journey.Cache = Incremental.ProgramCache Journey.Program := rfl

def startReport : Journey.Report := Journey.reportAt start (by simp [Journey.StateReach])

example : startReport.checked.state = start := rfl
example : Journey.Carrier.site startReport.checked.output = start :=
  ResultProgram.CheckedReport.site_exact startReport.checked

/-! Wrong raw/schema combinations fail before `Program` or later artifacts. -/

/--
error: preo_program: `BadSchema` was refused by `Preo.Expr.Raw.infer`.
-/
#guard_msgs (error, substring := true) in
preo_program BadSchema over {
  state := AppState,
  schema := AppSchema,
  project := appProject,
  reach := [start],
  raw := .natSucc (.field 1),
  futureId := "bad",
  resolution := .preserveFork,
  policy := natPolicy }

/-! A projection at the wrong schema is a required-emission failure and the
whole namespace is rolled back, including declarations emitted before it. -/

/--
error: Type mismatch
  appProject
has type
  AppState → Expr.Env AppSchema
but is expected to have type
  State → Expr.Env Schema
-/
#guard_msgs (error, substring := true) in
preo_program Reused over {
  state := AppState,
  schema := [.nat],
  project := appProject,
  reach := [start],
  raw := .natSucc (.field 0),
  futureId := "bad-projection",
  resolution := .preserveFork,
  policy := natPolicy }

/- Reusing the exact prefix proves the failed command left no declarations. -/
preo_program Reused over {
  state := AppState,
  schema := AppSchema,
  project := appProject,
  reach := [start],
  raw := .natSucc (.field 0),
  futureId := "reused",
  resolution := .preserveFork,
  policy := natPolicy }

#check Reused
#check Reused.State
#check Reused.Project
#check Reused.Result
#check Reused.reportAt

/-! Report construction refuses a state without authored reach evidence. -/

/--
error: Tactic `decide` proved that the proposition
-/
#guard_msgs (error, substring := true) in
example : Reused.Report := Reused.reportAt later (by decide)

end Uwueave.Preo.StateProgramSurface.Tests
