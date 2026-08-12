/-
# Uwueave.Preo.StateProgram — checked typed queries over application state.

`Expr.Program` evaluates a typed environment.  An application evaluates a
state.  This module joins them only through an explicit author-written
projection and an explicit finite list of application states.  It does not
infer field names, discover runtime reach, authenticate an external world, or
claim that two application states are related merely because a deployment can
move between them.
-/
import Uwueave.Preo.Incremental
import Uwueave.Preo.ResultProgram

namespace Uwueave.Preo

open Uwueave Uwueave.Catalog

/-- A checked typed expression bound to an application state by an explicit
projection. `stateReach` is authored analysis scope, not discovered runtime
reach. -/
structure StateProgram (State : Type) (Γ : Expr.Schema) where
  program : Expr.Program Γ
  project : State → Expr.Env Γ
  stateReach : List State

namespace StateProgram

variable {State : Type} {Γ : Expr.Schema}

/-- The environment reach is exactly the image of the authored state reach. -/
def envReach (p : StateProgram State Γ) : List (Expr.Env Γ) :=
  p.stateReach.map p.project

/-- Exact image characterization. There is intentionally no converse back to
state membership without an injective projection. -/
theorem mem_envReach_iff (p : StateProgram State Γ) (env : Expr.Env Γ) :
    env ∈ p.envReach ↔ ∃ state ∈ p.stateReach, p.project state = env := by
  simp [envReach]

/-- Every authored reachable state maps to a reachable typed environment. -/
theorem project_mem_envReach (p : StateProgram State Γ) {state : State}
    (h : state ∈ p.stateReach) : p.project state ∈ p.envReach :=
  (p.mem_envReach_iff _).2 ⟨state, h, rfl⟩

/-- Evaluation always passes through the authored projection. -/
def eval (p : StateProgram State Γ) (state : State) : p.program.type.denote :=
  p.program.eval (p.project state)

/-- Cache the exact projected environment of one application state. -/
def buildCache (p : StateProgram State Γ) (state : State) :
    Incremental.ProgramCache p.program :=
  Incremental.buildProgramCache p.program (p.project state)

@[simp] theorem buildCache_env (p : StateProgram State Γ) (state : State) :
    (p.buildCache state).env = p.project state := rfl

@[simp] theorem buildCache_value (p : StateProgram State Γ) (state : State) :
    (p.buildCache state).value = p.eval state := rfl

/-- Equality of projected environments is the exact pure-query future.  This
is deliberately weaker than equality of application states and stronger than
an unproved deployment transition relation. -/
def Future (p : StateProgram State Γ) : Evidence.Future State :=
  fun before after => p.project before = p.project after

/-- The singleton answer computed by the checked typed program. -/
def answer (p : StateProgram State Γ) (state : State) :
    GSet p.program.type.denote :=
  ResultProgram.ExactSnapshot.answer p.eval state

/-- Pure snapshot evaluation is settled at its state. -/
def settled (p : StateProgram State Γ) (state : State) : Prop :=
  ResultProgram.ExactSnapshot.settled p.eval state

/-- The pure typed evaluator has one exact result. -/
def evaluate (p : StateProgram State Γ) (state : State) :
    ResultStatus.Status p.program.type.denote :=
  ResultProgram.ExactSnapshot.evaluate p.eval state

/-- Complete six-status soundness over the explicit projection future. -/
theorem totalSound (p : StateProgram State Γ) :
    StatusEffects.TotalSoundEvaluator6 p.Future p.answer p.settled p.evaluate :=
  ResultProgram.ExactSnapshot.totalSound p.Future p.eval (by
    intro before after hfuture
    simp only [Future] at hfuture
    simp [eval, hfuture])

/-- Bind the checked query to an explicit future identity, resolution syntax,
and presentation policy.  No policy is inferred from the raw expression. -/
def declaration (p : StateProgram State Γ) (name futureId : String)
    (resolution : StatusEffects.Resolution State p.program.type.denote)
    (surface : ResultProgram.SurfacePolicy State p.program.type.denote) :
    ResultProgram.CheckedDeclaration State p.program.type.denote
      p.Future resolution where
  name := name
  futureId := futureId
  reach := p.stateReach
  answer := p.answer
  settled := p.settled
  evaluate := p.evaluate
  surface := surface
  totalSound := p.totalSound

@[simp] theorem declaration_reach (p : StateProgram State Γ) (name futureId : String)
    (resolution : StatusEffects.Resolution State p.program.type.denote)
    (surface : ResultProgram.SurfacePolicy State p.program.type.denote) :
    (p.declaration name futureId resolution surface).reach = p.stateReach := rfl

@[simp] theorem declaration_evaluate (p : StateProgram State Γ) (name futureId : String)
    (resolution : StatusEffects.Resolution State p.program.type.denote)
    (surface : ResultProgram.SurfacePolicy State p.program.type.denote) (state : State) :
    (p.declaration name futureId resolution surface).evaluate state =
      .exact (p.eval state) := rfl

@[simp] theorem declaration_resolution (p : StateProgram State Γ) (name futureId : String)
    (resolution : StatusEffects.Resolution State p.program.type.denote)
    (surface : ResultProgram.SurfacePolicy State p.program.type.denote) :
    (p.declaration name futureId resolution surface).descriptor.resolution = resolution := rfl

/-- Construct a checked report only from an authored state-reach membership
proof.  The generic result layer retains that proof as data. -/
def reportAt (p : StateProgram State Γ) (name futureId : String)
    (resolution : StatusEffects.Resolution State p.program.type.denote)
    (surface : ResultProgram.SurfacePolicy State p.program.type.denote)
    (state : State) (inReach : state ∈ p.stateReach) :
    ResultProgram.ReachReport (p.declaration name futureId resolution surface)
      (RenderSix.stdCarrier6 p.Future p.program.type.denote) :=
  ResultProgram.ReachReport.renderAt
    (p.declaration name futureId resolution surface)
    (RenderSix.stdCarrier6 p.Future p.program.type.denote) state inReach

end StateProgram
end Uwueave.Preo
