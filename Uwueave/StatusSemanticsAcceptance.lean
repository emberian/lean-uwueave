/-
# Uwueave.StatusSemanticsAcceptance — semantic report acceptance and refusals

Focused fixtures for the uniform six-row status API, the finite-reach report
adapter, and the explicit observation boundary.  The typed-program fixture is
deliberately exact-only: its future is snapshot equality, so it does not stand
in for an evidence evaluator capable of reaching all six cells.
-/
import Uwueave.Preo.Incremental

namespace Uwueave.StatusSemanticsAcceptance

open Uwueave Uwueave.Catalog
open Uwueave.ResultStatus (Status)
open Uwueave.Preo

/-! ## All six semantic rows are reached by the evidence declaration -/

private theorem evidence_semanticsAt (e : ResultProgram.EvidenceState) :
    (ResultStatus.statusOf e).Semantics (Evidence.values e) (Evidence.Closed e) :=
  ResultProgram.evidenceProgram.semanticsAt e

theorem exact_row :
    (Status.exact 47).Semantics (Evidence.values Evidence.exactW)
      (Evidence.Closed Evidence.exactW) := by
  simpa only [ResultStatus.statusOf_exactW] using evidence_semanticsAt Evidence.exactW

theorem provisional_row :
    (Status.provisional 47).Semantics (Evidence.values Evidence.openW)
      (Evidence.Closed Evidence.openW) := by
  simpa only [ResultStatus.statusOf_openW] using evidence_semanticsAt Evidence.openW

theorem forkedClosed_row :
    Status.forkedClosed.Semantics (Evidence.values Evidence.forkedClosedW)
      (Evidence.Closed Evidence.forkedClosedW) := by
  simpa only [ResultStatus.statusOf_forkedClosedW] using
    evidence_semanticsAt Evidence.forkedClosedW

theorem forkedOpen_row :
    Status.forkedOpen.Semantics (Evidence.values Evidence.forkedOpenW)
      (Evidence.Closed Evidence.forkedOpenW) := by
  simpa only [ResultStatus.statusOf_forkedOpenW] using
    evidence_semanticsAt Evidence.forkedOpenW

theorem absent_row :
    Status.absent.Semantics (Evidence.values ResultStatus.emptyClosedW)
      (Evidence.Closed ResultStatus.emptyClosedW) := by
  simpa only [ResultStatus.statusOf_emptyClosedW] using
    evidence_semanticsAt ResultStatus.emptyClosedW

theorem pending_row :
    Status.pending.Semantics (Evidence.values ResultStatus.emptyOpenW)
      (Evidence.Closed ResultStatus.emptyOpenW) := by
  simpa only [ResultStatus.statusOf_emptyOpenW] using
    evidence_semanticsAt ResultStatus.emptyOpenW

/-! ## The missing pending clause is load-bearing -/

namespace PendingCandidate

/-- A two-state future: `false` may advance to `true`; `true` is final. -/
def future : Evidence.Future Bool
  | false, _ => True
  | true, true => True
  | true, false => False

/-- The bad state says `pending` even though its answer set is nonempty. -/
def answer (_ : Bool) : GSet Unit := fun _ => true

def settled : Bool → Prop
  | false => False
  | true => True

def evaluate : Bool → Status Unit
  | false => .pending
  | true => .exact ()

/-- The historical contract admits the lie: `pending` can escape to the exact
state, but the old clauses never inspect its answer set. -/
def oldSound : RenderSix.SoundEvaluator6 future answer evaluate where
  exact_correct := by
    intro state value h
    cases state <;> cases value
    · cases h
    · exact ⟨rfl, fun other _ => by cases other; rfl⟩
  exact_final := by
    intro before after value hfuture hstatus
    cases before <;> cases after <;> cases value <;>
      simp [future, evaluate] at *
  absent_correct := by
    intro state h
    cases state <;> simp [evaluate] at h
  absent_final := by
    intro before after hfuture hstatus
    cases before <;> cases after <;> simp [evaluate] at *
  pending_escapable := by
    intro state h
    cases state
    · exact ⟨true, trivial, by simp [evaluate]⟩
    · simp [evaluate] at h

theorem pending_has_candidate :
    evaluate false = Status.pending ∧ answer false () = true :=
  ⟨rfl, rfl⟩

/-- The strengthened contract rejects the old-contract witness at exactly the
new pending-emptiness projection. -/
theorem not_total :
    ¬ StatusEffects.TotalSoundEvaluator6 future answer settled evaluate := by
  intro h
  exact Bool.noConfusion (h.pending_correct false rfl ())

end PendingCandidate

/-! ## Checked-report semantic projections and refusal -/

noncomputable def exactReport :
    ResultProgram.CheckedReport ResultProgram.evidenceProgram
      ResultProgram.evidenceCarrier :=
  ResultProgram.CheckedReport.renderAt ResultProgram.evidenceProgram
    ResultProgram.evidenceCarrier Evidence.exactW

theorem exact_report_projects_semantics :
    Evidence.values Evidence.exactW 47 = true
      ∧ Holes.SealsTo (Evidence.values Evidence.exactW) 47
      ∧ Evidence.Closed Evidence.exactW := by
  apply exactReport.exact_semantics
  exact (exactReport.says_iff _).2 ResultStatus.statusOf_exactW

theorem exact_report_refuses_pending :
    ¬ ResultProgram.evidenceCarrier.Says exactReport.output Status.pending := by
  apply exactReport.refuses_status_without_semantics Status.pending
  intro h
  have hfalse : Evidence.values Evidence.exactW 47 = false := by
    simpa [exactReport, ResultProgram.evidenceProgram,
      ResultProgram.CheckedReport.renderAt] using h.1 47
  rw [(Evidence.values_cand47 (e := Evidence.exactW) rfl).1] at hfalse
  exact Bool.noConfusion hfalse

/-! ## A generated-style exact snapshot declaration -/

abbrev SnapshotSchema : Preo.Expr.Schema := [.nat]

def snapshotProgram : Preo.Expr.Program SnapshotSchema where
  raw := .field 0
  success := rfl

def zeroEnv : Preo.Expr.Env SnapshotSchema :=
  .cons (t := .nat) (0 : Nat) .nil

def oneEnv : Preo.Expr.Env SnapshotSchema :=
  .cons (t := .nat) (1 : Nat) .nil

def snapshotDeclaration :=
  Preo.Incremental.TypedResult.declaration snapshotProgram
    "acceptance/snapshot" "acceptance/equality" "acceptance/inspectable" [zeroEnv]

def snapshotCarrier := RenderSix.stdCarrier6
  (Preo.Incremental.TypedResult.Future snapshotProgram) Nat

def snapshotReport : ResultProgram.ReachReport snapshotDeclaration snapshotCarrier :=
  ResultProgram.ReachReport.renderAt snapshotDeclaration snapshotCarrier zeroEnv
    (by exact List.Mem.head _)

/-- Typed derives inhabit only the exact snapshot row; no other cell is
claimed reachable by this adapter. -/
theorem typed_snapshot_is_exact :
    snapshotDeclaration.evaluate zeroEnv = Status.exact (snapshotProgram.eval zeroEnv)
      ∧ (snapshotDeclaration.evaluate zeroEnv).Semantics
        (snapshotDeclaration.answer zeroEnv) (snapshotDeclaration.settled zeroEnv) :=
  ⟨rfl, snapshotReport.semanticsAt⟩

theorem typed_snapshot_effect_supported :
    snapshotDeclaration.effect.Allows
      (StatusEffects.shapeOf (snapshotDeclaration.evaluate zeroEnv)) :=
  snapshotReport.effect_supports

theorem typed_snapshot_refuses_out_of_reach :
    ¬ ∃ r : ResultProgram.ReachReport snapshotDeclaration snapshotCarrier,
      r.checked.state = oneEnv := by
  apply ResultProgram.ReachReport.refuses_out_of_reach oneEnv
  change oneEnv ∉ [zeroEnv]
  simp [zeroEnv, oneEnv]

theorem typed_snapshot_refuses_named_resolution :
    ¬ ∃ r : ResultProgram.CheckedReport snapshotDeclaration snapshotCarrier,
      r.resolutionId = .named "pick" := by
  apply ResultProgram.CheckedReport.refuses_wrong_resolution
  simp [ResultProgram.resolutionIdentity]

/-! ## Authenticity is retained, never fabricated -/

def equalityBoundary : ResultProgram.ObservationBoundary
    (Preo.Expr.Env SnapshotSchema) (Preo.Expr.Env SnapshotSchema) where
  Authentic := Eq

def observedSnapshot : ResultProgram.ObservedReport equalityBoundary
    snapshotDeclaration snapshotCarrier :=
  ResultProgram.ObservedReport.attach equalityBoundary zeroEnv snapshotReport rfl

theorem observed_snapshot_authentic_site :
    equalityBoundary.Authentic observedSnapshot.world
      (snapshotCarrier.site observedSnapshot.report.checked.output) :=
  observedSnapshot.authentic_site

theorem observation_refuses_wrong_state :
    ¬ ∃ r : ResultProgram.ObservedReport equalityBoundary
        snapshotDeclaration snapshotCarrier,
      r.world = oneEnv ∧ r.report.checked.state = zeroEnv := by
  apply ResultProgram.ObservedReport.refuses_inauthentic oneEnv zeroEnv
  simp [equalityBoundary, zeroEnv, oneEnv]

end Uwueave.StatusSemanticsAcceptance
