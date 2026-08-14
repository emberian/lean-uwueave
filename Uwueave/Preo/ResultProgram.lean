/-
# Uwueave.Preo.ResultProgram — checked six-status programs and reports

`StatusEffects` supplies the six-way effect lattice and total semantic
soundness contract. `RenderSix` supplies an abstract report carrier. This file
joins them at a reusable Preoscript boundary: a declaration is indexed by the
future and resolution term it promises, owns an explicit finite reach, and
carries a proof of all six status clauses. Its inferred effect is therefore
both supported and least, rather than an author-written capability claim.

A `CheckedReport` is stronger than a bare `Carrier6.R`. It is tied to the
state actually evaluated, to that state's status, to the declaration's named
resolution mode, and to explicit visibility and per-value disclosure policy.
The exactness fields make a false site, visibility, or disclosure claim
refutable. This checks claims against the declared policy; as in
`HonestRender`, no proposition about pixel salience is inferred from it.

## Honest boundary

  * **External observation authenticity is supplied, not manufactured.**
    ⟨PREMISE U-0116 at the deployment observation boundary⟩
    `ObservationBoundary.Authentic` names the relation between an external
    world and the Lean state evaluated here. `ObservedReport.attach` requires a
    proof of that relation, `authentic_site` transports it to the carrier site,
    and `refuses_inauthentic` rejects a refuted pair. No constructor in this
    module observes a filesystem, network, device, or process and no theorem
    claims that a running deployment supplies the premise.
-/
import Uwueave.StatusEffects

namespace Uwueave.Preo.ResultProgram

open Uwueave Uwueave.Catalog
open Uwueave.ResultStatus (Status)

/-! ## Presentation and resolution identity -/

/-- Whether a result is inspectable at the presentation boundary. This is an
independent axis: it does not add a seventh semantic status. -/
inductive Visibility where
  | inspectable
  | opaque (reason : String)
  deriving DecidableEq, Repr

/-- An explicit decision for one possible answer branch. Hidden branches retain
a reason instead of disappearing behind a Boolean. -/
inductive Disclosure where
  | shown
  | hidden (reason : String)
  deriving DecidableEq, Repr

/-- Presentation policy is named and total. `disclosure s v` records a decision
for every value; consumers normally request it only with evidence that `v` is
an answer at `s`. -/
structure SurfacePolicy (S β : Type) where
  name : String
  visibility : S → Status β → Visibility
  disclosure : S → β → Disclosure

/-- Data-only identity of the resolution syntax. The policy function itself is
kept in the declaration's type index; this projection is safe to export. -/
inductive ResolutionIdentity where
  | preserveFork
  | named (name : String)
  deriving DecidableEq, Repr

def resolutionIdentity {S β : Type} : StatusEffects.Resolution S β →
    ResolutionIdentity
  | .preserveFork => .preserveFork
  | .byPolicy name _ => .named name

/-! ## Exact pure snapshots -/

/- Shared semantics for a pure query whose result is one exact value.  The
future-specific obligation is isolated to stability of the evaluator. -/
namespace ExactSnapshot

/-- The singleton answer computed by an exact snapshot evaluator. -/
def answer {S β : Type} [DecidableEq β] (eval : S → β) (state : S) : GSet β :=
  fun value => decide (value = eval state)

/-- A pure exact snapshot is settled at every state. -/
def settled {S β : Type} (_eval : S → β) (_state : S) : Prop := True

/-- A pure snapshot reports precisely its computed value. -/
def evaluate {S β : Type} (eval : S → β) (state : S) : Status β :=
  .exact (eval state)

/-- Complete six-status soundness for any evaluator stable under its authored
future.  Impossible non-exact rows are discharged once here rather than by
every typed snapshot adapter. -/
theorem totalSound {S β : Type} [DecidableEq β]
    (F : Evidence.Future S) (eval : S → β)
    (stable : ∀ before after, F before after → eval before = eval after) :
    StatusEffects.TotalSoundEvaluator6 F (answer eval) (settled eval)
      (evaluate eval) where
  core := {
    exact_correct := by
      intro state value h
      simp only [evaluate, Status.exact.injEq] at h
      subst value
      simp [answer, Holes.SealsTo]
    exact_final := by
      intro before after value hfuture h
      simp only [evaluate, Status.exact.injEq] at h ⊢
      exact (stable before after hfuture).symm.trans h
    absent_correct := by intro state h; simp [evaluate] at h
    absent_final := by intro before after hfuture h; simp [evaluate] at h
    pending_escapable := by intro state h; simp [evaluate] at h }
  exact_settled := by intro _ _ _; trivial
  provisional_correct := by intro state value h; simp [evaluate] at h
  forkedClosed_correct := by intro state h; simp [evaluate] at h
  forkedOpen_correct := by intro state h; simp [evaluate] at h
  absent_settled := by intro _ _; trivial
  pending_correct := by intro state h; simp [evaluate] at h
  pending_open := by intro state h; simp [evaluate] at h

end ExactSnapshot

/-! ## Checked declarations -/

/-- A reusable, checked result program.

The future and resolution term are indices, so a declaration cannot be moved
to another future or silently changed from fork-preserving to policy-resolved.
The remaining semantic functions are fields because the total soundness proof
must refer to exactly those functions. -/
structure CheckedDeclaration (S β : Type) (F : Evidence.Future S)
    (resolution : StatusEffects.Resolution S β) where
  name : String
  /-- Exportable identity for the future relation carried by the type index. -/
  futureId : String
  reach : List S
  answer : S → GSet β
  settled : S → Prop
  evaluate : S → Status β
  surface : SurfacePolicy S β
  totalSound : StatusEffects.TotalSoundEvaluator6 F answer settled evaluate

namespace CheckedDeclaration

variable {S β : Type} {F : Evidence.Future S}
  {resolution : StatusEffects.Resolution S β}

/-- Exact adapter to the existing query descriptor. -/
def descriptor (d : CheckedDeclaration S β F resolution) :
    StatusEffects.QueryDescriptor S β where
  answer := d.answer
  evaluate := d.evaluate
  resolution := resolution

@[simp] theorem descriptor_answer (d : CheckedDeclaration S β F resolution) :
    d.descriptor.answer = d.answer := rfl

@[simp] theorem descriptor_evaluate (d : CheckedDeclaration S β F resolution) :
    d.descriptor.evaluate = d.evaluate := rfl

@[simp] theorem descriptor_resolution (d : CheckedDeclaration S β F resolution) :
    d.descriptor.resolution = resolution := rfl

/-- The declaration's capability is inferred from its explicit finite reach. -/
def effect (d : CheckedDeclaration S β F resolution) : StatusEffects.Effect :=
  StatusEffects.infer d.reach d.evaluate

/-- Every evaluation in the declared finite reach is admitted. -/
theorem effect_supports (d : CheckedDeclaration S β F resolution) :
    StatusEffects.Supports d.effect d.reach d.evaluate :=
  StatusEffects.infer_sound d.reach d.evaluate

/-- No smaller six-status downset supports the declared finite reach. -/
theorem effect_least (d : CheckedDeclaration S β F resolution)
    (candidate : StatusEffects.Effect)
    (h : StatusEffects.Supports candidate d.reach d.evaluate) :
    d.effect ⊑ₑ candidate :=
  StatusEffects.infer_least h

/-- Exact characterization of an allowed inferred shape. -/
theorem effect_allows_iff (d : CheckedDeclaration S β F resolution)
    (shape : StatusEffects.Shape) :
    d.effect.Allows shape ↔
      ∃ s, s ∈ d.reach ∧ shape ⊑ₛ StatusEffects.shapeOf (d.evaluate s) :=
  Iff.rfl

/-- The computed status satisfies its complete semantic row at every state.
This is independent of finite-reach admission: reach controls the inferred
effect, while total soundness controls what each status means. -/
theorem semanticsAt (d : CheckedDeclaration S β F resolution) (state : S) :
    (d.evaluate state).Semantics (d.answer state) (d.settled state) :=
  d.totalSound.semanticsAt state

/-- The six-way soundness proof projects exactly to the historical renderer
contract when an older consumer needs it. -/
theorem rendererSound (d : CheckedDeclaration S β F resolution) :
    RenderSix.SoundEvaluator6 F d.answer d.evaluate :=
  d.totalSound.toSoundEvaluator6

/-- The sanctioned rendering function. Its state and computed status are the
same arguments passed to the carrier. -/
def renderer (d : CheckedDeclaration S β F resolution)
    (C : RenderSix.Carrier6 F β) : S → C.R :=
  fun s => C.report s (d.evaluate s)

theorem renderer_honest (d : CheckedDeclaration S β F resolution)
    (C : RenderSix.Carrier6 F β) :
    RenderSix.HonestRenderer6 F d.answer C (d.renderer C) :=
  RenderSix.soundEvaluator6_renders_honestly C d.rendererSound

end CheckedDeclaration

/-! ## Reports with exact site and presentation claims -/

/-- A report checked against one declaration.

Unlike a bare `Carrier6.R`, none of the identity or presentation claims is
trusted input: every stored claim is accompanied by equality to the declaration
and the state/status actually rendered. -/
structure CheckedReport {S β : Type} {F : Evidence.Future S}
    {resolution : StatusEffects.Resolution S β}
    (d : CheckedDeclaration S β F resolution)
    (C : RenderSix.Carrier6 F β) where
  state : S
  output : C.R
  rendered : output = C.report state (d.evaluate state)
  futureId : String
  future_exact : futureId = d.futureId
  resolutionId : ResolutionIdentity
  resolution_exact : resolutionId = resolutionIdentity resolution
  surfaceId : String
  surface_exact : surfaceId = d.surface.name
  visibility : Visibility
  visibility_exact : visibility = d.surface.visibility state (d.evaluate state)
  disclosure : β → Disclosure
  disclosure_exact : disclosure = d.surface.disclosure state

namespace CheckedReport

variable {S β : Type} {F : Evidence.Future S}
  {resolution : StatusEffects.Resolution S β}
  {d : CheckedDeclaration S β F resolution}
  {C : RenderSix.Carrier6 F β}

/-- The only constructor needed by a renderer: all checked fields are computed,
not accepted from an external claim. -/
def renderAt (d : CheckedDeclaration S β F resolution)
    (C : RenderSix.Carrier6 F β) (state : S) : CheckedReport d C where
  state := state
  output := C.report state (d.evaluate state)
  rendered := rfl
  futureId := d.futureId
  future_exact := rfl
  resolutionId := resolutionIdentity resolution
  resolution_exact := rfl
  surfaceId := d.surface.name
  surface_exact := rfl
  visibility := d.surface.visibility state (d.evaluate state)
  visibility_exact := rfl
  disclosure := d.surface.disclosure state
  disclosure_exact := rfl

/-- The report's carrier site is definitionally backed by its evaluated state. -/
theorem site_exact (r : CheckedReport d C) : C.site r.output = r.state := by
  rw [r.rendered, C.site_report]

/-- The report says exactly the status computed at its checked site. -/
theorem says_computed (r : CheckedReport d C) :
    C.Says r.output (d.evaluate r.state) := by
  rw [r.rendered]
  exact C.says_report _ _

/-- Exact status projection: a report says `status` iff that was the
declaration's evaluation at its checked site. -/
theorem says_iff (r : CheckedReport d C) (status : Status β) :
    C.Says r.output status ↔ d.evaluate r.state = status := by
  constructor
  · intro h
    exact C.says_functional r.output _ _ (says_computed r) h
  · intro h
    rw [← h]
    exact says_computed r

/-- The status computed for a checked report satisfies its semantic row. -/
theorem semanticsAt (r : CheckedReport d C) :
    (d.evaluate r.state).Semantics (d.answer r.state) (d.settled r.state) :=
  d.semanticsAt r.state

/-- Any status the carrier says for this report has the corresponding answer
and settledness semantics at the report's checked site. -/
theorem says_semantics (r : CheckedReport d C) {status : Status β}
    (h : C.Says r.output status) :
    status.Semantics (d.answer r.state) (d.settled r.state) := by
  rw [← (r.says_iff status).mp h]
  exact r.semanticsAt

/-- The exact row projects candidate membership, uniqueness, and settledness
without exposing either carrier representation or evaluator conditionals. -/
theorem exact_semantics (r : CheckedReport d C) {value : β}
    (h : C.Says r.output (Status.exact value)) :
    d.answer r.state value = true ∧ Holes.SealsTo (d.answer r.state) value
      ∧ d.settled r.state :=
  r.says_semantics h

/-- A semantically impossible status cannot be said by a checked report. -/
theorem refuses_status_without_semantics (r : CheckedReport d C)
    (status : Status β)
    (hnot : ¬ status.Semantics (d.answer r.state) (d.settled r.state)) :
    ¬ C.Says r.output status :=
  fun h => hnot (r.says_semantics h)

@[simp] theorem renderAt_site (d : CheckedDeclaration S β F resolution)
    (C : RenderSix.Carrier6 F β) (state : S) :
    C.site (renderAt d C state).output = state :=
  site_exact _

@[simp] theorem renderAt_resolution (d : CheckedDeclaration S β F resolution)
    (C : RenderSix.Carrier6 F β) (state : S) :
    (renderAt d C state).resolutionId = resolutionIdentity resolution := rfl

@[simp] theorem renderAt_future (d : CheckedDeclaration S β F resolution)
    (C : RenderSix.Carrier6 F β) (state : S) :
    (renderAt d C state).futureId = d.futureId := rfl

@[simp] theorem renderAt_surface (d : CheckedDeclaration S β F resolution)
    (C : RenderSix.Carrier6 F β) (state : S) :
    (renderAt d C state).surfaceId = d.surface.name := rfl

@[simp] theorem renderAt_visibility (d : CheckedDeclaration S β F resolution)
    (C : RenderSix.Carrier6 F β) (state : S) :
    (renderAt d C state).visibility =
      d.surface.visibility state (d.evaluate state) := rfl

@[simp] theorem renderAt_disclosure (d : CheckedDeclaration S β F resolution)
    (C : RenderSix.Carrier6 F β) (state : S) (value : β) :
    (renderAt d C state).disclosure value = d.surface.disclosure state value := rfl

/-- A report cannot be packaged under a site different from the state whose
status it actually rendered. -/
theorem refuses_wrong_site (state claimed : S) (hne : claimed ≠ state) :
    ¬ ∃ r : CheckedReport d C, r.state = state ∧ C.site r.output = claimed := by
  rintro ⟨r, hrs, hrclaim⟩
  apply hne
  rw [← hrs, ← site_exact r]
  exact hrclaim.symm

/-- A visibility claim that disagrees with the named surface policy is
uninhabitable. -/
theorem refuses_wrong_visibility (state : S) (claim : Visibility)
    (hne : claim ≠ d.surface.visibility state (d.evaluate state)) :
    ¬ ∃ r : CheckedReport d C, r.state = state ∧ r.visibility = claim := by
  rintro ⟨r, hrs, hrclaim⟩
  apply hne
  rw [← hrclaim, r.visibility_exact, hrs]

/-- A shown/hidden claim that disagrees with the named disclosure function at
the checked site is uninhabitable. -/
theorem refuses_wrong_disclosure (state : S) (value : β) (claim : Disclosure)
    (hne : claim ≠ d.surface.disclosure state value) :
    ¬ ∃ r : CheckedReport d C,
      r.state = state ∧ r.disclosure value = claim := by
  rintro ⟨r, hrs, hrclaim⟩
  apply hne
  rw [← hrclaim, r.disclosure_exact, hrs]

/-- A resolution identity different from the declaration's indexed resolution
cannot be attached to a checked report. -/
theorem refuses_wrong_resolution (claim : ResolutionIdentity)
    (hne : claim ≠ resolutionIdentity resolution) :
    ¬ ∃ r : CheckedReport d C, r.resolutionId = claim := by
  rintro ⟨r, hr⟩
  exact hne (hr ▸ r.resolution_exact)

end CheckedReport

/-! ## Finite-reach and observation adapters -/

/-- A checked report whose evaluated state belongs to the exact finite reach
used for effect inference. The proof is retained as data; no running reach is
discovered or inferred by this wrapper. -/
structure ReachReport {S β : Type} {F : Evidence.Future S}
    {resolution : StatusEffects.Resolution S β}
    (d : CheckedDeclaration S β F resolution)
    (C : RenderSix.Carrier6 F β) where
  checked : CheckedReport d C
  inReach : checked.state ∈ d.reach

namespace ReachReport

variable {S β : Type} {F : Evidence.Future S}
  {resolution : StatusEffects.Resolution S β}
  {d : CheckedDeclaration S β F resolution}
  {C : RenderSix.Carrier6 F β}

/-- Construct a reach-admitted report from an explicit membership proof. -/
def renderAt (d : CheckedDeclaration S β F resolution)
    (C : RenderSix.Carrier6 F β) (state : S) (inReach : state ∈ d.reach) :
    ReachReport d C where
  checked := CheckedReport.renderAt d C state
  inReach := inReach

/-- Reach admission preserves the complete semantics of the checked report. -/
theorem semanticsAt (r : ReachReport d C) :
    (d.evaluate r.checked.state).Semantics (d.answer r.checked.state)
      (d.settled r.checked.state) :=
  r.checked.semanticsAt

/-- The inferred effect admits the exact shape carried by every admitted
report, rather than relying on the caller to remember its reach proof. -/
theorem effect_supports (r : ReachReport d C) :
    d.effect.Allows (StatusEffects.shapeOf (d.evaluate r.checked.state)) :=
  d.effect_supports r.checked.state r.inReach

/-- No reach-admitted report can claim a state outside the authored reach. -/
theorem refuses_out_of_reach (state : S) (hnot : state ∉ d.reach) :
    ¬ ∃ r : ReachReport d C, r.checked.state = state := by
  rintro ⟨r, hr⟩
  exact hnot (hr ▸ r.inReach)

end ReachReport

/-- A runtime boundary supplies the proposition connecting an external world
observation to the Lean state used for evaluation. This interface does not
construct, trust, or authenticate such a witness by itself. -/
structure ObservationBoundary (World S : Type) where
  Authentic : World → S → Prop

/-- A reach-admitted checked report together with a caller-supplied proof that
its state authentically represents one external observation. -/
structure ObservedReport {World S β : Type} {F : Evidence.Future S}
    {resolution : StatusEffects.Resolution S β}
    (boundary : ObservationBoundary World S)
    (d : CheckedDeclaration S β F resolution)
    (C : RenderSix.Carrier6 F β) where
  world : World
  report : ReachReport d C
  authentic : boundary.Authentic world report.checked.state

namespace ObservedReport

variable {World S β : Type} {F : Evidence.Future S}
  {resolution : StatusEffects.Resolution S β}
  {boundary : ObservationBoundary World S}
  {d : CheckedDeclaration S β F resolution}
  {C : RenderSix.Carrier6 F β}

/-- Attach an authenticity proof supplied by the observation boundary. -/
def attach (boundary : ObservationBoundary World S) (world : World)
    (report : ReachReport d C)
    (authentic : boundary.Authentic world report.checked.state) :
    ObservedReport boundary d C where
  world := world
  report := report
  authentic := authentic

/-- The retained authenticity proof reaches the carrier site because the
checked report's site is exactly its evaluated state. -/
theorem authentic_site (r : ObservedReport boundary d C) :
    boundary.Authentic r.world (C.site r.report.checked.output) := by
  rw [r.report.checked.site_exact]
  exact r.authentic

/-- A boundary-refuted world/state pair cannot be packaged as observed. -/
theorem refuses_inauthentic (world : World) (state : S)
    (hnot : ¬ boundary.Authentic world state) :
    ¬ ∃ r : ObservedReport boundary d C,
      r.world = world ∧ r.report.checked.state = state := by
  rintro ⟨r, hw, hs⟩
  apply hnot
  rw [← hw, ← hs]
  exact r.authentic

end ObservedReport

/-! ## Executable theorem fixtures -/

abbrev EvidenceState := Evidence.ResultEvidence Holes.Val

def evidenceSurface : SurfacePolicy EvidenceState Holes.Val where
  name := "evidence/default"
  visibility := fun _ status =>
    match status with
    | .pending => .opaque "awaiting evidence"
    | _ => .inspectable
  disclosure := fun _ _ => .shown

noncomputable def evidenceProgram : CheckedDeclaration EvidenceState Holes.Val
    (Evidence.SealedFuture (α := Holes.Val)) (.preserveFork) where
  name := "evidence-status"
  futureId := "evidence/sealed"
  reach := [Evidence.openW, Evidence.forkedClosedW,
    ResultStatus.emptyClosedW, ResultStatus.emptyOpenW]
  answer := Evidence.values
  settled := Evidence.Closed
  evaluate := ResultStatus.statusOf
  surface := evidenceSurface
  totalSound := StatusEffects.statusOf_totalSound6

/-- The reusable declaration simultaneously witnesses total six-way soundness
and a least finite effect. -/
theorem evidence_program_checked :
    StatusEffects.TotalSoundEvaluator6
        (Evidence.SealedFuture (α := Holes.Val)) Evidence.values Evidence.Closed
        ResultStatus.statusOf
      ∧ StatusEffects.Supports evidenceProgram.effect evidenceProgram.reach
          evidenceProgram.evaluate
      ∧ ∀ candidate, StatusEffects.Supports candidate evidenceProgram.reach
          evidenceProgram.evaluate → evidenceProgram.effect ⊑ₑ candidate :=
  ⟨evidenceProgram.totalSound, evidenceProgram.effect_supports,
    fun candidate h => evidenceProgram.effect_least candidate h⟩

def evidenceCarrier : RenderSix.Carrier6
    (Evidence.SealedFuture (α := Holes.Val)) Holes.Val :=
  RenderSix.stdCarrier6 _ _

noncomputable def openReport : CheckedReport evidenceProgram evidenceCarrier :=
  CheckedReport.renderAt evidenceProgram evidenceCarrier Evidence.openW

theorem open_report_exact_projections :
    evidenceCarrier.site openReport.output = Evidence.openW
      ∧ evidenceCarrier.Says openReport.output (Status.provisional 47)
      ∧ openReport.futureId = "evidence/sealed"
      ∧ openReport.resolutionId = .preserveFork
      ∧ openReport.surfaceId = "evidence/default"
      ∧ openReport.visibility = .inspectable
      ∧ openReport.disclosure 47 = .shown := by
  refine ⟨openReport.site_exact, ?_, rfl, rfl, rfl, ?_, rfl⟩
  exact (openReport.says_iff _).mpr ResultStatus.statusOf_openW
  simp [openReport, CheckedReport.renderAt, evidenceProgram, evidenceSurface,
    ResultStatus.statusOf_openW]

/-- Concrete falsifiability: the open report cannot claim to have evaluated a
different evidence state. -/
theorem open_report_refuses_lie_about_site :
    ¬ ∃ r : CheckedReport evidenceProgram evidenceCarrier,
      r.state = Evidence.openW ∧
        evidenceCarrier.site r.output = Evidence.forkedClosedW := by
  apply CheckedReport.refuses_wrong_site
  intro h
  exact Evidence.not_closed_openW
    (h ▸ Evidence.closed_forkedClosedW)

/-- Concrete falsifiability: the same report cannot replace the policy's
inspectable decision with an opaque claim. -/
theorem open_report_refuses_lie_about_visibility :
    ¬ ∃ r : CheckedReport evidenceProgram evidenceCarrier,
      r.state = Evidence.openW ∧ r.visibility = .opaque "hidden" := by
  apply CheckedReport.refuses_wrong_visibility
  simp [evidenceProgram, evidenceSurface, ResultStatus.statusOf_openW]

/-- Concrete falsifiability: it cannot claim a hidden branch where the named
policy records that branch as shown. -/
theorem open_report_refuses_lie_about_disclosure :
    ¬ ∃ r : CheckedReport evidenceProgram evidenceCarrier,
      r.state = Evidence.openW ∧ r.disclosure 47 = .hidden "suppressed" := by
  apply CheckedReport.refuses_wrong_disclosure
  simp [evidenceProgram, evidenceSurface]

end Uwueave.Preo.ResultProgram
