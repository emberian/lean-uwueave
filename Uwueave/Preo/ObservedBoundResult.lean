/-
# Uwueave.Preo.ObservedBoundResult — authenticated running observations

`StateProgram` has an authored analysis reach and `BoundResult` binds that
declaration to an exact named world future.  Neither one discovers what a
running deployment observed.  This module adds only a proof adapter: a caller
must supply an `ObservationBoundary.Authentic` witness, membership in a
separately supplied running reach, membership in the authored world reach, and
an exact world-indexed certificate.

No definition here reads a process, network, filesystem, clock, or device.  In
particular, the adapter never equates authored reach with running reach and
never constructs the authenticity premise it retains.
-/
import Uwueave.Preo.BoundResult

namespace Uwueave.Preo.ObservedBoundResult

open Uwueave

variable {M : Future.WorldModel} {State β : Type}
  {stateFuture : Evidence.Future State}
  {resolution : StatusEffects.Resolution State β}
  {future : Future.FutureDecl M}
  {source : ResultProgram.CheckedDeclaration State β stateFuture resolution}

/-- The state-level carrier used by the observed side of the adapter. -/
def sourceCarrier : RenderSix.Carrier6 stateFuture β :=
  RenderSix.stdCarrier6 stateFuture β

/-- Per-world evidence that one exact world belongs to both independent
scopes.  This does not claim either list includes or equals the other. -/
structure RunningReachBridge
    (binding : BoundResult.WorldBinding future source)
    (runningReach : List M.World) (index : Future.WorldIndex M) where
  inRunning : index.world ∈ runningReach
  inAuthored : index.world ∈ binding.worldReach

/-- An observed state report and a certificate-gated world report aligned at
one exact world index.

`observed` retains the caller's authenticity proof at the source state;
`certified` retains the exact future, declaration answer, certificate, world
index, and authored world-reach proof. -/
structure ObservedCertifiedReport
    (boundary : ResultProgram.ObservationBoundary M.World State)
    (binding : BoundResult.WorldBinding future source)
    (runningReach : List M.World)
    {K : Type} (key : M.World → K) (C : K → Prop)
    (index : Future.WorldIndex M) where
  reach : RunningReachBridge binding runningReach index
  certified : BoundResult.WorldBinding.CertifiedReport binding key C index
  observed : ResultProgram.ObservedReport boundary source sourceCarrier
  observed_world_exact : observed.world = index.world
  observed_state_exact :
    observed.report.checked.state = binding.worldToState index.world

/-- Attach an observed and certified report only when every premise names the
same exact world, projected state, future declaration, and answer function. -/
def attachAtWorld
    (boundary : ResultProgram.ObservationBoundary M.World State)
    (binding : BoundResult.WorldBinding future source)
    (runningReach : List M.World)
    {K : Type} {key : M.World → K} {C : K → Prop}
    (index : Future.WorldIndex M)
    (observation : boundary.Authentic index.world
      (binding.worldToState index.world))
    (inRunning : index.world ∈ runningReach)
    (inAuthored : index.world ∈ binding.worldReach)
    (certificate : Future.CheckedCertificate future
      binding.declaration.answer key C index) :
    ObservedCertifiedReport boundary binding runningReach key C index := by
  let stateReport : ResultProgram.ReachReport source sourceCarrier :=
    ResultProgram.ReachReport.renderAt source sourceCarrier
      (binding.worldToState index.world)
      (binding.projectsReach index.world inAuthored)
  let observed : ResultProgram.ObservedReport boundary source sourceCarrier :=
    ResultProgram.ObservedReport.attach boundary index.world stateReport observation
  exact {
    reach := ⟨inRunning, inAuthored⟩
    certified := binding.certifiedReportAtWorld index certificate inAuthored
    observed := observed
    observed_world_exact := rfl
    observed_state_exact := rfl }

namespace ObservedCertifiedReport

variable {boundary : ResultProgram.ObservationBoundary M.World State}
  {bound : BoundResult.WorldBinding future source}
  {runningReach : List M.World}
  {K : Type} {key : M.World → K} {C : K → Prop}
  {expectedIndex : Future.WorldIndex M}

/-- Stable projection for consumers which retain the exact binding. -/
def binding (_report : ObservedCertifiedReport boundary bound runningReach key C
    expectedIndex) : BoundResult.WorldBinding future source := bound

/-- Stable projection for consumers which retain the exact world index. -/
def index (_report : ObservedCertifiedReport boundary bound runningReach key C
    expectedIndex) : Future.WorldIndex M := expectedIndex

/-- The exact observed world. -/
def world (report : ObservedCertifiedReport boundary bound runningReach key C
    expectedIndex) : M.World := report.index.world

/-- The exact application state evaluated for the observed report. -/
def state (report : ObservedCertifiedReport boundary bound runningReach key C
    expectedIndex) : State := report.binding.worldToState report.world

/-- Existing V3 and result consumers can consume the exact certified report
without reconstructing any index or certificate equality. -/
def report (observed : ObservedCertifiedReport boundary bound runningReach key C
    expectedIndex) :
    BoundResult.WorldBinding.CertifiedReport bound key C expectedIndex :=
  observed.certified

/-- Exact certificate projection; its answer is definitionally the bound
declaration's answer. -/
def certificate
    (observed : ObservedCertifiedReport boundary bound runningReach key C
      expectedIndex) :
    Future.CheckedCertificate future bound.declaration.answer key C expectedIndex :=
  observed.certified.certificate

/-- The caller-supplied observation proof, transported through the stored exact
world and state equalities. -/
theorem observation
    (report : ObservedCertifiedReport boundary bound runningReach key C
      expectedIndex) :
    boundary.Authentic report.world report.state := by
  have stateExact : report.observed.report.checked.state = report.state := by
    simpa only [state, binding, world, index] using report.observed_state_exact
  have worldExact : report.observed.world = report.world := by
    simpa only [world, index] using report.observed_world_exact
  rw [← worldExact, ← stateExact]
  exact report.observed.authentic

/-- Running reach, authored reach, observation, report site, and certificate
index all align at the same exact world and projected state. -/
theorem exact_alignment
    (report : ObservedCertifiedReport boundary bound runningReach key C
      expectedIndex) :
    report.world ∈ runningReach
      ∧ report.world ∈ bound.worldReach
      ∧ boundary.Authentic report.world report.state
      ∧ report.certified.report.checked.state = report.world
      ∧ report.observed.report.checked.state = report.state := by
  refine ⟨report.reach.inRunning, report.reach.inAuthored, report.observation,
    ?_, ?_⟩
  · exact report.certified.world_exact
  · simpa only [state, binding, world, index] using report.observed_state_exact

/-- A state refuted by the supplied observation boundary cannot be substituted
for the exact projected state. -/
theorem refuses_forged_state
    (report : ObservedCertifiedReport boundary bound runningReach key C
      expectedIndex)
    (claimed : State) (refuted : ¬ boundary.Authentic report.world claimed) :
    ¬ report.state = claimed := by
  intro exact
  apply refuted
  rw [← exact]
  exact report.observation

/-- A world refuted by the supplied observation boundary cannot be substituted
for the exact retained world. -/
theorem refuses_forged_world
    (report : ObservedCertifiedReport boundary bound runningReach key C
      expectedIndex)
    (claimed : M.World) (refuted : ¬ boundary.Authentic claimed report.state) :
    ¬ report.world = claimed := by
  intro exact
  apply refuted
  rw [← exact]
  exact report.observation

/-- A report and certificate at the retained index cannot be reused at a stale
or otherwise distinct world index, even if state projection later collides. -/
theorem refuses_stale_index
    (report : ObservedCertifiedReport boundary bound runningReach key C
      expectedIndex)
    (stale : Future.WorldIndex M) (different : stale.world ≠ report.world) :
    ¬ report.certified.report.checked.state = stale.world := by
  apply report.certified.refuses_different_world stale
  simpa only [world, index] using different

end ObservedCertifiedReport

/-- A world excluded from the separately supplied running reach cannot produce
an observed certified report, even when it belongs to the authored reach. -/
theorem refuses_out_of_running_reach
    (boundary : ResultProgram.ObservationBoundary M.World State)
    (binding : BoundResult.WorldBinding future source)
    (runningReach : List M.World)
    {K : Type} (key : M.World → K) (C : K → Prop)
    (index : Future.WorldIndex M) (outside : index.world ∉ runningReach) :
    ¬ Nonempty
      (ObservedCertifiedReport boundary binding runningReach key C index) := by
  rintro ⟨report⟩
  exact outside report.reach.inRunning

end Uwueave.Preo.ObservedBoundResult
