/-
# Uwueave.Preo.BoundResult — exact world/future bindings for checked results

A state-level checked declaration does not determine a deployment future.  This
module therefore binds it to an existing named `FutureDecl` only when the caller
supplies an explicit world-to-state projection, an authored world reach, and a
fresh six-status soundness proof over that exact world relation.

Certificate-gated reports retain the exact `WorldIndex` and
`CheckedCertificate` used to construct them.  In particular, equality of two
projected states is not enough to reuse a report or certificate at another
world, and no equality relation is relabelled as delivery or extension.
-/
import Uwueave.Preo.Future
import Uwueave.Preo.StateProgram

namespace Uwueave.Preo.BoundResult

open Uwueave

/-- Precompose an explicitly authored resolution policy with a world-to-state
projection.  The resolution constructor and its name are retained exactly. -/
def liftResolution {World State β : Type} (project : World → State) :
    StatusEffects.Resolution State β → StatusEffects.Resolution World β
  | .preserveFork => .preserveFork
  | .byPolicy name policy => .byPolicy name (fun world => policy (project world))

/-- Precompose presentation decisions with the same explicit projection. -/
def liftSurface {World State β : Type} (project : World → State)
    (surface : ResultProgram.SurfacePolicy State β) :
    ResultProgram.SurfacePolicy World β where
  name := surface.name
  visibility := fun world status => surface.visibility (project world) status
  disclosure := fun world value => surface.disclosure (project world) value

@[simp] theorem liftResolution_identity {World State β : Type}
    (project : World → State) (resolution : StatusEffects.Resolution State β) :
    ResultProgram.resolutionIdentity (liftResolution project resolution) =
      ResultProgram.resolutionIdentity resolution := by
  cases resolution <;> rfl

/-- A checked state declaration bound to one exact named world future.

`worldSound` is intentionally a field rather than an inferred consequence of
the source declaration: a state future generally forgets pool, frontier, and
epoch facts needed to justify a world future. -/
structure WorldBinding {M : Future.WorldModel} {State β : Type}
    {stateFuture : Evidence.Future State}
    {resolution : StatusEffects.Resolution State β}
    (future : Future.FutureDecl M)
    (source : ResultProgram.CheckedDeclaration State β stateFuture resolution) where
  worldToState : M.World → State
  worldReach : List M.World
  projectsReach : ∀ world, world ∈ worldReach → worldToState world ∈ source.reach
  worldSound : StatusEffects.TotalSoundEvaluator6 future.future
    (fun world => source.answer (worldToState world))
    (fun world => source.settled (worldToState world))
    (fun world => source.evaluate (worldToState world))

namespace WorldBinding

variable {M : Future.WorldModel} {State β : Type}
  {stateFuture : Evidence.Future State}
  {resolution : StatusEffects.Resolution State β}
  {future : Future.FutureDecl M}
  {source : ResultProgram.CheckedDeclaration State β stateFuture resolution}

/-- The genuinely world-indexed declaration.  Its future type is exactly the
relation in `future`; its exported identity is exactly `future.name`. -/
def declaration (binding : WorldBinding future source) :
    ResultProgram.CheckedDeclaration M.World β future.future
      (liftResolution binding.worldToState resolution) where
  name := source.name
  futureId := future.name
  reach := binding.worldReach
  answer := fun world => source.answer (binding.worldToState world)
  settled := fun world => source.settled (binding.worldToState world)
  evaluate := fun world => source.evaluate (binding.worldToState world)
  surface := liftSurface binding.worldToState source.surface
  totalSound := binding.worldSound

/-- The reference carrier at world sites, indexed by the same exact future. -/
def carrier (binding : WorldBinding future source) :
    RenderSix.Carrier6 future.future β :=
  let _soundnessWitness := binding.worldSound
  RenderSix.stdCarrier6 future.future β

@[simp] theorem declaration_futureId (binding : WorldBinding future source) :
    binding.declaration.futureId = future.name := rfl

@[simp] theorem declaration_reach (binding : WorldBinding future source) :
    binding.declaration.reach = binding.worldReach := rfl

@[simp] theorem declaration_evaluate (binding : WorldBinding future source)
    (world : M.World) :
    binding.declaration.evaluate world =
      source.evaluate (binding.worldToState world) := rfl

/-- Report only at the exact world stored by an index and admitted by the
authored world reach. -/
def reportAtWorld (binding : WorldBinding future source)
    (index : Future.WorldIndex M) (inReach : index.world ∈ binding.worldReach) :
    ResultProgram.ReachReport binding.declaration binding.carrier :=
  ResultProgram.ReachReport.renderAt binding.declaration binding.carrier
    index.world inReach

@[simp] theorem reportAtWorld_state (binding : WorldBinding future source)
    (index : Future.WorldIndex M) (inReach : index.world ∈ binding.worldReach) :
    (binding.reportAtWorld index inReach).checked.state = index.world := rfl

/-- A certificate-gated report retains the certificate, its exact world index,
and an equality tying that index to the checked report site. -/
structure CertifiedReport (binding : WorldBinding future source)
    {K : Type} (key : M.World → K) (C : K → Prop)
    (index : Future.WorldIndex M) where
  certificate : Future.CheckedCertificate future binding.declaration.answer key C index
  report : ResultProgram.ReachReport binding.declaration binding.carrier
  world_exact : report.checked.state = index.world

/-- The only ordinary constructor: both reach and certificate evidence must be
supplied for the same exact `WorldIndex`. -/
def certifiedReportAtWorld (binding : WorldBinding future source)
    {K : Type} {key : M.World → K} {C : K → Prop}
    (index : Future.WorldIndex M)
    (certificate : Future.CheckedCertificate future binding.declaration.answer key C index)
    (inReach : index.world ∈ binding.worldReach) :
    CertifiedReport binding key C index where
  certificate := certificate
  report := binding.reportAtWorld index inReach
  world_exact := rfl

namespace CertifiedReport

variable {binding : WorldBinding future source}
  {K : Type} {key : M.World → K} {C : K → Prop}
  {index : Future.WorldIndex M}

/-- Acceptance check: the retained certificate is definitionally about the
same answer function used by the world-indexed checked declaration. -/
theorem certificate_answers_declaration
    (report : CertifiedReport binding key C index) :
    Future.CheckedCertificate future binding.declaration.answer key C index :=
  report.certificate

/-- Certificate gating retains admission to the exact authored world reach. -/
theorem index_mem (report : CertifiedReport binding key C index) :
    index.world ∈ binding.worldReach := by
  rw [← report.world_exact]
  exact report.report.inReach

/-- A report certified at one world cannot be reused at a distinct world even
when both worlds project to the same application state. -/
theorem refuses_different_world (report : CertifiedReport binding key C index)
    (claimed : Future.WorldIndex M) (different : claimed.world ≠ index.world) :
    ¬ report.report.checked.state = claimed.world := by
  intro h
  exact different (h.symm.trans report.world_exact)

/-- The value-erased status is computed from the exact world-indexed
declaration, never accepted as caller metadata. -/
def statusShape (report : CertifiedReport binding key C index) :
    StatusEffects.Shape :=
  StatusEffects.shapeOf
    (binding.declaration.evaluate report.report.checked.state)

@[simp] theorem statusShape_exact_world
    (report : CertifiedReport binding key C index) :
    report.statusShape =
      StatusEffects.shapeOf (binding.declaration.evaluate index.world) := by
  simp only [statusShape, report.world_exact]

/-- Selection of a disclosure branch is available only with an exact-status
witness naming the selected value.  Non-value and fork statuses provide no
such scalar branch. -/
structure ExactBranch (report : CertifiedReport binding key C index) where
  value : β
  isExact : binding.declaration.evaluate index.world = .exact value

namespace ExactBranch

variable {report : CertifiedReport binding key C index}

/-- The exact branch is also what the checked carrier says at its retained
world site. -/
theorem says (branch : ExactBranch report) :
    binding.carrier.Says report.report.checked.output (.exact branch.value) := by
  apply (report.report.checked.says_iff _).mpr
  rw [report.world_exact]
  exact branch.isExact

/-- Disclosure is obtained by applying the checked report's total policy to
the proof-selected exact value; it is not a free scalar claim. -/
def disclosure (branch : ExactBranch report) : ResultProgram.Disclosure :=
  report.report.checked.disclosure branch.value

@[simp] theorem disclosure_exact (branch : ExactBranch report) :
    branch.disclosure =
      binding.declaration.surface.disclosure index.world branch.value := by
  simp only [disclosure, report.report.checked.disclosure_exact,
    report.world_exact]

end ExactBranch

end CertifiedReport

/-- Refutation check for answer relabelling.  A certificate for a genuinely
different answer function may exist, but it cannot be paired with the equality
needed to pass the exact report gate. -/
theorem refuses_wrong_certificate_answer (binding : WorldBinding future source)
    {K : Type} {key : M.World → K} {C : K → Prop}
    (index : Future.WorldIndex M)
    (wrongAnswer : M.World → Uwueave.Catalog.GSet β)
    (different : wrongAnswer ≠ binding.declaration.answer) :
    ¬ (Future.CheckedCertificate future wrongAnswer key C index ∧
      wrongAnswer = binding.declaration.answer) := by
  rintro ⟨_, exact⟩
  exact different exact

/-- No reach report can be manufactured for a world excluded from the exact
authored world reach. -/
theorem refuses_out_of_world_reach (binding : WorldBinding future source)
    (index : Future.WorldIndex M) (outside : index.world ∉ binding.worldReach) :
    ¬ ∃ report : ResultProgram.ReachReport binding.declaration binding.carrier,
      report.checked.state = index.world := by
  intro h
  obtain ⟨report, exact⟩ := h
  have member : report.checked.state ∈ binding.worldReach := by
    simpa only [declaration_reach] using report.inReach
  exact outside (exact ▸ member)

end WorldBinding
end Uwueave.Preo.BoundResult
