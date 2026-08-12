/-
# Uwueave.Preo.ArtifactV3Checked — proof-indexed V3 row builders

This is the one-way bridge from the checked typed-query layer to neutral V3
rows.  Public row builders consume `StateProgram` or `BoundResult` values; no
decoded row is promoted back into either source and no semantic proof is
reconstructed from first-order metadata.
-/
import Uwueave.Preo.ArtifactV3Data
import Uwueave.Preo.ArtifactChecked
import Uwueave.Preo.BoundResult

namespace Uwueave.Preo.ArtifactV3

open Uwueave
open Uwueave.Preo
open Uwueave.Preo.Artifact

set_option autoImplicit false

/-! ## Checked typed-query projection -/

/-- Stable identities authored for one exact checked state program.  The
program remains a type index; callers cannot reuse this handle for a different
program. -/
structure CheckedQuery {State : Type} {Γ : Expr.Schema}
    (base : Artifact.Artifact) (source : StateProgram State Γ) where private mk ::
  id : QueryId
  schema : SchemaId
  result : ResultId
  program : ProgramId
  fieldId : Nat → FieldId
  fieldId_mem : ∀ n, n ∈ source.program.reads →
    base.fields.any (fun field => field.id == fieldId n) = true

/-- Bind stable identities to the exact checked program.  `fieldId` is an
authoritative schema-position map, not an inferred hash. -/
def CheckedQuery.ofStateProgram {State : Type} {Γ : Expr.Schema}
    (base : Artifact.Artifact) (source : StateProgram State Γ)
    (id : QueryId) (schema : SchemaId) (result : ResultId) (program : ProgramId)
    (fieldId : Nat → FieldId)
    (fieldId_mem : ∀ n, n ∈ source.program.reads →
      base.fields.any (fun field => field.id == fieldId n) = true) :
    CheckedQuery base source :=
  ⟨id, schema, result, program, fieldId, fieldId_mem⟩

private def HoleKind.ofExpr : Expr.HoleKind → HoleKind
  | .field => .field
  | .opaque => .opaque

private def HoleRow.ofExpr (fieldId : Nat → FieldId) (hole : Expr.Hole) : HoleRow :=
  ⟨hole.path, fieldId hole.field, HoleKind.ofExpr hole.kind⟩

/-- Positive tags are emitted only by pattern matching on the actual
proof-producing analyses stored behind `Expr.Program`. -/
private def analysesOf {Γ : Expr.Schema} (program : Expr.Program Γ) :
    List AnalysisTag :=
  let merge := match program.mergeSafe? with
    | some _ => [.mergeSafe]
    | none => []
  let monotone := match program.monotoneSafe? with
    | some _ => [.monotoneSafe]
    | none => []
  merge ++ monotone

def CheckedQuery.toRow {State : Type} {Γ : Expr.Schema}
    {base : Artifact.Artifact} {source : StateProgram State Γ}
    (checked : CheckedQuery base source) : QueryRow where
  id := checked.id
  schema := checked.schema
  result := checked.result
  program := checked.program
  reads := source.program.reads.map checked.fieldId
  holes := source.program.holes.map (HoleRow.ofExpr checked.fieldId)
  analyses := analysesOf source.program

@[simp] theorem CheckedQuery.toRow_reads {State : Type} {Γ : Expr.Schema}
    {base : Artifact.Artifact} {source : StateProgram State Γ}
    (checked : CheckedQuery base source) :
    checked.toRow.reads = source.program.reads.map checked.fieldId := rfl

@[simp] theorem CheckedQuery.toRow_holes {State : Type} {Γ : Expr.Schema}
    {base : Artifact.Artifact} {source : StateProgram State Γ}
    (checked : CheckedQuery base source) :
    checked.toRow.holes = source.program.holes.map (HoleRow.ofExpr checked.fieldId) := rfl

/-! ## Append-only aggregate builders -/

/-- Appending a row under the checked builder's ordering premise preserves the
strictly-increasing stable-ID invariant required by V3 validation. -/
theorem append_preserves_strictIds {alpha : Type} (id : alpha → Nat)
    (rows : List alpha) (row : alpha)
    (prior : rows.Pairwise fun left right => id left < id right)
    (ordered : ∀ previous ∈ rows, id previous < id row) :
    (rows ++ [row]).Pairwise fun left right => id left < id right := by
  apply List.pairwise_append.mpr
  refine ⟨prior, by simp, ?_⟩
  intro previous previousMem current currentMem
  simp only [List.mem_singleton] at currentMem
  subst current
  exact ordered previous previousMem

/-- Begin a V3 aggregate from an unchanged V2 checked artifact projection. -/
def ArtifactV3Encoding.ofArtifact (base : Artifact.Artifact) (schema : SchemaId) :
    ArtifactV3Encoding :=
  ⟨base.canonicalEncoding, schema, [], [], [], []⟩

def ArtifactV3Encoding.addQuery {State : Type} {Γ : Expr.Schema}
    {base : Artifact.Artifact} {source : StateProgram State Γ}
    (encoding : ArtifactV3Encoding) (query : CheckedQuery base source)
    (_base_exact : encoding.base = base.canonicalEncoding)
    (_schema_exact : encoding.schema = query.schema)
    (_id_ordered : ∀ previous ∈ encoding.queries,
      previous.id.value < query.id.value) : ArtifactV3Encoding :=
  { encoding with queries := encoding.queries ++ [query.toRow] }

/-- The checked query's authored stable mapping lands in the exact checked
base for every proof-derived read. -/
theorem CheckedQuery.read_field_mem {State : Type} {Γ : Expr.Schema}
    {base : Artifact.Artifact} {source : StateProgram State Γ}
    (checked : CheckedQuery base source) {n : Nat}
    (read : n ∈ source.program.reads) :
    base.fields.any (fun field => field.id == checked.fieldId n) = true :=
  checked.fieldId_mem n read

/-! ## Checked world, policy, result, and certificate projection -/

/-- Stable identity tied to one exact `WorldIndex`. -/
structure CheckedWorld {M : Future.WorldModel} (index : Future.WorldIndex M)
    where private mk ::
  id : WorldId

def CheckedWorld.ofWorldIndex {M : Future.WorldModel} (index : Future.WorldIndex M)
    (id : WorldId) : CheckedWorld index :=
  ⟨id⟩

/-- First-order resolution identity computed from the exact resolution syntax.
The callback assigns stable IDs only to already-retained policy names. -/
structure CheckedResolution {State β : Type}
    (resolution : StatusEffects.Resolution State β) where private mk ::
  row : ResolutionRow

def CheckedResolution.ofResolution {State β : Type}
    (resolution : StatusEffects.Resolution State β)
    (namedId : String → ResolutionId) : CheckedResolution resolution :=
  ⟨match resolution with
    | .preserveFork => .preserveFork
    | .byPolicy name _ => .named (namedId name)⟩

/-- Stable surface identity and reason-name mapping tied to one exact checked
surface policy.  No visibility or disclosure decision is accepted here. -/
structure CheckedSurface {State β : Type}
    (surface : ResultProgram.SurfacePolicy State β) where private mk ::
  id : SurfaceId
  reasonId : String → ReasonId

def CheckedSurface.ofPolicy {State β : Type}
    (surface : ResultProgram.SurfacePolicy State β) (id : SurfaceId)
    (reasonId : String → ReasonId) : CheckedSurface surface :=
  ⟨id, reasonId⟩

private def StatusShape.ofStatusEffects : StatusEffects.Shape → StatusShape
  | .exact => .exact
  | .provisional => .provisional
  | .forkedClosed => .forkedClosed
  | .forkedOpen => .forkedOpen
  | .absent => .absent
  | .pending => .pending

private def StatusShape.toStatusEffects : StatusShape → StatusEffects.Shape
  | .exact => .exact
  | .provisional => .provisional
  | .forkedClosed => .forkedClosed
  | .forkedOpen => .forkedOpen
  | .absent => .absent
  | .pending => .pending

private def canonicalStatusShapes : List StatusShape :=
  [.exact, .provisional, .forkedClosed, .forkedOpen, .absent, .pending]

private def statusRefines : StatusShape → StatusShape → Bool
  | .exact, _ => true
  | .provisional, .provisional | .provisional, .pending
  | .provisional, .forkedOpen => true
  | .forkedClosed, .forkedClosed | .forkedClosed, .forkedOpen => true
  | .forkedOpen, .forkedOpen => true
  | .absent, .absent | .absent, .pending => true
  | .pending, .pending => true
  | _, _ => false

/-- Canonical six-shape downset computed from the exact checked declaration's
finite reach.  Callers never supply an effect list. -/
private def effectOfDeclaration {S β : Type} {F : Evidence.Future S}
    {resolution : StatusEffects.Resolution S β}
    (declaration : ResultProgram.CheckedDeclaration S β F resolution) :
    List StatusShape :=
  let observed := declaration.reach.map fun state =>
    StatusShape.ofStatusEffects (StatusEffects.shapeOf (declaration.evaluate state))
  canonicalStatusShapes.filter fun candidate =>
    observed.any fun shape => statusRefines candidate shape

private theorem statusRefines_eq_true_iff (left right : StatusShape) :
    statusRefines left right = true ↔
      StatusEffects.Refines left.toStatusEffects right.toStatusEffects := by
  cases left <;> cases right <;>
    simp [statusRefines, StatusShape.toStatusEffects, StatusEffects.Refines]

private theorem statusShape_roundtrip (shape : StatusEffects.Shape) :
    (StatusShape.ofStatusEffects shape).toStatusEffects = shape := by
  cases shape <;> rfl

/-- The computed list is exactly the semantic effect of the checked
declaration, represented in canonical six-shape order. -/
theorem mem_effectOfDeclaration_iff {S β : Type} {F : Evidence.Future S}
    {resolution : StatusEffects.Resolution S β}
    (declaration : ResultProgram.CheckedDeclaration S β F resolution)
    (shape : StatusShape) :
    shape ∈ effectOfDeclaration declaration ↔
      declaration.effect.Allows shape.toStatusEffects := by
  unfold effectOfDeclaration
  rw [List.mem_filter]
  have canonical : shape ∈ canonicalStatusShapes := by
    cases shape <;> decide
  simp only [canonical, true_and, List.any_eq_true]
  change
    (∃ observed,
      observed ∈ declaration.reach.map (fun state =>
        StatusShape.ofStatusEffects
          (StatusEffects.shapeOf (declaration.evaluate state))) ∧
      statusRefines shape observed = true) ↔
    ∃ state, state ∈ declaration.reach ∧
      StatusEffects.Refines shape.toStatusEffects
        (StatusEffects.shapeOf (declaration.evaluate state))
  constructor
  · rintro ⟨observed, observedMem, refines⟩
    rw [List.mem_map] at observedMem
    obtain ⟨state, stateMem, rfl⟩ := observedMem
    refine ⟨state, stateMem, ?_⟩
    simpa only [statusShape_roundtrip] using
      (statusRefines_eq_true_iff _ _).mp refines
  · rintro ⟨state, stateMem, refines⟩
    refine ⟨StatusShape.ofStatusEffects
      (StatusEffects.shapeOf (declaration.evaluate state)), ?_, ?_⟩
    · exact List.mem_map.mpr ⟨state, stateMem, rfl⟩
    · apply (statusRefines_eq_true_iff _ _).mpr
      simpa [statusShape_roundtrip] using refines

private def VisibilityRow.ofResultProgram (reasonId : String → ReasonId) :
    ResultProgram.Visibility → VisibilityRow
  | .inspectable => .inspectable
  | .opaque reason => .opaque (reasonId reason)

private def DisclosureRow.ofResultProgram (reasonId : String → ReasonId) :
    ResultProgram.Disclosure → DisclosureRow
  | .shown => .shown
  | .hidden reason => .hidden (reasonId reason)

/-- All checked inputs shared by an exact or non-value result projection.  The
query is indexed by the exact `StateProgram`; the future and world handles are
indexed by the exact `FutureDecl` and `WorldIndex` retained in `report`. -/
structure CheckedResult
    {State : Type} {Γ : Expr.Schema}
    {source : StateProgram State Γ}
    {stateResolution : StatusEffects.Resolution State source.program.type.denote}
    {name futureName : String}
    {stateSurface : ResultProgram.SurfacePolicy State source.program.type.denote}
    {M : Future.WorldModel} {futureDecl : Future.FutureDecl M}
    {binding : BoundResult.WorldBinding futureDecl
      (source.declaration name futureName stateResolution stateSurface)}
    {K : Type} {key : M.World → K} {C : K → Prop}
    {index : Future.WorldIndex M}
    {base : Artifact.Artifact}
    (query : CheckedQuery base source)
    (future : Artifact.CheckedFuture futureDecl.future)
    (world : CheckedWorld index)
    (report : binding.CertifiedReport key C index) where private mk ::
  resolution : CheckedResolution stateResolution
  surface : CheckedSurface stateSurface

def CheckedResult.ofCertifiedReport
    {State : Type} {Γ : Expr.Schema}
    {source : StateProgram State Γ}
    {stateResolution : StatusEffects.Resolution State source.program.type.denote}
    {name futureName : String}
    {stateSurface : ResultProgram.SurfacePolicy State source.program.type.denote}
    {M : Future.WorldModel} {futureDecl : Future.FutureDecl M}
    {binding : BoundResult.WorldBinding futureDecl
      (source.declaration name futureName stateResolution stateSurface)}
    {K : Type} {key : M.World → K} {C : K → Prop}
    {index : Future.WorldIndex M} {base : Artifact.Artifact}
    (query : CheckedQuery base source)
    (future : Artifact.CheckedFuture futureDecl.future)
    (world : CheckedWorld index)
    (report : binding.CertifiedReport key C index)
    (resolution : CheckedResolution stateResolution)
    (surface : CheckedSurface stateSurface) :
    CheckedResult query future world report :=
  ⟨resolution, surface⟩

section ResultProjection

variable {State : Type} {Γ : Expr.Schema}
  {source : StateProgram State Γ}
  {stateResolution : StatusEffects.Resolution State source.program.type.denote}
  {name futureName : String}
  {stateSurface : ResultProgram.SurfacePolicy State source.program.type.denote}
  {M : Future.WorldModel} {futureDecl : Future.FutureDecl M}
  {binding : BoundResult.WorldBinding futureDecl
    (source.declaration name futureName stateResolution stateSurface)}
  {K : Type} {key : M.World → K} {C : K → Prop}
  {index : Future.WorldIndex M} {base : Artifact.Artifact}

private def CheckedResult.rowWithoutDisclosure
    {query : CheckedQuery base source}
    {future : Artifact.CheckedFuture futureDecl.future}
    {world : CheckedWorld index}
    {report : binding.CertifiedReport key C index}
    (checked : CheckedResult query future world report) : ResultRow where
  id := query.result
  query := query.id
  future := future.id
  resolution := checked.resolution.row
  surface := checked.surface.id
  status := StatusShape.ofStatusEffects report.statusShape
  effect := effectOfDeclaration binding.declaration
  visibility := VisibilityRow.ofResultProgram checked.surface.reasonId
    report.report.checked.visibility
  disclosure := none

/-- Project an exact result.  `some` disclosure is available only from the
kernel-checked selected value in `ExactBranch`. -/
def CheckedResult.toExactRow
    {query : CheckedQuery base source}
    {future : Artifact.CheckedFuture futureDecl.future}
    {world : CheckedWorld index}
    {report : binding.CertifiedReport key C index}
    (checked : CheckedResult query future world report)
    (branch : report.ExactBranch) : ResultRow :=
  { checked.rowWithoutDisclosure with
    status := .exact
    disclosure := some <|
      DisclosureRow.ofResultProgram checked.surface.reasonId branch.disclosure }

/-- Project a non-exact result only with a proof excluding the exact status.
Its scalar disclosure is necessarily absent. -/
def CheckedResult.toNonExactRow
    {query : CheckedQuery base source}
    {future : Artifact.CheckedFuture futureDecl.future}
    {world : CheckedWorld index}
    {report : binding.CertifiedReport key C index}
    (checked : CheckedResult query future world report)
    (_notExact : report.statusShape ≠ .exact) : ResultRow :=
  checked.rowWithoutDisclosure

@[simp] theorem CheckedResult.toExactRow_status
    {query : CheckedQuery base source}
    {future : Artifact.CheckedFuture futureDecl.future}
    {world : CheckedWorld index}
    {report : binding.CertifiedReport key C index}
    (checked : CheckedResult query future world report)
    (branch : report.ExactBranch) : (checked.toExactRow branch).status = .exact := rfl

/-- A stable certificate ID projected from the same exact certified report,
future handle, and world handle as its result row. -/
structure CheckedCertificate
    {future : Artifact.CheckedFuture futureDecl.future}
    {world : CheckedWorld index}
    (report : binding.CertifiedReport key C index) where private mk ::
  id : CertificateId

def CheckedCertificate.ofCertifiedReport
    {future : Artifact.CheckedFuture futureDecl.future}
    {world : CheckedWorld index}
    (report : binding.CertifiedReport key C index) (id : CertificateId) :
    CheckedCertificate (future := future) (world := world) report :=
  ⟨id⟩

def CheckedCertificate.toRow
    {future : Artifact.CheckedFuture futureDecl.future}
    {world : CheckedWorld index}
    {report : binding.CertifiedReport key C index}
    (checked : CheckedCertificate (future := future) (world := world) report) :
    CertificateRow :=
  ⟨checked.id, future.id, world.id⟩

def ArtifactV3Encoding.addWorld {M : Future.WorldModel}
    {index : Future.WorldIndex M} (encoding : ArtifactV3Encoding)
    (world : CheckedWorld index)
    (_id_ordered : ∀ previous ∈ encoding.worlds,
      previous.value < world.id.value) : ArtifactV3Encoding :=
  { encoding with worlds := encoding.worlds ++ [world.id] }

def ArtifactV3Encoding.addExactResult
    {base : Artifact.Artifact} {query : CheckedQuery base source}
    {future : Artifact.CheckedFuture futureDecl.future}
    {world : CheckedWorld index}
    {report : binding.CertifiedReport key C index}
    (encoding : ArtifactV3Encoding)
    (checked : CheckedResult query future world report)
    (branch : report.ExactBranch)
    (_base_exact : encoding.base = base.canonicalEncoding)
    (_query_present : encoding.queries.any (fun row => row.id == query.id) = true)
    (_future_present : encoding.base.futures.any
      (fun row => row.id == future.id.value) = true)
    (_id_ordered : ∀ previous ∈ encoding.results,
      previous.id.value < query.result.value) :
    ArtifactV3Encoding :=
  { encoding with results := encoding.results ++ [checked.toExactRow branch] }

def ArtifactV3Encoding.addNonExactResult
    {base : Artifact.Artifact} {query : CheckedQuery base source}
    {future : Artifact.CheckedFuture futureDecl.future}
    {world : CheckedWorld index}
    {report : binding.CertifiedReport key C index}
    (encoding : ArtifactV3Encoding)
    (checked : CheckedResult query future world report)
    (notExact : report.statusShape ≠ .exact)
    (_base_exact : encoding.base = base.canonicalEncoding)
    (_query_present : encoding.queries.any (fun row => row.id == query.id) = true)
    (_future_present : encoding.base.futures.any
      (fun row => row.id == future.id.value) = true)
    (_id_ordered : ∀ previous ∈ encoding.results,
      previous.id.value < query.result.value) :
    ArtifactV3Encoding :=
  { encoding with results := encoding.results ++ [checked.toNonExactRow notExact] }

def ArtifactV3Encoding.addCertificate
    {future : Artifact.CheckedFuture futureDecl.future}
    {world : CheckedWorld index}
    {report : binding.CertifiedReport key C index}
    (encoding : ArtifactV3Encoding)
    (checked : CheckedCertificate (future := future) (world := world) report)
    (_future_present : encoding.base.futures.any
      (fun row => row.id == future.id.value) = true)
    (_world_present : encoding.worlds.contains world.id = true)
    (_id_ordered : ∀ previous ∈ encoding.certificates,
      previous.id.value < checked.id.value) : ArtifactV3Encoding :=
  { encoding with certificates := encoding.certificates ++ [checked.toRow] }

@[simp] theorem ArtifactV3Encoding.addQuery_queries
    {query : CheckedQuery base source} (encoding : ArtifactV3Encoding)
    (baseExact : encoding.base = base.canonicalEncoding)
    (schemaExact : encoding.schema = query.schema)
    (idOrdered : ∀ previous ∈ encoding.queries,
      previous.id.value < query.id.value) :
    (encoding.addQuery query baseExact schemaExact idOrdered).queries =
      encoding.queries ++ [query.toRow] := rfl

@[simp] theorem ArtifactV3Encoding.addWorld_worlds
    (encoding : ArtifactV3Encoding) (world : CheckedWorld index)
    (idOrdered : ∀ previous ∈ encoding.worlds,
      previous.value < world.id.value) :
    (encoding.addWorld world idOrdered).worlds = encoding.worlds ++ [world.id] := rfl

@[simp] theorem ArtifactV3Encoding.addExactResult_results
    {query : CheckedQuery base source}
    {future : Artifact.CheckedFuture futureDecl.future}
    {world : CheckedWorld index}
    {report : binding.CertifiedReport key C index}
    (encoding : ArtifactV3Encoding)
    (checked : CheckedResult query future world report)
    (branch : report.ExactBranch)
    (baseExact : encoding.base = base.canonicalEncoding)
    (queryPresent : encoding.queries.any (fun row => row.id == query.id) = true)
    (futurePresent : encoding.base.futures.any
      (fun row => row.id == future.id.value) = true)
    (idOrdered : ∀ previous ∈ encoding.results,
      previous.id.value < query.result.value) :
    (encoding.addExactResult checked branch baseExact queryPresent futurePresent
      idOrdered).results = encoding.results ++ [checked.toExactRow branch] := rfl

@[simp] theorem ArtifactV3Encoding.addCertificate_certificates
    {future : Artifact.CheckedFuture futureDecl.future}
    {world : CheckedWorld index}
    {report : binding.CertifiedReport key C index}
    (encoding : ArtifactV3Encoding)
    (checked : CheckedCertificate (future := future) (world := world) report)
    (futurePresent : encoding.base.futures.any
      (fun row => row.id == future.id.value) = true)
    (worldPresent : encoding.worlds.contains world.id = true)
    (idOrdered : ∀ previous ∈ encoding.certificates,
      previous.id.value < checked.id.value) :
    (encoding.addCertificate checked futurePresent worldPresent idOrdered).certificates =
      encoding.certificates ++ [checked.toRow] := rfl

end ResultProjection

end Uwueave.Preo.ArtifactV3
