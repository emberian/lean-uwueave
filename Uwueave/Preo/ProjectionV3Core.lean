/-
# Uwueave.Preo.ProjectionV3Core — data-only V3 validation

V3 validates the unchanged V2 base through `ProjectionV2Core`, then checks the
typed-query extension: finite bounds, unique stable identities, exact
cross-row references, canonical analysis/effect lists, field dependencies,
and certificate membership in explicit future/world registries.

Successful validation remains first-order.  It does not reconstruct a
`StateProgram`, `BoundResult`, checked certificate, world, or proof.
-/
import Uwueave.Preo.ArtifactV3Data
import Uwueave.Preo.ProjectionV2Core

namespace Uwueave.Preo.ProjectionV3

open Uwueave.Preo.Artifact
open Uwueave.Preo.ArtifactV3

set_option autoImplicit false

def schema : String := "uwueave/preo-projection/v3"

structure Projection where
  schema : String
  encoding : ArtifactV3Encoding
  deriving DecidableEq

def Projection.ofEncoding (encoding : ArtifactV3Encoding) : Projection :=
  ⟨Uwueave.Preo.ProjectionV3.schema, encoding⟩

structure ValidationBounds where
  base : ProjectionV2.ValidationBounds
  maxWorlds : Nat
  maxQueries : Nat
  maxResults : Nat
  maxCertificates : Nat
  maxReadsPerQuery : Nat
  maxHolesPerQuery : Nat
  maxAnalysesPerQuery : Nat
  maxEffectShapesPerResult : Nat
  deriving DecidableEq

structure ValidationConfig where
  bounds : ValidationBounds
  deriving DecidableEq

inductive BoundedList where
  | worlds
  | queries
  | results
  | certificates
  | queryReads (queryId : Nat)
  | queryHoles (queryId : Nat)
  | queryAnalyses (queryId : Nat)
  | resultEffect (resultId : Nat)
  deriving DecidableEq

inductive ValidationError where
  | wrongSchema (expected found : String)
  | base (error : ProjectionV2.ValidationError)
  | listTooLarge (list : BoundedList) (actual limit : Nat)
  | duplicateWorldId (id : Nat)
  | duplicateQueryId (id : Nat)
  | duplicateResultId (id : Nat)
  | duplicateProgramId (id : Nat)
  | duplicateCertificateId (id : Nat)
  | wrongQuerySchema (queryId expected found : Nat)
  | danglingQueryResult (queryId resultId : Nat)
  | mismatchedQueryResult (queryId resultId foundQueryId : Nat)
  | danglingResultQuery (resultId queryId : Nat)
  | mismatchedResultQuery (resultId queryId foundResultId : Nat)
  | danglingQueryField (queryId fieldId : Nat)
  | queryReadsMismatch (queryId : Nat)
  | nonCanonicalAnalyses (queryId : Nat) (found : List AnalysisTag)
  | danglingResultFuture (resultId futureId : Nat)
  | nonCanonicalEffect (resultId : Nat) (found : List StatusShape)
  | effectNotDownwardClosed (resultId : Nat)
  | statusOutsideEffect (resultId : Nat) (status : StatusShape)
  | missingExactDisclosure (resultId : Nat)
  | disclosureWithoutExactValue (resultId : Nat) (status : StatusShape)
  | danglingCertificateFuture (certificateId futureId : Nat)
  | danglingCertificateWorld (certificateId worldId : Nat)
  deriving DecidableEq

abbrev ValidationResult (alpha : Type) := Except ValidationError alpha

structure ValidatedProjectionV3 where private mk ::
  projection : Projection
  config : ValidationConfig
  baseValidated : ProjectionV2.ValidatedProjectionV2
  base_exact : baseValidated.encoding = projection.encoding.base
  deriving DecidableEq

def ValidatedProjectionV3.schema (validated : ValidatedProjectionV3) : String :=
  validated.projection.schema

def ValidatedProjectionV3.encoding
    (validated : ValidatedProjectionV3) : ArtifactV3Encoding :=
  validated.projection.encoding

def ValidatedProjectionV3.validationConfig
    (validated : ValidatedProjectionV3) : ValidationConfig :=
  validated.config

def ValidatedProjectionV3.validatedBase
    (validated : ValidatedProjectionV3) : ProjectionV2.ValidatedProjectionV2 :=
  validated.baseValidated

private def firstDuplicate? : List Nat → Option Nat
  | [] => none
  | id :: ids => if ids.contains id then some id else firstDuplicate? ids

private def checkBound (list : BoundedList) (actual limit : Nat) :
    ValidationResult Unit :=
  if actual ≤ limit then pure ()
  else throw (.listTooLarge list actual limit)

private def canonicalAnalyses : List AnalysisTag :=
  [.mergeSafe, .monotoneSafe]

private def canonicalizeAnalyses (found : List AnalysisTag) : List AnalysisTag :=
  canonicalAnalyses.filter fun tag => found.contains tag

private def canonicalEffectShapes : List StatusShape :=
  [.exact, .provisional, .forkedClosed, .forkedOpen, .absent, .pending]

private def canonicalizeEffect (found : List StatusShape) : List StatusShape :=
  canonicalEffectShapes.filter fun shape => found.contains shape

private def effectDownwardClosed (effect : List StatusShape) : Bool :=
  (!effect.contains .provisional || effect.contains .exact) &&
  (!effect.contains .forkedClosed || effect.contains .exact) &&
  (!effect.contains .forkedOpen ||
    (effect.contains .exact && effect.contains .provisional &&
      effect.contains .forkedClosed)) &&
  (!effect.contains .absent || effect.contains .exact) &&
  (!effect.contains .pending ||
    (effect.contains .exact && effect.contains .provisional &&
      effect.contains .absent))

private def checkQuery (bounds : ValidationBounds) (encoding : ArtifactV3Encoding)
    (query : QueryRow) : ValidationResult Unit := do
  checkBound (.queryReads query.id.value) query.reads.length bounds.maxReadsPerQuery
  checkBound (.queryHoles query.id.value) query.holes.length bounds.maxHolesPerQuery
  checkBound (.queryAnalyses query.id.value) query.analyses.length
    bounds.maxAnalysesPerQuery
  if query.schema = encoding.schema then pure ()
  else throw (.wrongQuerySchema query.id.value encoding.schema.value query.schema.value)
  let result ← match encoding.results.find? (fun row => row.id == query.result) with
    | some result => pure result
    | none => throw (.danglingQueryResult query.id.value query.result.value)
  if result.query = query.id then pure ()
  else throw (.mismatchedQueryResult query.id.value query.result.value result.query.value)
  for field in query.reads do
    if encoding.base.fields.any (fun row => row.id == field.value) then pure ()
    else throw (.danglingQueryField query.id.value field.value)
  for hole in query.holes do
    if encoding.base.fields.any (fun row => row.id == hole.field.value) then pure ()
    else throw (.danglingQueryField query.id.value hole.field.value)
  if query.reads = query.holes.map HoleRow.field then pure ()
  else throw (.queryReadsMismatch query.id.value)
  if query.analyses = canonicalizeAnalyses query.analyses then pure ()
  else throw (.nonCanonicalAnalyses query.id.value query.analyses)

private def checkResult (bounds : ValidationBounds) (encoding : ArtifactV3Encoding)
    (result : ResultRow) : ValidationResult Unit := do
  checkBound (.resultEffect result.id.value) result.effect.length
    bounds.maxEffectShapesPerResult
  let query ← match encoding.queries.find? (fun row => row.id == result.query) with
    | some query => pure query
    | none => throw (.danglingResultQuery result.id.value result.query.value)
  if query.result = result.id then pure ()
  else throw (.mismatchedResultQuery result.id.value result.query.value query.result.value)
  if encoding.base.futures.any (fun row => row.id == result.future.value) then pure ()
  else throw (.danglingResultFuture result.id.value result.future.value)
  if result.effect = canonicalizeEffect result.effect then pure ()
  else throw (.nonCanonicalEffect result.id.value result.effect)
  if effectDownwardClosed result.effect then pure ()
  else throw (.effectNotDownwardClosed result.id.value)
  if result.effect.contains result.status then pure ()
  else throw (.statusOutsideEffect result.id.value result.status)
  match result.status, result.disclosure with
  | .exact, some _ => pure ()
  | .exact, none => throw (.missingExactDisclosure result.id.value)
  | _, none => pure ()
  | status, some _ => throw (.disclosureWithoutExactValue result.id.value status)

private def checkCertificate (encoding : ArtifactV3Encoding)
    (certificate : CertificateRow) : ValidationResult Unit := do
  if encoding.base.futures.any (fun row => row.id == certificate.future.value) then pure ()
  else throw (.danglingCertificateFuture certificate.id.value certificate.future.value)
  if encoding.worlds.contains certificate.world then pure ()
  else throw (.danglingCertificateWorld certificate.id.value certificate.world.value)

/-- Validate the exact V2 base and every V3 identity/reference/resource rule.
The private result is the only input accepted by the production renderer. -/
def validate (config : ValidationConfig) (projection : Projection) :
    ValidationResult ValidatedProjectionV3 := do
  if projection.schema = schema then pure ()
  else throw (.wrongSchema schema projection.schema)
  let encoding := projection.encoding
  let baseProjection := ProjectionV2.Projection.ofEncoding encoding.base
  let baseValidated ← match ProjectionV2.validate ⟨config.bounds.base⟩ baseProjection with
    | .ok validated => pure validated
    | .error error => throw (.base error)
  checkBound .worlds encoding.worlds.length config.bounds.maxWorlds
  checkBound .queries encoding.queries.length config.bounds.maxQueries
  checkBound .results encoding.results.length config.bounds.maxResults
  checkBound .certificates encoding.certificates.length config.bounds.maxCertificates
  match firstDuplicate? (encoding.worlds.map WorldId.value) with
  | some id => throw (.duplicateWorldId id)
  | none => pure ()
  match firstDuplicate? (encoding.queries.map fun row => row.id.value) with
  | some id => throw (.duplicateQueryId id)
  | none => pure ()
  match firstDuplicate? (encoding.results.map fun row => row.id.value) with
  | some id => throw (.duplicateResultId id)
  | none => pure ()
  match firstDuplicate? (encoding.queries.map fun row => row.program.value) with
  | some id => throw (.duplicateProgramId id)
  | none => pure ()
  match firstDuplicate? (encoding.certificates.map fun row => row.id.value) with
  | some id => throw (.duplicateCertificateId id)
  | none => pure ()
  for query in encoding.queries do
    checkQuery config.bounds encoding query
  for result in encoding.results do
    checkResult config.bounds encoding result
  for certificate in encoding.certificates do
    checkCertificate encoding certificate
  let acceptedProjection : Projection :=
    { projection with
      encoding := { encoding with base := baseValidated.encoding } }
  pure ⟨acceptedProjection, config, baseValidated, rfl⟩

end Uwueave.Preo.ProjectionV3
