/-
# Uwueave.Preo.ProjectionV3Core — data-only V3 validation

V3 validates the unchanged V2 base through `ProjectionV2Core`, then checks the
typed-query extension: finite bounds, unique stable identities, exact
cross-row references, canonical analysis/effect lists, field dependencies,
and certificate membership in explicit future/world registries.

Successful validation remains first-order.  It does not reconstruct a
`StateProgram`, `BoundResult`, checked certificate, world, or proof.

V3's present wire cannot validate a certificate-to-result association or
collisions between authored resolution/surface/reason names because those
registries are not encoded.  Validation therefore makes no such claims.
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
  /-- Largest admitted numeric identity in the V3 extension rows, including
  their references into V2.  V2 owns separate bounds and does not yet cap all
  of its numeric IDs, so this is not a bound on the complete combined render. -/
  maxStableIdValue : Nat
  maxWorlds : Nat
  maxQueries : Nat
  maxResults : Nat
  maxCertificates : Nat
  maxReadsPerQuery : Nat
  maxHolesPerQuery : Nat
  /-- Maximum syntax-tree path depth of one query hole. -/
  maxHolePathDepth : Nat
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

inductive StableIdKind where
  | schema
  | world
  | query
  | result
  | program
  | field
  | future
  | resolution
  | surface
  | reason
  | certificate
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
  | stableIdTooLarge (kind : StableIdKind) (id limit : Nat)
  | nonCanonicalRowOrder (rows : BoundedList) (previous current : Nat)
  | wrongQuerySchema (queryId expected found : Nat)
  | danglingQueryResult (queryId resultId : Nat)
  | mismatchedQueryResult (queryId resultId foundQueryId : Nat)
  | danglingResultQuery (resultId queryId : Nat)
  | mismatchedResultQuery (resultId queryId foundResultId : Nat)
  | danglingQueryField (queryId fieldId : Nat)
  | queryReadsMismatch (queryId : Nat)
  | nonCanonicalAnalyses (queryId : Nat) (found : List AnalysisTag)
  | incoherentAnalyses (queryId : Nat) (found : List AnalysisTag)
  | holePathTooDeep (queryId holeIndex actual limit : Nat)
  | invalidHolePathSegment (queryId holeIndex segmentIndex found : Nat)
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

private def checkStableId (kind : StableIdKind) (limit id : Nat) :
    ValidationResult Unit :=
  if id ≤ limit then pure ()
  else throw (.stableIdTooLarge kind id limit)

private def firstNonIncreasing? : List Nat → Option (Nat × Nat)
  | [] | [_] => none
  | previous :: current :: rest =>
      if previous < current then firstNonIncreasing? (current :: rest)
      else some (previous, current)

private def checkRowOrder (rows : BoundedList) (ids : List Nat) :
    ValidationResult Unit :=
  match firstNonIncreasing? ids with
  | none => pure ()
  | some (previous, current) =>
      throw (.nonCanonicalRowOrder rows previous current)

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

private def checkQueryResourceBounds (bounds : ValidationBounds) (query : QueryRow) :
    ValidationResult Unit := do
  checkBound (.queryReads query.id.value) query.reads.length bounds.maxReadsPerQuery
  checkBound (.queryHoles query.id.value) query.holes.length bounds.maxHolesPerQuery
  checkBound (.queryAnalyses query.id.value) query.analyses.length
    bounds.maxAnalysesPerQuery
  for (hole, holeIndex) in query.holes.zipIdx do
    if hole.path.length ≤ bounds.maxHolePathDepth then pure ()
    else throw (.holePathTooDeep query.id.value holeIndex hole.path.length
      bounds.maxHolePathDepth)
    for (segment, segmentIndex) in hole.path.zipIdx do
      if segment ≤ 1 then pure ()
      else throw (.invalidHolePathSegment query.id.value holeIndex segmentIndex segment)

private def checkQuery (encoding : ArtifactV3Encoding) (query : QueryRow) :
    ValidationResult Unit := do
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
  if query.analyses.contains .mergeSafe &&
      !query.analyses.contains .monotoneSafe then
    throw (.incoherentAnalyses query.id.value query.analyses)
  else pure ()

private def checkQueryStableIds (limit : Nat) (query : QueryRow) :
    ValidationResult Unit := do
  checkStableId .query limit query.id.value
  checkStableId .schema limit query.schema.value
  checkStableId .result limit query.result.value
  checkStableId .program limit query.program.value
  for field in query.reads do
    checkStableId .field limit field.value
  for hole in query.holes do
    checkStableId .field limit hole.field.value

private def checkResultStableIds (limit : Nat) (result : ResultRow) :
    ValidationResult Unit := do
  checkStableId .result limit result.id.value
  checkStableId .query limit result.query.value
  checkStableId .future limit result.future.value
  match result.resolution with
  | .preserveFork => pure ()
  | .named id => checkStableId .resolution limit id.value
  checkStableId .surface limit result.surface.value
  match result.visibility with
  | .inspectable => pure ()
  | .opaque reason => checkStableId .reason limit reason.value
  match result.disclosure with
  | none | some .shown => pure ()
  | some (.hidden reason) => checkStableId .reason limit reason.value

private def checkCertificateStableIds (limit : Nat)
    (certificate : CertificateRow) : ValidationResult Unit := do
  checkStableId .certificate limit certificate.id.value
  checkStableId .future limit certificate.future.value
  checkStableId .world limit certificate.world.value

private def checkResultResourceBounds (bounds : ValidationBounds) (result : ResultRow) :
    ValidationResult Unit :=
  checkBound (.resultEffect result.id.value) result.effect.length
    bounds.maxEffectShapesPerResult

private def checkResult (encoding : ArtifactV3Encoding) (result : ResultRow) :
    ValidationResult Unit := do
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
  checkRowOrder .worlds (encoding.worlds.map WorldId.value)
  checkRowOrder .queries (encoding.queries.map fun row => row.id.value)
  checkRowOrder .results (encoding.results.map fun row => row.id.value)
  checkRowOrder .certificates (encoding.certificates.map fun row => row.id.value)
  checkStableId .schema config.bounds.maxStableIdValue encoding.schema.value
  for world in encoding.worlds do
    checkStableId .world config.bounds.maxStableIdValue world.value
  for query in encoding.queries do
    checkQueryStableIds config.bounds.maxStableIdValue query
  for result in encoding.results do
    checkResultStableIds config.bounds.maxStableIdValue result
  for certificate in encoding.certificates do
    checkCertificateStableIds config.bounds.maxStableIdValue certificate
  -- Reject extension-owned nested resource excess before traversing the V2
  -- base or resolving any cross-row references.
  for query in encoding.queries do
    checkQueryResourceBounds config.bounds query
  for result in encoding.results do
    checkResultResourceBounds config.bounds result
  let baseProjection := ProjectionV2.Projection.ofEncoding encoding.base
  let baseValidated ← match ProjectionV2.validate ⟨config.bounds.base⟩ baseProjection with
    | .ok validated => pure validated
    | .error error => throw (.base error)
  for query in encoding.queries do
    checkQuery encoding query
  for result in encoding.results do
    checkResult encoding result
  for certificate in encoding.certificates do
    checkCertificate encoding certificate
  let acceptedProjection : Projection :=
    { projection with
      encoding := { encoding with base := baseValidated.encoding } }
  pure ⟨acceptedProjection, config, baseValidated, rfl⟩

end Uwueave.Preo.ProjectionV3
