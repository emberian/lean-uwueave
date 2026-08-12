/-
# Uwueave.Preo.ProjectionV3Examples — V3 acceptance and refusal examples

These first-order fixtures exercise every V3 row family over the unchanged
proof-originated V2 example.  The proof-indexed construction journey is tested
separately through `ArtifactV3Checked`; this opt-in leaf deliberately keeps all
worked data out of the production validator/renderer closure.
-/
import Uwueave.Preo.ProjectionV3
import Uwueave.Preo.ProjectionV2Examples

namespace Uwueave.Preo.ProjectionV3

open Uwueave.Preo.ArtifactV3

set_option autoImplicit false

namespace Examples

private def validationError? {alpha : Type} :
    ValidationResult alpha → Option ValidationError
  | .ok _ => none
  | .error error => some error

def config : ValidationConfig where
  bounds := {
    base := ProjectionV2.Examples.config.bounds
    maxStableIdValue := 2000
    maxWorlds := 8
    maxQueries := 8
    maxResults := 8
    maxCertificates := 8
    maxReadsPerQuery := 8
    maxHolesPerQuery := 8
    maxHolePathDepth := 8
    maxAnalysesPerQuery := 2
    maxEffectShapesPerResult := 6 }

def fullEncoding : ArtifactV3Encoding where
  base := ProjectionV2.Examples.fullEncoding
  schema := ⟨1000⟩
  worlds := [⟨1001⟩]
  queries := [{
    id := ⟨1002⟩
    schema := ⟨1000⟩
    result := ⟨1003⟩
    program := ⟨1004⟩
    reads := [⟨402⟩]
    holes := [{ path := [0], field := ⟨402⟩, kind := .field }]
    analyses := [.mergeSafe, .monotoneSafe] }]
  results := [{
    id := ⟨1003⟩
    query := ⟨1002⟩
    future := ⟨404⟩
    resolution := .preserveFork
    surface := ⟨1005⟩
    status := .exact
    effect := [.exact]
    visibility := .inspectable
    disclosure := some .shown }]
  certificates := [{ id := ⟨1006⟩, future := ⟨404⟩, world := ⟨1001⟩ }]

def fullProjection : Projection := Projection.ofEncoding fullEncoding

def fullQuery : QueryRow := fullEncoding.queries[0]'(by decide)
def fullResult : ResultRow := fullEncoding.results[0]'(by decide)
def fullCertificate : CertificateRow := fullEncoding.certificates[0]'(by decide)

theorem full_is_nonempty :
    fullEncoding.base.fields.length = 1
      ∧ fullEncoding.worlds.length = 1
      ∧ fullEncoding.queries.length = 1
      ∧ fullEncoding.results.length = 1
      ∧ fullEncoding.certificates.length = 1 := by decide

theorem full_validates : (validate config fullProjection).isOk = true := by decide

def fullValidated : ValidatedProjectionV3 :=
  (validate config fullProjection).toOption.get (by decide)

theorem full_validated_base_exact :
    fullValidated.validatedBase.encoding = fullValidated.encoding.base :=
  fullValidated.base_exact

def wrongSchema : Projection := { fullProjection with schema := ProjectionV2.schema }

theorem wrong_schema_refused :
    validationError? (validate config wrongSchema) =
      some (.wrongSchema schema ProjectionV2.schema) := by decide

def danglingResultFuture : Projection :=
  { fullProjection with encoding :=
      { fullEncoding with results := fullEncoding.results.map fun row =>
          { row with future := ⟨999⟩ } } }

theorem dangling_result_future_refused :
    validationError? (validate config danglingResultFuture) =
      some (.danglingResultFuture 1003 999) := by decide

def wrongQuerySchema : Projection :=
  { fullProjection with encoding :=
      { fullEncoding with queries := fullEncoding.queries.map fun row =>
          { row with schema := ⟨999⟩ } } }

theorem wrong_query_schema_refused :
    validationError? (validate config wrongQuerySchema) =
      some (.wrongQuerySchema 1002 1000 999) := by decide

def mismatchedQueryResult : Projection :=
  { fullProjection with encoding :=
      { fullEncoding with results := fullEncoding.results.map fun row =>
          { row with query := ⟨999⟩ } } }

theorem mismatched_query_result_refused :
    validationError? (validate config mismatchedQueryResult) =
      some (.mismatchedQueryResult 1002 1003 999) := by decide

def queryReadsMismatch : Projection :=
  { fullProjection with encoding :=
      { fullEncoding with queries := fullEncoding.queries.map fun row =>
          { row with reads := [] } } }

theorem query_reads_mismatch_refused :
    validationError? (validate config queryReadsMismatch) =
      some (.queryReadsMismatch 1002) := by decide

def danglingCertificateFuture : Projection :=
  { fullProjection with encoding :=
      { fullEncoding with certificates := fullEncoding.certificates.map fun row =>
          { row with future := ⟨999⟩ } } }

theorem dangling_certificate_future_refused :
    validationError? (validate config danglingCertificateFuture) =
      some (.danglingCertificateFuture 1006 999) := by decide

def danglingCertificateWorld : Projection :=
  { fullProjection with encoding :=
      { fullEncoding with certificates := fullEncoding.certificates.map fun row =>
          { row with world := ⟨999⟩ } } }

theorem dangling_certificate_world_refused :
    validationError? (validate config danglingCertificateWorld) =
      some (.danglingCertificateWorld 1006 999) := by decide

def exactWithoutDisclosure : Projection :=
  { fullProjection with encoding :=
      { fullEncoding with results := fullEncoding.results.map fun row =>
          { row with disclosure := none } } }

theorem exact_without_disclosure_refused :
    validationError? (validate config exactWithoutDisclosure) =
      some (.missingExactDisclosure 1003) := by decide

def pendingWithDisclosure : Projection :=
  { fullProjection with encoding :=
      { fullEncoding with results := fullEncoding.results.map fun row =>
          { { row with status := StatusShape.pending } with
            effect := [StatusShape.exact, .provisional, .absent, .pending] } } }

theorem pending_with_disclosure_refused :
    validationError? (validate config pendingWithDisclosure) =
      some (.disclosureWithoutExactValue 1003 .pending) := by decide

def duplicateWorld : Projection :=
  { fullProjection with encoding :=
      { fullEncoding with worlds := fullEncoding.worlds ++ fullEncoding.worlds } }

theorem duplicate_world_refused :
    validationError? (validate config duplicateWorld) =
      some (.duplicateWorldId 1001) := by decide

def zeroQueryBound : ValidationConfig :=
  { config with bounds := { config.bounds with maxQueries := 0 } }

theorem query_bound_refused :
    validationError? (validate zeroQueryBound fullProjection) =
      some (.listTooLarge .queries 1 0) := by decide

def overdeepHolePath : Projection :=
  { fullProjection with encoding :=
      { fullEncoding with queries := fullEncoding.queries.map fun row =>
          { row with holes := row.holes.map fun hole =>
              { hole with path := List.replicate 9 0 } } } }

theorem overdeep_hole_path_refused :
    validationError? (validate config overdeepHolePath) =
      some (.holePathTooDeep 1002 0 9 8) := by decide

def invalidHolePathSegment : Projection :=
  { fullProjection with encoding :=
      { fullEncoding with queries := fullEncoding.queries.map fun row =>
          { row with holes := row.holes.map fun hole =>
              { hole with path := [2] } } } }

theorem invalid_hole_path_segment_refused :
    validationError? (validate config invalidHolePathSegment) =
      some (.invalidHolePathSegment 1002 0 0 2) := by decide

def incoherentAnalyses : Projection :=
  { fullProjection with encoding :=
      { fullEncoding with queries := fullEncoding.queries.map fun row =>
          { row with analyses := [.mergeSafe] } } }

theorem incoherent_analyses_refused :
    validationError? (validate config incoherentAnalyses) =
      some (.incoherentAnalyses 1002 [.mergeSafe]) := by decide

def oversizedSurfaceId : Projection :=
  { fullProjection with encoding :=
      { fullEncoding with results := fullEncoding.results.map fun row =>
          { row with surface := ⟨2001⟩ } } }

theorem oversized_surface_id_refused :
    validationError? (validate config oversizedSurfaceId) =
      some (.stableIdTooLarge .surface 2001 2000) := by decide

private def secondQuery : QueryRow :=
  { fullQuery with id := ⟨1007⟩, result := ⟨1008⟩, program := ⟨1009⟩ }

private def secondResult : ResultRow :=
  { fullResult with id := ⟨1008⟩, query := ⟨1007⟩ }

def reorderedQueries : Projection :=
  { fullProjection with encoding :=
      { fullEncoding with
        queries := [secondQuery, fullQuery]
        results := [fullResult, secondResult] } }

theorem reordered_queries_refused :
    validationError? (validate config reorderedQueries) =
      some (.nonCanonicalRowOrder .queries 1007 1002) := by decide

def reorderedWorlds : Projection :=
  { fullProjection with encoding :=
      { fullEncoding with worlds := [⟨1007⟩, ⟨1001⟩] } }

theorem reordered_worlds_refused :
    validationError? (validate config reorderedWorlds) =
      some (.nonCanonicalRowOrder .worlds 1007 1001) := by decide

def reorderedResults : Projection :=
  { fullProjection with encoding :=
      { fullEncoding with
        queries := [fullQuery, secondQuery]
        results := [secondResult, fullResult] } }

theorem reordered_results_refused :
    validationError? (validate config reorderedResults) =
      some (.nonCanonicalRowOrder .results 1008 1003) := by decide

private def secondCertificate : CertificateRow :=
  { fullCertificate with id := ⟨1007⟩ }

def reorderedCertificates : Projection :=
  { fullProjection with encoding :=
      { fullEncoding with certificates := [secondCertificate, fullCertificate] } }

theorem reordered_certificates_refused :
    validationError? (validate config reorderedCertificates) =
      some (.nonCanonicalRowOrder .certificates 1007 1006) := by decide

def nonCanonicalAnalyses : Projection :=
  { fullProjection with encoding :=
      { fullEncoding with queries := fullEncoding.queries.map fun row =>
          { row with analyses := [.monotoneSafe, .mergeSafe] } } }

theorem noncanonical_analyses_refused :
    validationError? (validate config nonCanonicalAnalyses) =
      some (.nonCanonicalAnalyses 1002 [.monotoneSafe, .mergeSafe]) := by decide

def nonDownwardEffect : Projection :=
  { fullProjection with encoding :=
      { fullEncoding with results := fullEncoding.results.map fun row =>
          { { row with status := StatusShape.provisional } with
            effect := [StatusShape.provisional]
            disclosure := none } } }

theorem nondownward_effect_refused :
    validationError? (validate config nonDownwardEffect) =
      some (.effectNotDownwardClosed 1003) := by decide

def statusOutsideEffect : Projection :=
  { fullProjection with encoding :=
      { fullEncoding with results := fullEncoding.results.map fun row =>
          { { row with status := StatusShape.pending } with
            disclosure := none } } }

theorem status_outside_effect_refused :
    validationError? (validate config statusOutsideEffect) =
      some (.statusOutsideEffect 1003 .pending) := by decide

end Examples
end Uwueave.Preo.ProjectionV3
