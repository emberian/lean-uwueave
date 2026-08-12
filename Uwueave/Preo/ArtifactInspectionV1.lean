/-
# Uwueave.Preo.ArtifactInspectionV1 -- bounded diagnostic artifact inspection

This module turns canonical artifact-v2 and artifact-v3 frames into
deterministic JSON.  It delegates payload admission to the Lean-owned durable
codecs and structural admission to ProjectionV2/ProjectionV3.  The result is
diagnostic first-order data only: it is not a proof, permit, certificate, or
reconstruction of checked sources.

The API is pure.  File/stdin access belongs only to the explicit companion
command.  Bounds limit accepted row/reference counts; they do not assert a
filesystem, allocation, or denial-of-service theorem.
-/
import Lean.Data.Json
import Uwueave.Preo.ArtifactDurableCore
import Uwueave.Preo.ArtifactV3Durable
import Uwueave.Preo.ProjectionV2Core
import Uwueave.Preo.ProjectionV3Core

namespace Uwueave.Preo.ArtifactInspectionV1

open Lean
open Uwueave.Preo.Artifact
open Uwueave.Preo.ArtifactDurable
open Uwueave.Preo.ArtifactV3

set_option autoImplicit false

/-- Consumer-selected diagnostic limits.  Projection validation applies the
same row/reference ceiling uniformly so no hidden row family is unbounded. -/
structure Bounds where
  maxInputBytes : Nat := 1024 * 1024
  maxRecords : Nat := 64
  maxRows : Nat := 256
  maxRefsPerRow : Nat := 256
  deriving DecidableEq, Repr

inductive Error where
  | inputLimit (actual limit : Nat)
  | tornFrame (recordStart observedEnd : Nat)
  | refusedFrame (recordStart : Nat)
  | recordLimit (limit : Nat)
  | expectedOneFrame (actual : Nat)
  | invalidV2 (recordIndex : Nat)
  | invalidV3 (recordIndex : Nat)
  deriving DecidableEq

private def validationConfig (bounds : Bounds) : ProjectionV2.ValidationConfig where
  bounds := {
    maxFields := bounds.maxRows
    maxInvariants := bounds.maxRows
    maxFutures := bounds.maxRows
    maxSessions := bounds.maxRows
    maxPlans := bounds.maxRows
    maxBudgets := bounds.maxRows
    maxObligationsPerSession := bounds.maxRefsPerRow
    maxActionsPerPlan := bounds.maxRefsPerRow
    maxProfileEntriesPerPlan := 5
    maxProfileEntriesPerBudget := 5
    maxParticipantsPerDemand := bounds.maxRefsPerRow
    maxWitnessWords := bounds.maxRefsPerRow }

private def validationConfigV3 (bounds : Bounds) : ProjectionV3.ValidationConfig where
  bounds := {
    base := (validationConfig bounds).bounds
    maxStableIdValue := bounds.maxInputBytes
    maxWorlds := bounds.maxRows
    maxQueries := bounds.maxRows
    maxResults := bounds.maxRows
    maxCertificates := bounds.maxRows
    maxReadsPerQuery := bounds.maxRefsPerRow
    maxHolesPerQuery := bounds.maxRefsPerRow
    maxHolePathDepth := bounds.maxRefsPerRow
    maxAnalysesPerQuery := 2
    maxEffectShapesPerResult := 6 }

private def nat (value : Nat) : Json := value

private def array (values : List Json) : Json := .arr values.toArray

private def optionNat : Option Nat → Json
  | none => .null
  | some value => nat value

private def currencyName : Currency → String
  | .peerBarrier => "peerBarrier"
  | .arbiterCut => "arbiterCut"
  | .networkRound => "networkRound"
  | .userPrompt => "userPrompt"
  | .rollback => "rollback"

private def currency (value : Currency) : Json := .str (currencyName value)

private def profileEntry (entry : Currency × Nat) : Json :=
  Json.mkObj [("currency", currency entry.1), ("count", nat entry.2)]

private def profile (entries : List (Currency × Nat)) : Json :=
  array (entries.map profileEntry)

private def evidence : EvidenceKey → Json
  | .none => Json.mkObj [("kind", "none")]
  | .named key => Json.mkObj [("kind", "named"), ("key", nat key)]

private def demand (value : DemandArtifact) : Json :=
  Json.mkObj
    [("currency", currency value.currency),
     ("participants", array (value.participants.map nat)),
     ("scope", nat value.scope),
     ("epoch", nat value.epoch),
     ("evidence", evidence value.evidence),
     ("round", nat value.round),
     ("barrier", nat value.barrier)]

private def origin : OriginArtifact → Json
  | .ambient => Json.mkObj [("kind", "ambient")]
  | .crossing index =>
      Json.mkObj [("kind", "crossing"), ("index", nat index)]

private def obligation (value : ObligationArtifact) : Json :=
  Json.mkObj [("origin", origin value.origin), ("demand", demand value.demand)]

private def verdict : VerdictEvidence → Json
  | .free => Json.mkObj [("kind", "free")]
  | .clash left right =>
      Json.mkObj
        [("kind", "clash"),
         ("left", array (left.map nat)),
         ("right", array (right.map nat))]

private def declaration (value : DeclarationArtifactEncoding) : Json :=
  Json.mkObj
    [("id", nat value.id),
     ("stateTypeId", nat value.stateTypeId),
     ("schemaVersion", nat value.schemaVersion)]

private def field (value : FieldArtifactEncoding) : Json :=
  Json.mkObj
    [("id", nat value.id),
     ("declarationId", nat value.declarationId),
     ("kindId", nat value.kindId),
     ("carrierTypeId", nat value.carrierTypeId),
     ("keyTypeId", optionNat value.keyTypeId)]

private def invariant (value : InvariantArtifactEncoding) : Json :=
  Json.mkObj
    [("id", nat value.id),
     ("declarationId", nat value.declarationId),
     ("carrierTypeId", nat value.carrierTypeId),
     ("verdict", verdict value.verdict)]

private def future (value : FutureArtifactEncoding) : Json :=
  Json.mkObj
    [("id", nat value.id),
     ("declarationId", nat value.declarationId),
     ("worldTypeId", nat value.worldTypeId),
     ("relationId", nat value.relationId)]

private def session (value : SessionArtifactEncoding) : Json :=
  Json.mkObj
    [("id", nat value.id),
     ("declarationId", nat value.declarationId),
     ("crossings", nat value.crossings),
     ("obligations", array (value.obligations.map obligation))]

private def plan (value : PlanArtifactEncoding) : Json :=
  Json.mkObj
    [("id", nat value.id),
     ("sessionId", nat value.sessionId),
     ("actions", array (value.actions.map demand)),
     ("profile", profile value.profile)]

private def budget (value : BudgetArtifactEncoding) : Json :=
  Json.mkObj
    [("id", nat value.id),
     ("sessionId", nat value.sessionId),
     ("planId", nat value.planId),
     ("limits", profile value.limits),
     ("realizedProfile", profile value.realizedProfile)]

private def counts (value : ArtifactEncoding) : Json :=
  Json.mkObj
    [("fields", nat value.fields.length),
     ("invariants", nat value.invariants.length),
     ("futures", nat value.futures.length),
     ("sessions", nat value.sessions.length),
     ("plans", nat value.plans.length),
     ("budgets", nat value.budgets.length)]

private inductive Value where
  | v2 (value : ArtifactEncoding)
  | v3 (value : ArtifactV3Encoding)

private def Value.base : Value → ArtifactEncoding
  | .v2 value => value
  | .v3 value => value.base

private def Value.formatVersion : Value → Nat
  | .v2 _ => 2
  | .v3 _ => 3

private structure Record where
  startOffset : Nat
  endOffset : Nat
  value : Value

/-! The public durable decoder is deliberately simple and structurally
recursive over every tagged payload pair.  The interpreter used by this
standalone command has a fixed recursion guard, so large valid artifacts need
an equivalent tail-recursive outer-envelope pass.  Semantic payload admission
still calls the exact existing `artifactCodec.decode`; no second artifact
decoder exists here. -/

private inductive BodyResult where
  | accepted (payload following : List UInt8) (consumed : Nat)
  | torn
  | corrupt

private def decodeBodyFast : List UInt8 → List UInt8 → Nat → BodyResult
  | _, [], _ => .torn
  | reversed, tag :: rest, consumed =>
      if tag = Durable.endTag then
        .accepted reversed.reverse rest (consumed + 1)
      else if tag = Durable.dataTag then
        match rest with
        | [] => .torn
        | byte :: following =>
            decodeBodyFast (byte :: reversed) following (consumed + 2)
      else
        .corrupt

private inductive FrameResult where
  | accepted (value : Value) (following : List UInt8) (consumed : Nat)
  | torn
  | refused

/-- Stack-safe envelope parsing followed by the Lean-owned canonical artifact
decoder.  Header/version/domain and exact re-encoding are all mandatory. -/
private def decodeFrameFast : List UInt8 → FrameResult
  | [] => .torn
  | [m0] => if m0 = Durable.magic₀ then .torn else .refused
  | [m0, m1] =>
      if m0 = Durable.magic₀ ∧ m1 = Durable.magic₁ then .torn else .refused
  | [m0, m1, version] =>
      if m0 = Durable.magic₀ ∧ m1 = Durable.magic₁ ∧
          (version = artifactFormat.version ∨
            version = ArtifactV3Durable.artifactV3Format.version) then
        .torn
      else
        .refused
  | m0 :: m1 :: version :: domain :: body =>
      if m0 = Durable.magic₀ ∧ m1 = Durable.magic₁ ∧
          domain = artifactFormat.domain then
        match decodeBodyFast [] body 0 with
        | .accepted payload following consumed =>
            if version = artifactFormat.version then
              match artifactCodec.decode payload with
              | some value => .accepted (.v2 value) following (4 + consumed)
              | none => .refused
            else if version = ArtifactV3Durable.artifactV3Format.version then
              match ArtifactV3Durable.artifactV3Codec.decode payload with
              | some value => .accepted (.v3 value) following (4 + consumed)
              | none => .refused
            else
              .refused
        | .torn => .torn
        | .corrupt => .refused
      else
        .refused

private structure DecodedJournal where
  records : List Record
  completedPrefixLength : Nat

private def decodeJournalFast (limit : Nat) (bytes : List UInt8) : Except Error DecodedJournal :=
  let rec loop : Nat → Nat → List UInt8 → List Record → Except Error DecodedJournal
    | remaining, offset, bytes, reversed =>
        if bytes = [] then
          pure ⟨reversed.reverse, offset⟩
        else if remaining = 0 then
          throw (.recordLimit limit)
        else
          match decodeFrameFast bytes with
          | .accepted value following consumed =>
              loop (remaining - 1) (offset + consumed) following
                (⟨offset, offset + consumed, value⟩ :: reversed)
          | .torn => throw (.tornFrame offset (offset + bytes.length))
          | .refused => throw (.refusedFrame offset)
  loop limit 0 bytes []

private def holeKind : HoleKind → String
  | .field => "field"
  | .opaque => "opaque"

private def analysisTag : AnalysisTag → String
  | .mergeSafe => "mergeSafe"
  | .monotoneSafe => "monotoneSafe"

private def statusShape : StatusShape → String
  | .exact => "exact"
  | .provisional => "provisional"
  | .forkedClosed => "forkedClosed"
  | .forkedOpen => "forkedOpen"
  | .absent => "absent"
  | .pending => "pending"

private def hole (value : HoleRow) : Json :=
  Json.mkObj
    [("path", array (value.path.map nat)),
     ("fieldId", nat value.field.value),
     ("kind", holeKind value.kind)]

private def query (value : QueryRow) : Json :=
  Json.mkObj
    [("id", nat value.id.value),
     ("schemaId", nat value.schema.value),
     ("resultId", nat value.result.value),
     ("programId", nat value.program.value),
     ("reads", array (value.reads.map fun id => nat id.value)),
     ("holes", array (value.holes.map hole)),
     ("analyses", array (value.analyses.map fun tag => analysisTag tag))]

private def resolution : ResolutionRow → Json
  | .preserveFork => Json.mkObj [("kind", "preserveFork")]
  | .named id => Json.mkObj [("kind", "named"), ("id", nat id.value)]

private def visibility : VisibilityRow → Json
  | .inspectable => Json.mkObj [("kind", "inspectable")]
  | .opaque reason =>
      Json.mkObj [("kind", "opaque"), ("reasonId", nat reason.value)]

private def disclosure : Option DisclosureRow → Json
  | none => .null
  | some .shown => Json.mkObj [("kind", "shown")]
  | some (.hidden reason) =>
      Json.mkObj [("kind", "hidden"), ("reasonId", nat reason.value)]

private def result (value : ResultRow) : Json :=
  Json.mkObj
    [("id", nat value.id.value),
     ("queryId", nat value.query.value),
     ("futureId", nat value.future.value),
     ("resolution", resolution value.resolution),
     ("surfaceId", nat value.surface.value),
     ("status", statusShape value.status),
     ("effect", array (value.effect.map fun shape => statusShape shape)),
     ("visibility", visibility value.visibility),
     ("disclosure", disclosure value.disclosure)]

private def certificate (value : CertificateRow) : Json :=
  Json.mkObj
    [("id", nat value.id.value),
     ("futureId", nat value.future.value),
     ("worldId", nat value.world.value)]

private def statusEffect : Value → Json
  | .v2 _ => .null
  | .v3 value =>
      Json.mkObj
        [("schemaId", nat value.schema.value),
         ("worldIds", array (value.worlds.map fun id => nat id.value)),
         ("counts", Json.mkObj
           [("queries", nat value.queries.length),
            ("results", nat value.results.length),
            ("certificates", nat value.certificates.length)]),
         ("queries", array (value.queries.map query)),
         ("results", array (value.results.map result)),
         ("certificates", array (value.certificates.map certificate))]

private def inspectRecord (index : Nat) (record : Record) : Json :=
  let base := record.value.base
  Json.mkObj
    [("index", nat index),
     ("startOffset", nat record.startOffset),
     ("endOffset", nat record.endOffset),
     ("formatVersion", nat record.value.formatVersion),
     ("declaration", declaration base.declaration),
     ("counts", counts base),
     ("fields", array (base.fields.map field)),
     ("invariants", array (base.invariants.map invariant)),
     ("futures", array (base.futures.map future)),
     ("sessions", array (base.sessions.map session)),
     ("plans", array (base.plans.map plan)),
     ("budgets", array (base.budgets.map budget)),
     ("statusEffect", statusEffect record.value)]

private def validateRecord (bounds : Bounds) (index : Nat)
    (record : Record) : Except Error Unit :=
  match record.value with
  | .v2 value =>
      match ProjectionV2.validate (validationConfig bounds)
          (ProjectionV2.Projection.ofEncoding value) with
      | .ok _ => pure ()
      | .error _ => throw (.invalidV2 index)
  | .v3 value =>
      match ProjectionV3.validate (validationConfigV3 bounds)
          (ProjectionV3.Projection.ofEncoding value) with
      | .ok _ => pure ()
      | .error _ => throw (.invalidV3 index)

private def renderJournal (bounds : Bounds) (decoded : DecodedJournal) : Except Error Json := do
  for (record, index) in decoded.records.zipIdx do
    validateRecord bounds index record
  pure <| Json.mkObj
    [("schema", "uwueave/preo-inspection/v1"),
     ("authority", "diagnostic-only"),
     ("recordCount", nat decoded.records.length),
     ("completedPrefixLength", nat decoded.completedPrefixLength),
     ("records", array (decoded.records.zipIdx.map fun pair =>
        inspectRecord pair.2 pair.1))]

private def decodeBounded (bounds : Bounds) (bytes : List UInt8) :
    Except Error DecodedJournal := do
  if bytes.length ≤ bounds.maxInputBytes then pure ()
  else throw (.inputLimit bytes.length bounds.maxInputBytes)
  decodeJournalFast bounds.maxRecords bytes

/-- Inspect a complete canonical concatenation of v2/v3 frames.  Any torn or
corrupt suffix refuses the entire request; partial JSON is never returned. -/
def inspectJournal (bounds : Bounds) (bytes : List UInt8) : Except Error Json := do
  renderJournal bounds (← decodeBounded bounds bytes)

/-- Inspect exactly one canonical v2 or v3 frame. -/
def inspectFrame (bounds : Bounds) (bytes : List UInt8) : Except Error Json := do
  let decoded ← decodeBounded bounds bytes
  if decoded.records.length = 1 then
    renderJournal bounds decoded
  else
    throw (.expectedOneFrame decoded.records.length)

end Uwueave.Preo.ArtifactInspectionV1
