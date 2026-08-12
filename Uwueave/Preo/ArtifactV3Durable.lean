/-
# Uwueave.Preo.ArtifactV3Durable — canonical durable V3 bytes

The V3 payload begins with the complete, unchanged V2 payload and appends
query, result, and certificate lists.  It uses version 3 of the existing
preoscript artifact domain.  Decoding returns neutral rows only and never
reconstructs a typed program, result proof, or certificate proof.
-/
import Uwueave.Preo.ArtifactV3Data
import Uwueave.Preo.ArtifactDurableCore

namespace Uwueave.Preo.ArtifactV3Durable

open Uwueave
open Uwueave.Preo.Artifact
open Uwueave.Preo.ArtifactV3
open Uwueave.Preo.ArtifactDurable

set_option autoImplicit false

abbrev Bytes := Durable.Bytes

private def fieldIdWire : WireCodec FieldId :=
  natWire.xmap FieldId.value FieldId.mk (by intro value; cases value; rfl)

private def queryIdWire : WireCodec QueryId :=
  natWire.xmap QueryId.value QueryId.mk (by intro value; cases value; rfl)

private def resultIdWire : WireCodec ResultId :=
  natWire.xmap ResultId.value ResultId.mk (by intro value; cases value; rfl)

private def schemaIdWire : WireCodec SchemaId :=
  natWire.xmap SchemaId.value SchemaId.mk (by intro value; cases value; rfl)

private def programIdWire : WireCodec ProgramId :=
  natWire.xmap ProgramId.value ProgramId.mk (by intro value; cases value; rfl)

private def certificateIdWire : WireCodec CertificateId :=
  natWire.xmap CertificateId.value CertificateId.mk (by intro value; cases value; rfl)

private def worldIdWire : WireCodec WorldId :=
  natWire.xmap WorldId.value WorldId.mk (by intro value; cases value; rfl)

private def resolutionIdWire : WireCodec ResolutionId :=
  natWire.xmap ResolutionId.value ResolutionId.mk (by intro value; cases value; rfl)

private def surfaceIdWire : WireCodec SurfaceId :=
  natWire.xmap SurfaceId.value SurfaceId.mk (by intro value; cases value; rfl)

private def reasonIdWire : WireCodec ReasonId :=
  natWire.xmap ReasonId.value ReasonId.mk (by intro value; cases value; rfl)

private def futureIdWire : WireCodec FutureId :=
  natWire.xmap FutureId.value FutureId.mk (by intro value; cases value; rfl)

private def holeKindTag : HoleKind → UInt8
  | .field => 0
  | .opaque => 1

private def holeKindOfTag : UInt8 → Option HoleKind
  | 0 => some .field
  | 1 => some .opaque
  | _ => none

private theorem holeKind_tag_roundtrip (value : HoleKind) :
    holeKindOfTag (holeKindTag value) = some value := by cases value <;> rfl

private def holeKindWire : WireCodec HoleKind :=
  taggedWire holeKindTag holeKindOfTag holeKind_tag_roundtrip

private def holeWire : WireCodec HoleRow :=
  (natWire.list.prod (fieldIdWire.prod holeKindWire)).xmap
    (fun value => (value.path, (value.field, value.kind)))
    (fun value => ⟨value.1, value.2.1, value.2.2⟩)
    (by intro value; cases value; rfl)

private def analysisTagTag : AnalysisTag → UInt8
  | .mergeSafe => 0
  | .monotoneSafe => 1

private def analysisTagOfTag : UInt8 → Option AnalysisTag
  | 0 => some .mergeSafe
  | 1 => some .monotoneSafe
  | _ => none

private theorem analysisTag_tag_roundtrip (value : AnalysisTag) :
    analysisTagOfTag (analysisTagTag value) = some value := by cases value <;> rfl

private def analysisTagWire : WireCodec AnalysisTag :=
  taggedWire analysisTagTag analysisTagOfTag analysisTag_tag_roundtrip

private def queryWire : WireCodec QueryRow :=
  (queryIdWire.prod (schemaIdWire.prod (resultIdWire.prod
    (programIdWire.prod (fieldIdWire.list.prod
      (holeWire.list.prod analysisTagWire.list)))))).xmap
    (fun value => (value.id, (value.schema, (value.result,
      (value.program, (value.reads, (value.holes, value.analyses)))))))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1,
      value.2.2.2.2.1, value.2.2.2.2.2.1, value.2.2.2.2.2.2⟩)
    (by intro value; cases value; rfl)

private def resolutionWire : WireCodec ResolutionRow where
  encode
    | .preserveFork => [0]
    | .named id => 1 :: resolutionIdWire.encode id
  parse
    | [] => none
    | tag :: trailing =>
        if tag = 0 then some (.preserveFork, trailing)
        else if tag = 1 then
          match resolutionIdWire.parse trailing with
          | none => none
          | some (id, rest) => some (.named id, rest)
        else none
  parse_encode_append := by
    intro value trailing
    cases value with
    | preserveFork => simp
    | named id => simp [resolutionIdWire.parse_encode_append]

private def statusShapeTag : StatusShape → UInt8
  | .exact => 0
  | .provisional => 1
  | .forkedClosed => 2
  | .forkedOpen => 3
  | .absent => 4
  | .pending => 5

private def statusShapeOfTag : UInt8 → Option StatusShape
  | 0 => some .exact
  | 1 => some .provisional
  | 2 => some .forkedClosed
  | 3 => some .forkedOpen
  | 4 => some .absent
  | 5 => some .pending
  | _ => none

private theorem statusShape_tag_roundtrip (value : StatusShape) :
    statusShapeOfTag (statusShapeTag value) = some value := by cases value <;> rfl

private def statusShapeWire : WireCodec StatusShape :=
  taggedWire statusShapeTag statusShapeOfTag statusShape_tag_roundtrip

private def visibilityWire : WireCodec VisibilityRow where
  encode
    | .inspectable => [0]
    | .opaque reason => 1 :: reasonIdWire.encode reason
  parse
    | [] => none
    | tag :: trailing =>
        if tag = 0 then some (.inspectable, trailing)
        else if tag = 1 then
          match reasonIdWire.parse trailing with
          | none => none
          | some (reason, rest) => some (.opaque reason, rest)
        else none
  parse_encode_append := by
    intro value trailing
    cases value with
    | inspectable => simp
    | «opaque» reason => simp [reasonIdWire.parse_encode_append]

private def disclosureWire : WireCodec DisclosureRow where
  encode
    | .shown => [0]
    | .hidden reason => 1 :: reasonIdWire.encode reason
  parse
    | [] => none
    | tag :: trailing =>
        if tag = 0 then some (.shown, trailing)
        else if tag = 1 then
          match reasonIdWire.parse trailing with
          | none => none
          | some (reason, rest) => some (.hidden reason, rest)
        else none
  parse_encode_append := by
    intro value trailing
    cases value with
    | shown => simp
    | hidden reason => simp [reasonIdWire.parse_encode_append]

private def resultWire : WireCodec ResultRow :=
  (resultIdWire.prod (queryIdWire.prod (futureIdWire.prod
    (resolutionWire.prod (surfaceIdWire.prod (statusShapeWire.prod
      (statusShapeWire.list.prod (visibilityWire.prod disclosureWire.option)))))))).xmap
    (fun value => (value.id, (value.query, (value.future,
      (value.resolution, (value.surface, (value.status,
        (value.effect, (value.visibility, value.disclosure)))))))))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1,
      value.2.2.2.2.1, value.2.2.2.2.2.1, value.2.2.2.2.2.2.1,
      value.2.2.2.2.2.2.2.1, value.2.2.2.2.2.2.2.2⟩)
    (by intro value; cases value; rfl)

private def certificateWire : WireCodec CertificateRow :=
  (certificateIdWire.prod (futureIdWire.prod worldIdWire)).xmap
    (fun value => (value.id, (value.future, value.world)))
    (fun value => ⟨value.1, value.2.1, value.2.2⟩)
    (by intro value; cases value; rfl)

/-- Prefix codec for the append-only V3 payload. -/
def artifactV3Wire : WireCodec ArtifactV3Encoding :=
  (artifactWire.prod (schemaIdWire.prod (worldIdWire.list.prod
    (queryWire.list.prod (resultWire.list.prod certificateWire.list))))).xmap
    (fun value => (value.base,
      (value.schema, (value.worlds,
        (value.queries, (value.results, value.certificates))))))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2.1,
      value.2.2.2.2.1, value.2.2.2.2.2⟩)
    (by intro value; cases value; rfl)

def artifactV3Codec : Durable.CanonicalCodec ArtifactV3Encoding :=
  canonicalCodecOfWire artifactV3Wire

theorem decodeArtifactV3_encode (value : ArtifactV3Encoding) :
    artifactV3Codec.decode (artifactV3Codec.encode value) = some value :=
  artifactV3Codec.decode_encode value

/-! ## Versioned, domain-separated V3 frame -/

/-- Format v3 in the existing preoscript-artifact domain. -/
def artifactV3Format : Durable.FormatTag := ⟨3, 161⟩

def projectionBytes (value : ArtifactV3Encoding) : Bytes :=
  Durable.encodeValue artifactV3Codec artifactV3Format value

def decodeProjection (bytes : Bytes) : Option (ArtifactV3Encoding × Bytes) :=
  Durable.decodeValue artifactV3Codec artifactV3Format bytes

theorem decodeProjection_projectionBytes_append
    (value : ArtifactV3Encoding) (trailing : Bytes) :
    decodeProjection (projectionBytes value ++ trailing) = some (value, trailing) :=
  Durable.decodeValue_encodeValue_append artifactV3Codec artifactV3Format value trailing

theorem decodeProjection_projectionBytes (value : ArtifactV3Encoding) :
    decodeProjection (projectionBytes value) = some (value, []) := by
  simpa using decodeProjection_projectionBytes_append value []

/-- A V3 frame is never silently admitted by the unchanged V2 decoder. -/
theorem v2_decoder_refuses_v3 (value : ArtifactV3Encoding) (trailing : Bytes) :
    ArtifactDurable.decodeProjection (projectionBytes value ++ trailing) = none := by
  unfold projectionBytes ArtifactDurable.decodeProjection Durable.encodeValue
    Durable.decodeValue
  rw [Durable.decodeFor_encodeFrame_ne ArtifactDurable.artifactFormat artifactV3Format
    (by decide) (artifactV3Codec.encode value) trailing]
  simp

/-- A V2 frame is never silently admitted by the V3 decoder. -/
theorem v3_decoder_refuses_v2 (value : ArtifactEncoding) (trailing : Bytes) :
    decodeProjection (ArtifactDurable.projectionBytes value ++ trailing) = none := by
  unfold decodeProjection ArtifactDurable.projectionBytes Durable.encodeValue
    Durable.decodeValue
  rw [Durable.decodeFor_encodeFrame_ne artifactV3Format ArtifactDurable.artifactFormat
    (by decide) (ArtifactDurable.artifactCodec.encode value) trailing]
  simp

end Uwueave.Preo.ArtifactV3Durable
