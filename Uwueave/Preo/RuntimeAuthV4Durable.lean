/-
# Uwueave.Preo.RuntimeAuthV4Durable — canonical auth-manifest bytes

This leaf gives the neutral runtime-auth manifest *sidecar* a canonical,
versioned, domain-separated durable frame.  It is not the existing
`Uwueave.RuntimeAuthV4` request wire and must never be submitted as request or
signature bytes. Prefix decoding preserves arbitrary trailing
bytes for journals; `decodeManifestExact` and `decodeBounded` accept only a
whole frame.  Decoding returns neutral rows and reconstructs no signature,
authority, membership, history, frontier, or storage proof.
-/
import Uwueave.Preo.RuntimeAuthV4Data
import Uwueave.Preo.ArtifactDurableCore

namespace Uwueave.Preo.RuntimeAuthV4Durable

open Uwueave
open Uwueave.Preo.RuntimeAuthV4
open Uwueave.Preo.ArtifactDurable

set_option autoImplicit false

abbrev Bytes := Durable.Bytes

private def bytesWire : WireCodec Bytes := WireCodec.list byteWire

private def parsePrefix : Bytes → Bytes → Option Bytes
  | [], bytes => some bytes
  | _ :: _, [] => none
  | expected :: rest, actual :: bytes =>
      if actual = expected then parsePrefix rest bytes else none

private theorem parsePrefix_append (framing trailing : Bytes) :
    parsePrefix framing (framing ++ trailing) = some trailing := by
  induction framing with
  | nil => rfl
  | cons byte rest ih => simp [parsePrefix, ih]

private def prefixedWire {alpha : Type} (framing : Bytes)
    (codec : WireCodec alpha) : WireCodec alpha where
  encode value := framing ++ codec.encode value
  parse bytes := do
    let trailing ← parsePrefix framing bytes
    codec.parse trailing
  parse_encode_append := by
    intro value trailing
    simp [List.append_assoc, parsePrefix_append, codec.parse_encode_append]

/-- Every field is explicitly tagged in addition to being length-delimited. -/
private def fieldWire {alpha : Type} (tag : UInt8)
    (codec : WireCodec alpha) : WireCodec alpha :=
  prefixedWire [tag] codec

private def nodeWire : WireCodec NodeRow :=
  ((fieldWire 1 bytesWire).prod (fieldWire 2 natWire)).xmap
    (fun value => (value.stable, value.kernelIndex))
    (fun raw => ⟨raw.1, raw.2⟩)
    (by intro value; cases value; rfl)

private def grantWire : WireCodec GrantScopeRow :=
  ((fieldWire 3 natWire).prod
    ((fieldWire 4 natWire).prod (fieldWire 5 natWire))).xmap
    (fun value => (value.id, (value.parent, value.scope)))
    (fun raw => ⟨raw.1, raw.2.1, raw.2.2⟩)
    (by intro value; cases value; rfl)

private abbrev SignedIdentityRaw :=
  Bytes × (Bytes × (Nat × (Nat × (Nat × Bytes))))

private def signedIdentityWire : WireCodec SignedIdentityRaw :=
  (fieldWire 16 bytesWire).prod ((fieldWire 17 bytesWire).prod
    ((fieldWire 18 natWire).prod ((fieldWire 19 natWire).prod
      ((fieldWire 20 natWire).prod (fieldWire 21 bytesWire)))))

private abbrev MoveRaw :=
  Bytes × (Nat × (NodeRow × (Option NodeRow × (Nat × Bytes))))

private def moveWire : WireCodec MoveRaw :=
  (fieldWire 22 bytesWire).prod ((fieldWire 23 natWire).prod
    ((fieldWire 24 nodeWire).prod
      ((fieldWire 25 (WireCodec.option nodeWire)).prod
        ((fieldWire 26 natWire).prod (fieldWire 27 bytesWire)))))

private def signedMoveWire : WireCodec SignedMoveRow :=
  (signedIdentityWire.prod moveWire).xmap
    (fun value =>
      ((value.document,
        (value.genesis,
          (value.signatureAlgorithm,
            (value.issuer, (value.keyEpoch, value.nonce))))),
       (value.operationId,
        (value.lamport,
          (value.child,
            (value.destination, (value.cite, value.signature)))))))
    (fun raw =>
      ⟨raw.1.1, raw.1.2.1, raw.1.2.2.1, raw.1.2.2.2.1,
        raw.1.2.2.2.2.1, raw.1.2.2.2.2.2,
        raw.2.1, raw.2.2.1, raw.2.2.2.1, raw.2.2.2.2.1,
        raw.2.2.2.2.2.1, raw.2.2.2.2.2.2⟩)
    (by intro value; cases value; rfl)

private abbrev ContextIdentityRaw :=
  GrantScopeRow × (Bytes × (Bytes × (Bytes × Bytes)))

private def contextIdentityWire : WireCodec ContextIdentityRaw :=
  (fieldWire 32 grantWire).prod ((fieldWire 33 bytesWire).prod
    ((fieldWire 34 bytesWire).prod
      ((fieldWire 35 bytesWire).prod (fieldWire 36 bytesWire))))

private def contextWire : WireCodec ContextRow :=
  (contextIdentityWire.prod
    ((fieldWire 37 natWire.list).prod (fieldWire 38 natWire.list))).xmap
    (fun value =>
      ((value.citedGrant,
        (value.substrateDigest,
          (value.historyHeadDigest, (value.originId, value.versionId)))),
       (value.roster, value.participants)))
    (fun raw =>
      ⟨raw.1.1, raw.1.2.1, raw.1.2.2.1, raw.1.2.2.2.1,
        raw.1.2.2.2.2, raw.2.1, raw.2.2⟩)
    (by intro value; cases value; rfl)

def manifestWire : WireCodec Manifest :=
  ((fieldWire 48 signedMoveWire).prod (fieldWire 49 contextWire)).xmap
    (fun value => (value.move, value.context))
    (fun raw => ⟨raw.1, raw.2⟩)
    (by intro value; cases value; rfl)

def manifestCodec : Durable.CanonicalCodec Manifest :=
  canonicalCodecOfWire manifestWire

/-- Format 4, domain 162: isolated from preoscript artifact domains 160/161. -/
def manifestFormat : Durable.FormatTag := ⟨4, 162⟩

def manifestBytes (value : Manifest) : Bytes :=
  Durable.encodeValue manifestCodec manifestFormat value

/-- Decode one prefix frame, retaining following journal bytes exactly. -/
def decodeManifest (bytes : Bytes) : Option (Manifest × Bytes) :=
  Durable.decodeValue manifestCodec manifestFormat bytes

/-- Decode exactly one whole manifest frame. -/
def decodeManifestExact (bytes : Bytes) : Option Manifest :=
  match decodeManifest bytes with
  | some (value, []) => some value
  | _ => none

theorem decodeManifest_manifestBytes_append (value : Manifest) (trailing : Bytes) :
    decodeManifest (manifestBytes value ++ trailing) = some (value, trailing) :=
  Durable.decodeValue_encodeValue_append manifestCodec manifestFormat value trailing

theorem decodeManifestExact_manifestBytes (value : Manifest) :
    decodeManifestExact (manifestBytes value) = some value := by
  unfold decodeManifestExact
  have decoded : decodeManifest (manifestBytes value) = some (value, []) := by
    simpa only [List.append_nil] using
      decodeManifest_manifestBytes_append value []
  rw [decoded]

inductive DecodeRefusal where
  | tooLarge
  | malformed
  | trailingBytes
  deriving DecidableEq

inductive DecodeOutcome where
  | refused (reason : DecodeRefusal)
  | accepted (manifest : Manifest)
  deriving DecidableEq

/-- Stable numeric tags for host diagnostics; these are not authority tokens. -/
def DecodeRefusal.tag : DecodeRefusal → Nat
  | .tooLarge => 1
  | .malformed => 2
  | .trailingBytes => 3

def DecodeOutcome.tag : DecodeOutcome → Nat
  | .accepted _ => 0
  | .refused reason => reason.tag

/-- Bound the complete supplied frame before parsing and refuse journal tails
at this whole-frame API. -/
def decodeBounded (maxBytes : Nat) (bytes : Bytes) : DecodeOutcome :=
  if bytes.length > maxBytes then .refused .tooLarge
  else
    match decodeManifest bytes with
    | none => .refused .malformed
    | some (value, []) => .accepted value
    | some (_, _ :: _) => .refused .trailingBytes

theorem decodeBounded_manifestBytes (maxBytes : Nat) (value : Manifest)
    (bounded : (manifestBytes value).length ≤ maxBytes) :
    decodeBounded maxBytes (manifestBytes value) = .accepted value := by
  unfold decodeBounded
  rw [if_neg (Nat.not_lt.mpr bounded)]
  have decoded : decodeManifest (manifestBytes value) = some (value, []) := by
    simpa only [List.append_nil] using
      decodeManifest_manifestBytes_append value []
  rw [decoded]

theorem decodeBounded_refuses_trailing (maxBytes : Nat) (value : Manifest)
    (byte : UInt8) (trailing : Bytes)
    (bounded : (manifestBytes value ++ byte :: trailing).length ≤ maxBytes) :
    decodeBounded maxBytes (manifestBytes value ++ byte :: trailing) =
      .refused .trailingBytes := by
  unfold decodeBounded
  have notTooLarge : ¬ (manifestBytes value ++ byte :: trailing).length > maxBytes :=
    Nat.not_lt.mpr bounded
  rw [if_neg notTooLarge]
  rw [decodeManifest_manifestBytes_append value (byte :: trailing)]

/-- Changing the sidecar version or domain cannot alias a valid manifest
frame. -/
theorem changed_format_refused (format : Durable.FormatTag)
    (different : format ≠ manifestFormat) (value : Manifest)
    (trailing : Bytes) :
    Durable.decodeValue manifestCodec format (manifestBytes value ++ trailing) = none := by
  unfold manifestBytes Durable.encodeValue Durable.decodeValue
  simp only [Durable.decodeFor_encodeFrame_ne format manifestFormat
    (Ne.symm different) (manifestCodec.encode value) trailing]
  rfl

end Uwueave.Preo.RuntimeAuthV4Durable
