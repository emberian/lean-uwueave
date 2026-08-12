/-
# Uwueave.Preo.ArtifactDurable — canonical durable bytes for semantic artifacts

`Artifact.ArtifactEncoding` is already the neutral first-order projection of a
checked preoscript artifact. This module gives that projection a canonical byte
codec and places it in `Durable`'s versioned, domain-separated frames.

The direction remains one-way with respect to proof authority. Decoding bytes
produces an `ArtifactEncoding`; it does not reconstruct a checked declaration,
`Spec.Verdict`, future certificate, schedule, or plan. In particular this file
does not strengthen `Artifact.FirstOrderCodec`.

## Format

  * Naturals use the canonical unary form `1^n 0`. The terminating zero is part
    of the value. Exact decoding rejects extra zeroes and every byte except the
    two grammar bytes, so there is no accepted overlong representation.
  * Products concatenate their component encodings.
  * Lists carry their canonical natural length followed by exactly that many
    elements.
  * Options and sum-shaped artifact enums carry explicit one-byte constructor
    tags. Unknown tags refuse.
  * The complete artifact projection is framed by `Durable` with an explicit
    format version and artifact domain byte.

`artifactCodec` checks the raw parser's value by re-encoding it before accepting
exact bytes. Thus even a future permissive parser cannot make a noncanonical
byte string authoritative.

## Boundaries

  * ⟨TERMINAL for format v2⟩ Unary naturals favor a tiny proof surface over
    density. A compact varint is a new format version, not a silent replacement.
  * ⟨TERMINAL⟩ The decoder returns first-order data only. No theorem here
    turns decoded artifacts back into proof-carrying sources.
  * The canonical-byte and logical torn-tail layers are paid:
    `projectionBytes` is exact and `two_frames_then_torn_third` proves recovery
    under an explicit `Durable.TornFrame` premise.
  * ⟨UNDONE⟩ No deployment refinement proves that a host serializer agrees
    byte-for-byte with `projectionBytes`, or that filesystem, flush,
    atomic-sector, or power-loss observations satisfy `Durable.TornFrame` and
    its prefix premise. `Durable` names rather than manufactures those
    assumptions.
-/
import Uwueave.Preo.ArtifactData
import Uwueave.Durable

namespace Uwueave.Preo.ArtifactDurable

open Uwueave
open Uwueave.Preo.Artifact

set_option autoImplicit false

abbrev Bytes := Durable.Bytes

/-! ## §0. Stack-safe executable framing -/

/-- Tail-recursive execution of the durable data-pair encoding.  This exists
for large artifacts run through Lean's interpreter, whose fixed recursion
guard rejects the structurally recursive `Durable.encodeData` after roughly
ten thousand payload bytes. -/
def stackSafeEncodeData (payload : Bytes) : Bytes :=
  (payload.foldl
    (fun encoded byte => byte :: Durable.dataTag :: encoded) []).reverse

private theorem stackSafeEncodeData_go (payload accumulator : Bytes) :
    (payload.foldl
      (fun encoded byte => byte :: Durable.dataTag :: encoded)
      accumulator).reverse =
    accumulator.reverse ++ Durable.encodeData payload := by
  induction payload generalizing accumulator with
  | nil => simp [Durable.encodeData]
  | cons byte payload ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp [Durable.encodeData, List.append_assoc]

/-- The executable data encoder is byte-identical to the logical encoder. -/
theorem stackSafeEncodeData_eq (payload : Bytes) :
    stackSafeEncodeData payload = Durable.encodeData payload := by
  simpa [stackSafeEncodeData] using stackSafeEncodeData_go payload []

/-- Generic stack-safe durable framing for any version/domain and payload. -/
def stackSafeEncodeFrame (tag : Durable.FormatTag) (payload : Bytes) : Bytes :=
  [Durable.magic₀, Durable.magic₁, tag.version, tag.domain] ++
    stackSafeEncodeData payload ++ [Durable.endTag]

/-- Stack-safe framing preserves the exact canonical durable wire format. -/
theorem stackSafeEncodeFrame_eq (tag : Durable.FormatTag) (payload : Bytes) :
    stackSafeEncodeFrame tag payload = Durable.encodeFrame tag payload := by
  simp [stackSafeEncodeFrame, Durable.encodeFrame, Durable.encodeEnvelope,
    Durable.encodePayload, stackSafeEncodeData_eq]

/-- Generic stack-safe value framing; semantic payload bytes remain owned by
the supplied canonical codec. -/
def stackSafeEncodeValue {alpha : Type} (codec : Durable.CanonicalCodec alpha)
    (tag : Durable.FormatTag) (value : alpha) : Bytes :=
  stackSafeEncodeFrame tag (codec.encode value)

/-- Stack-safe value framing is byte-identical to `Durable.encodeValue`. -/
theorem stackSafeEncodeValue_eq {alpha : Type}
    (codec : Durable.CanonicalCodec alpha) (tag : Durable.FormatTag)
    (value : alpha) :
    stackSafeEncodeValue codec tag value = Durable.encodeValue codec tag value := by
  simp [stackSafeEncodeValue, Durable.encodeValue, stackSafeEncodeFrame_eq]

/-- The canonical decoder accepts stack-safe bytes and preserves arbitrary
following journal bytes exactly. -/
theorem decodeValue_stackSafeEncodeValue_append {alpha : Type}
    (codec : Durable.CanonicalCodec alpha) (tag : Durable.FormatTag)
    (value : alpha) (following : Bytes) :
    Durable.decodeValue codec tag
      (stackSafeEncodeValue codec tag value ++ following) =
        some (value, following) := by
  rw [stackSafeEncodeValue_eq]
  exact Durable.decodeValue_encodeValue_append codec tag value following

/- Reserved framing bytes are adversarial payload data here; a changed tag is
refused, and a nonempty following suffix is returned rather than consumed. -/
namespace StackSafeExamples

def tag : Durable.FormatTag := ⟨7, 9⟩
def payload : Bytes :=
  [Durable.magic₀, Durable.dataTag, Durable.endTag, 255]

theorem reserved_payload_and_trailing_exact :
    Durable.decodeFor tag (stackSafeEncodeFrame tag payload ++ [91, 92]) =
      some (payload, [91, 92]) := by
  rw [stackSafeEncodeFrame_eq]
  exact Durable.decodeFor_encodeFrame_append tag payload [91, 92]

theorem changed_version_refused :
    Durable.decodeFor ⟨8, tag.domain⟩
      (stackSafeEncodeFrame tag payload ++ [91]) = none := by
  rw [stackSafeEncodeFrame_eq]
  exact Durable.decodeFor_encodeFrame_ne ⟨8, tag.domain⟩ tag (by decide)
    payload [91]

theorem changed_domain_refused :
    Durable.decodeFor ⟨tag.version, 10⟩
      (stackSafeEncodeFrame tag payload) = none := by
  rw [stackSafeEncodeFrame_eq]
  simpa using Durable.decodeFor_encodeFrame_ne ⟨tag.version, 10⟩ tag
    (by decide) payload []

end StackSafeExamples

/-! ## §1. A compositional prefix codec -/

/-- A prefix codec parses exactly one value and returns trailing bytes. The law
is the compositional roundtrip needed to assemble the artifact codec. Canonical
exact acceptance is added separately by `canonicalCodecOfWire`. -/
structure WireCodec (α : Type) where
  encode : α → Bytes
  parse : Bytes → Option (α × Bytes)
  parse_encode_append : ∀ value trailing,
    parse (encode value ++ trailing) = some (value, trailing)

/-- Transport a wire codec across an explicit retraction. -/
def WireCodec.xmap {α β : Type} (codec : WireCodec α)
    (to : β → α) (backward : α → β)
    (backward_to : ∀ value, backward (to value) = value) :
    WireCodec β where
  encode value := codec.encode (to value)
  parse bytes :=
    match codec.parse bytes with
    | none => none
    | some (value, trailing) => some (backward value, trailing)
  parse_encode_append := by
    intro value trailing
    rw [codec.parse_encode_append]
    simp [backward_to]

/-- One literal byte. -/
def byteWire : WireCodec UInt8 where
  encode value := [value]
  parse
    | [] => none
    | value :: trailing => some (value, trailing)
  parse_encode_append := by intro value trailing; rfl

/-- Canonical natural bytes. Zero is `[0]`; successor prepends `[1]`. -/
def encodeNat : Nat → Bytes
  | 0 => [0]
  | n + 1 => 1 :: encodeNat n

/-- Prefix parser for canonical unary naturals. Unknown bytes refuse. -/
def parseNat : Bytes → Option (Nat × Bytes)
  | [] => none
  | byte :: trailing =>
      if byte = 0 then
        some (0, trailing)
      else if byte = 1 then
        match parseNat trailing with
        | none => none
        | some (value, rest) => some (value + 1, rest)
      else
        none

theorem parseNat_encodeNat_append (value : Nat) (trailing : Bytes) :
    parseNat (encodeNat value ++ trailing) = some (value, trailing) := by
  induction value with
  | zero => simp [encodeNat, parseNat]
  | succ value ih => simp [encodeNat, parseNat, ih]

def natWire : WireCodec Nat :=
  ⟨encodeNat, parseNat, parseNat_encodeNat_append⟩

/-- Product encoding is concatenation, in field order. -/
def WireCodec.prod {α β : Type} (left : WireCodec α) (right : WireCodec β) :
    WireCodec (α × β) where
  encode value := left.encode value.1 ++ right.encode value.2
  parse bytes := do
    let (a, afterA) ← left.parse bytes
    let (b, afterB) ← right.parse afterA
    some ((a, b), afterB)
  parse_encode_append := by
    intro value trailing
    cases value with
    | mk a b =>
      simp [List.append_assoc, left.parse_encode_append,
        right.parse_encode_append]

/-- Option tags: `0` is `none`; `1` is `some` followed by its payload. -/
def WireCodec.option {α : Type} (codec : WireCodec α) : WireCodec (Option α) where
  encode
    | none => [0]
    | some value => 1 :: codec.encode value
  parse
    | [] => none
    | tag :: trailing =>
        if tag = 0 then
          some (none, trailing)
        else if tag = 1 then
          match codec.parse trailing with
          | none => none
          | some (value, rest) => some (some value, rest)
        else
          none
  parse_encode_append := by
    intro value trailing
    cases value with
    | none => simp
    | some value => simp [codec.parse_encode_append]

/-- Concatenated element bytes, without a length. -/
def encodeItems {α : Type} (codec : WireCodec α) : List α → Bytes
  | [] => []
  | value :: rest => codec.encode value ++ encodeItems codec rest

/-- Parse exactly `count` elements. -/
def parseItems {α : Type} (codec : WireCodec α) : Nat → Bytes →
    Option (List α × Bytes)
  | 0, bytes => some ([], bytes)
  | count + 1, bytes => do
      let (value, afterValue) ← codec.parse bytes
      let (rest, trailing) ← parseItems codec count afterValue
      some (value :: rest, trailing)

theorem parseItems_encodeItems_append {α : Type} (codec : WireCodec α)
    (values : List α) (trailing : Bytes) :
    parseItems codec values.length (encodeItems codec values ++ trailing) =
      some (values, trailing) := by
  induction values with
  | nil => simp [encodeItems, parseItems]
  | cons value rest ih =>
      simp [encodeItems, parseItems, List.append_assoc,
        codec.parse_encode_append, ih]

/-- Lists carry a canonical natural length followed by exactly that many
elements. -/
def WireCodec.list {α : Type} (codec : WireCodec α) : WireCodec (List α) where
  encode values := encodeNat values.length ++ encodeItems codec values
  parse bytes := do
    let (count, afterCount) ← parseNat bytes
    parseItems codec count afterCount
  parse_encode_append := by
    intro values trailing
    simp [List.append_assoc, parseNat_encodeNat_append,
      parseItems_encodeItems_append]

/-- A finite constructor-tag codec. Unknown tags refuse. -/
def taggedWire {α : Type} (tag : α → UInt8) (ofTag : UInt8 → Option α)
    (roundtrip : ∀ value, ofTag (tag value) = some value) : WireCodec α where
  encode value := [tag value]
  parse
    | [] => none
    | byte :: trailing =>
        match ofTag byte with
        | none => none
        | some value => some (value, trailing)
  parse_encode_append := by
    intro value trailing
    simp [roundtrip]

/-! ## §2. Exact canonical acceptance -/

/-- Exact decoding accepts a raw parse only if it consumes the input and its
value re-encodes byte-for-byte. -/
def exactDecode {α : Type} (codec : WireCodec α) (bytes : Bytes) : Option α :=
  match codec.parse bytes with
  | some (value, []) =>
      if codec.encode value = bytes then some value else none
  | _ => none

theorem exactDecode_encode {α : Type} (codec : WireCodec α) (value : α) :
    exactDecode codec (codec.encode value) = some value := by
  have parsed := codec.parse_encode_append value []
  simp only [List.append_nil] at parsed
  simp [exactDecode, parsed]

theorem exactDecode_encode_append_cons {α : Type} (codec : WireCodec α)
    (value : α) (byte : UInt8) (trailing : Bytes) :
    exactDecode codec (codec.encode value ++ byte :: trailing) = none := by
  unfold exactDecode
  rw [codec.parse_encode_append value (byte :: trailing)]

theorem encode_of_exactDecode {α : Type} (codec : WireCodec α)
    {bytes : Bytes} {value : α} (h : exactDecode codec bytes = some value) :
    codec.encode value = bytes := by
  unfold exactDecode at h
  split at h
  · next parsed heq =>
      split at h
      · next canonical =>
          have valueEq : parsed = value := Option.some.inj h
          subst valueEq
          exact canonical
      · contradiction
  · contradiction

/-- Any prefix codec becomes a `Durable.CanonicalCodec` by exact consumption
and re-encoding. -/
def canonicalCodecOfWire {α : Type} (codec : WireCodec α) :
    Durable.CanonicalCodec α where
  encode := codec.encode
  decode := exactDecode codec
  decode_encode := exactDecode_encode codec
  encode_decode := encode_of_exactDecode codec

theorem canonicalCodecOfWire_append_cons_refused {α : Type}
    (codec : WireCodec α) (value : α) (byte : UInt8) (trailing : Bytes) :
    (canonicalCodecOfWire codec).decode
      ((canonicalCodecOfWire codec).encode value ++ byte :: trailing) = none :=
  exactDecode_encode_append_cons codec value byte trailing

def natCodec : Durable.CanonicalCodec Nat := canonicalCodecOfWire natWire

/-- The first explicit overlong form is rejected: `[0]` already encodes zero,
so a second terminator cannot be accepted as part of the same natural. -/
theorem nat_overlong_zero_refused : natCodec.decode [0, 0] = none := by rfl

/-- Bytes outside the unary grammar are rejected rather than coerced. -/
theorem nat_unknown_tag_refused : natCodec.decode [2, 0] = none := by rfl

/-! ## §3. Constructor codecs -/

def currencyTag : Currency → UInt8
  | .peerBarrier => 0
  | .arbiterCut => 1
  | .networkRound => 2
  | .userPrompt => 3
  | .rollback => 4

def currencyOfTag (tag : UInt8) : Option Currency :=
  if tag = 0 then some .peerBarrier
  else if tag = 1 then some .arbiterCut
  else if tag = 2 then some .networkRound
  else if tag = 3 then some .userPrompt
  else if tag = 4 then some .rollback
  else none

theorem currencyOfTag_currencyTag (value : Currency) :
    currencyOfTag (currencyTag value) = some value := by
  cases value <;> rfl

def currencyWire : WireCodec Currency :=
  taggedWire currencyTag currencyOfTag currencyOfTag_currencyTag

/-- Evidence-key tags: `0` is absent and `1` carries a natural key. -/
def evidenceKeyWire : WireCodec EvidenceKey where
  encode
    | .none => [0]
    | .named key => 1 :: encodeNat key
  parse
    | [] => none
    | tag :: trailing =>
        if tag = 0 then some (.none, trailing)
        else if tag = 1 then
          match parseNat trailing with
          | none => none
          | some (key, rest) => some (.named key, rest)
        else none
  parse_encode_append := by
    intro value trailing
    cases value with
    | none => simp
    | named key => simp [parseNat_encodeNat_append]

/-- Origin tags: `0` is ambient and `1` carries a crossing index. -/
def originWire : WireCodec OriginArtifact where
  encode
    | .ambient => [0]
    | .crossing index => 1 :: encodeNat index
  parse
    | [] => none
    | tag :: trailing =>
        if tag = 0 then some (.ambient, trailing)
        else if tag = 1 then
          match parseNat trailing with
          | none => none
          | some (index, rest) => some (.crossing index, rest)
        else none
  parse_encode_append := by
    intro value trailing
    cases value with
    | ambient => simp
    | crossing index => simp [parseNat_encodeNat_append]

/-- Verdict tags: `0` is proof-originated freedom; `1` carries the two encoded
clash witnesses. The bytes remain data and never become a `Spec.Verdict`. -/
def verdictWire : WireCodec VerdictEvidence where
  encode
    | .free => [0]
    | .clash left right =>
        1 :: (natWire.list.encode left ++ natWire.list.encode right)
  parse
    | [] => none
    | tag :: trailing =>
        if tag = 0 then some (.free, trailing)
        else if tag = 1 then
          match natWire.list.parse trailing with
          | none => none
          | some (left, afterLeft) =>
              match natWire.list.parse afterLeft with
              | none => none
              | some (right, rest) => some (.clash left right, rest)
        else none
  parse_encode_append := by
    intro value trailing
    cases value with
    | free => simp
    | clash left right =>
        simp [List.append_assoc, WireCodec.list,
          parseNat_encodeNat_append, parseItems_encodeItems_append]

/-! ## §4. Product views of every first-order artifact structure -/

def declarationWire : WireCodec DeclarationArtifactEncoding :=
  (natWire.prod (natWire.prod natWire)).xmap
    (fun value => (value.id, (value.stateTypeId, value.schemaVersion)))
    (fun value => ⟨value.1, value.2.1, value.2.2⟩)
    (by intro value; cases value; rfl)

def fieldWire : WireCodec FieldArtifactEncoding :=
  (natWire.prod (natWire.prod (natWire.prod
    (natWire.prod natWire.option)))).xmap
    (fun value => (value.id, (value.declarationId,
      (value.kindId, (value.carrierTypeId, value.keyTypeId)))))
    (fun value => ⟨value.1, value.2.1, value.2.2.1,
      value.2.2.2.1, value.2.2.2.2⟩)
    (by intro value; cases value; rfl)

def invariantWire : WireCodec InvariantArtifactEncoding :=
  (natWire.prod (natWire.prod (natWire.prod verdictWire))).xmap
    (fun value => (value.id,
      (value.declarationId, (value.carrierTypeId, value.verdict))))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2⟩)
    (by intro value; cases value; rfl)

def futureWire : WireCodec FutureArtifactEncoding :=
  (natWire.prod (natWire.prod (natWire.prod natWire))).xmap
    (fun value => (value.id,
      (value.declarationId, (value.worldTypeId, value.relationId))))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2⟩)
    (by intro value; cases value; rfl)

def demandWire : WireCodec DemandArtifact :=
  (currencyWire.prod (natWire.list.prod (natWire.prod
    (natWire.prod (evidenceKeyWire.prod (natWire.prod natWire)))))).xmap
    (fun value => (value.currency, (value.participants,
      (value.scope, (value.epoch,
        (value.evidence, (value.round, value.barrier)))))))
    (fun value => ⟨value.1, value.2.1, value.2.2.1,
      value.2.2.2.1, value.2.2.2.2.1,
      value.2.2.2.2.2.1, value.2.2.2.2.2.2⟩)
    (by intro value; cases value; rfl)

def obligationWire : WireCodec ObligationArtifact :=
  (originWire.prod demandWire).xmap
    (fun value => (value.origin, value.demand))
    (fun value => ⟨value.1, value.2⟩)
    (by intro value; cases value; rfl)

def sessionWire : WireCodec SessionArtifactEncoding :=
  (natWire.prod (natWire.prod (natWire.prod obligationWire.list))).xmap
    (fun value => (value.id,
      (value.declarationId, (value.crossings, value.obligations))))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2⟩)
    (by intro value; cases value; rfl)

def profileEntryWire : WireCodec (Currency × Nat) :=
  currencyWire.prod natWire

def planWire : WireCodec PlanArtifactEncoding :=
  (natWire.prod (natWire.prod
    (demandWire.list.prod profileEntryWire.list))).xmap
    (fun value => (value.id,
      (value.sessionId, (value.actions, value.profile))))
    (fun value => ⟨value.1, value.2.1, value.2.2.1, value.2.2.2⟩)
    (by intro value; cases value; rfl)

def budgetWire : WireCodec BudgetArtifactEncoding :=
  (natWire.prod (natWire.prod (natWire.prod
    (profileEntryWire.list.prod profileEntryWire.list)))).xmap
    (fun value => (value.id, (value.sessionId,
      (value.planId, (value.limits, value.realizedProfile)))))
    (fun value => ⟨value.1, value.2.1, value.2.2.1,
      value.2.2.2.1, value.2.2.2.2⟩)
    (by intro value; cases value; rfl)

def artifactWire : WireCodec ArtifactEncoding :=
  (declarationWire.prod (fieldWire.list.prod
    (invariantWire.list.prod (futureWire.list.prod
      (sessionWire.list.prod (planWire.list.prod budgetWire.list)))))).xmap
    (fun value => (value.declaration, (value.fields,
      (value.invariants, (value.futures,
        (value.sessions, (value.plans, value.budgets)))))))
    (fun value => ⟨value.1, value.2.1, value.2.2.1,
      value.2.2.2.1, value.2.2.2.2.1, value.2.2.2.2.2.1,
      value.2.2.2.2.2.2⟩)
    (by intro value; cases value; rfl)

/-- The requested canonical durable codec for the neutral artifact projection. -/
def artifactCodec : Durable.CanonicalCodec ArtifactEncoding :=
  canonicalCodecOfWire artifactWire

/-- Prefix parsing supports stream composition and preserves trailing bytes. -/
theorem parseArtifact_encode_append (value : ArtifactEncoding)
    (trailing : Bytes) :
    artifactWire.parse (artifactWire.encode value ++ trailing) =
      some (value, trailing) :=
  artifactWire.parse_encode_append value trailing

/-- Exact artifact bytes round-trip canonically. -/
theorem decodeArtifact_encode (value : ArtifactEncoding) :
    artifactCodec.decode (artifactCodec.encode value) = some value :=
  artifactCodec.decode_encode value

/-! ## §5. Versioned, domain-separated projection bytes -/

/-- Format v2 in the preoscript-artifact domain. Version 2 adds the witnessed
five-currency budget list, so old v1 frames are refused rather than silently
decoded under a changed product shape. These bytes are semantic
separators, not host MIME metadata. -/
def artifactFormat : Durable.FormatTag := ⟨2, 161⟩

def wrongVersion : Durable.FormatTag := ⟨1, artifactFormat.domain⟩
def wrongDomain : Durable.FormatTag := ⟨artifactFormat.version, 162⟩

/-- Canonical artifact payload bytes inside one durable envelope. -/
def projectionBytes (value : ArtifactEncoding) : Bytes :=
  Durable.encodeValue artifactCodec artifactFormat value

/-- Decode one projection frame and preserve following journal bytes. -/
def decodeProjection (bytes : Bytes) : Option (ArtifactEncoding × Bytes) :=
  Durable.decodeValue artifactCodec artifactFormat bytes

/-- The exact framed roundtrip, including arbitrary trailing bytes. -/
theorem decodeProjection_projectionBytes_append
    (value : ArtifactEncoding) (trailing : Bytes) :
    decodeProjection (projectionBytes value ++ trailing) =
      some (value, trailing) :=
  Durable.decodeValue_encodeValue_append artifactCodec artifactFormat value trailing

/-- Exact one-frame decoding consumes the frame and nothing else. -/
theorem decodeProjection_projectionBytes (value : ArtifactEncoding) :
    decodeProjection (projectionBytes value) = some (value, []) := by
  simpa using decodeProjection_projectionBytes_append value []

/-- A v2 artifact cannot be decoded as the superseded v1 format. -/
theorem wrong_version_refused (value : ArtifactEncoding) (trailing : Bytes) :
    Durable.decodeValue artifactCodec wrongVersion
      (projectionBytes value ++ trailing) = none := by
  unfold projectionBytes Durable.encodeValue Durable.decodeValue
  rw [Durable.decodeFor_encodeFrame_ne wrongVersion artifactFormat
    (by decide) (artifactCodec.encode value) trailing]
  simp

/-- The same version in another domain is also refused. -/
theorem wrong_domain_refused (value : ArtifactEncoding) (trailing : Bytes) :
    Durable.decodeValue artifactCodec wrongDomain
      (projectionBytes value ++ trailing) = none := by
  unfold projectionBytes Durable.encodeValue Durable.decodeValue
  rw [Durable.decodeFor_encodeFrame_ne wrongDomain artifactFormat
    (by decide) (artifactCodec.encode value) trailing]
  simp

end Uwueave.Preo.ArtifactDurable
