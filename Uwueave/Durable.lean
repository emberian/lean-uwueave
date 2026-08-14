/-
# Uwueave.Durable — a logical durability rung for canonical bytes.

This module separates three things which are often collapsed into the word
"persistence":

  1. a first-order value codec supplies canonical payload bytes;
  2. this module frames those bytes with a magic header, version, domain, and
     unambiguous terminator, then appends frames to a byte journal;
  3. a deployment may arrange for observed storage images to be prefixes of
     attempted appends.

Only (1) and (2), plus recovery from images *assumed* to have the shape in
(3), are proved here.  In particular, no theorem in this file claims that a
filesystem append, rename, flush, sector write, host serializer, or power-loss
event has prefix semantics.  Those are deployment premises, represented at
the end of the file but never manufactured by the logical codec.

## Wire format

An envelope is encoded as

```
magic₀ magic₁ version domain (data byte)* end
```

where one payload byte `b` is represented by the pair `data b`.  The distinct
one-byte `end` tag terminates the frame.  A decoder therefore cannot confuse a
payload byte with framing, and every proper truncation before `end` is refused.
The expansion is intentionally simple rather than compact: this is a semantic
rung on which a denser codec can later be refined.

## Recovery claim

`recover` accepts complete, correctly tagged frames from the front and stops at
the first refusal.  `recover_crashPrefix` proves that a canonical journal plus
one explicitly described torn frame recovers exactly the complete prefix.
`recover_crashPrefix_monotone` says that increasing the complete record prefix
can only increase the recovered record prefix.  Neither result derives the
premise that real storage produces such an image.

## Boundaries

  * ⟨TERMINAL for this format⟩ Version and domain are single bytes.  A wider
    namespace can be placed in canonical payload bytes or introduced by a new
    version; it must not silently reinterpret this format.
  * ⟨TERMINAL⟩ The format detects truncation, bad framing, and tag mismatch.
    It has no checksum and does not claim to detect arbitrary bit corruption.
  * The logical layer is paid for artifact projections:
    `Preo.ArtifactDurable` supplies canonical `List UInt8`, version/domain
    separation, and logical torn-tail recovery.
  * ⟨UNDONE U-0027⟩ No refinement proves that a host serializer emits those bytes
    byte-for-byte, or connects a file descriptor, database transaction, flush
    primitive, or filesystem crash observation to the required prefix shape.
    `DeploymentAssumptions` names that missing boundary.
-/
import Std

namespace Uwueave.Durable

/-- The first-order byte carrier used by the logical format. -/
abbrev Bytes := List UInt8

/-- A codec whose accepted representation is canonical as well as round-trip
correct.  `decode_encode` prevents rejection of encoded values;
`encode_decode` prevents two accepted byte strings from denoting one value.

This is a logical interface.  An implementation in another language still
owes a refinement proof or differential check against its chosen inhabitant. -/
structure CanonicalCodec (α : Type) where
  encode : α → Bytes
  decode : Bytes → Option α
  decode_encode : ∀ a, decode (encode a) = some a
  encode_decode : ∀ {bytes a}, decode bytes = some a → encode a = bytes

/-- The semantic version and domain separator carried by every frame. -/
structure FormatTag where
  version : UInt8
  domain : UInt8
  deriving DecidableEq, Repr

/-- A decoded envelope.  Payload bytes have not yet been interpreted by a
`CanonicalCodec`. -/
structure Envelope where
  tag : FormatTag
  payload : Bytes
  deriving DecidableEq, Repr

def magic₀ : UInt8 := 213
def magic₁ : UInt8 := 74
def dataTag : UInt8 := 0
def endTag : UInt8 := 1

/-- Payload bytes without their final terminator.  Each byte occupies one
tagged pair. -/
def encodeData : Bytes → Bytes
  | [] => []
  | b :: rest => dataTag :: b :: encodeData rest

theorem encodeData_append (left right : Bytes) :
    encodeData (left ++ right) = encodeData left ++ encodeData right := by
  induction left with
  | nil => simp [encodeData]
  | cons b rest ih => simp [encodeData, ih]

/-- The self-delimiting payload representation. -/
def encodePayload (payload : Bytes) : Bytes :=
  encodeData payload ++ [endTag]

/-- Decode one self-delimiting payload and leave the following bytes untouched.
An absent terminator, a data tag without its byte, or any unknown tag refuses. -/
def decodePayload : Bytes → Option (Bytes × Bytes)
  | [] => none
  | tag :: [] =>
      if tag = endTag then
        some ([], [])
      else
        none
  | tag :: b :: tail =>
      if tag = endTag then
        some ([], b :: tail)
      else if tag = dataTag then
        match decodePayload tail with
        | none => none
        | some (payload, following) => some (b :: payload, following)
      else
        none

theorem decodePayload_end (following : Bytes) :
    decodePayload (endTag :: following) = some ([], following) := by
  cases following <;> simp [decodePayload, endTag]

theorem decodePayload_data (b : UInt8) (following : Bytes) :
    decodePayload (dataTag :: b :: following) =
      match decodePayload following with
      | none => none
      | some (payload, rest) => some (b :: payload, rest) := by
  simp [decodePayload, dataTag, endTag]

/-- Decoding crosses encoded data pairs transparently and begins decoding at
the supplied suffix. -/
theorem decodePayload_encodeData_append (payload suffix : Bytes) :
    decodePayload (encodeData payload ++ suffix) =
      match decodePayload suffix with
      | none => none
      | some (rest, following) => some (payload ++ rest, following) := by
  induction payload with
  | nil =>
      simp only [encodeData, List.nil_append]
      cases h : decodePayload suffix <;> simp
  | cons b payload ih =>
      simp only [encodeData, List.cons_append]
      rw [decodePayload_data, ih]
      cases h : decodePayload suffix with
      | none => rfl
      | some result =>
          cases result
          rfl

/-- Payload framing is a left inverse even when another frame follows. -/
theorem decodePayload_encodePayload_append (payload following : Bytes) :
    decodePayload (encodePayload payload ++ following) =
      some (payload, following) := by
  rw [encodePayload, List.append_assoc,
    decodePayload_encodeData_append]
  simp only [List.singleton_append]
  rw [decodePayload_end]
  simp

/-- An encoded data prefix with no terminator is refused. -/
theorem decodePayload_encodeData_none (payload : Bytes) :
    decodePayload (encodeData payload) = none := by
  simpa using decodePayload_encodeData_append payload []

/-- Stopping immediately after a data tag is also refused. -/
theorem decodePayload_encodeData_tag_none (payload : Bytes) :
    decodePayload (encodeData payload ++ [dataTag]) = none := by
  rw [decodePayload_encodeData_append]
  simp [decodePayload, dataTag, endTag]

/-- Encode one versioned, domain-separated envelope. -/
def encodeEnvelope (envelope : Envelope) : Bytes :=
  magic₀ :: magic₁ :: envelope.tag.version :: envelope.tag.domain ::
    encodePayload envelope.payload

/-- Decode one envelope, returning any bytes belonging to later frames.
Bad magic is refused; version and domain remain data until `decodeFor` checks
them against the requested `FormatTag`. -/
def decodeEnvelope : Bytes → Option (Envelope × Bytes)
  | m₀ :: m₁ :: version :: domain :: body =>
      if m₀ = magic₀ ∧ m₁ = magic₁ then
        match decodePayload body with
        | none => none
        | some (payload, following) =>
            some (⟨⟨version, domain⟩, payload⟩, following)
      else
        none
  | _ => none

/-- Envelope bytes decode exactly and do not consume a following journal. -/
theorem decodeEnvelope_encodeEnvelope_append
    (envelope : Envelope) (following : Bytes) :
    decodeEnvelope (encodeEnvelope envelope ++ following) =
      some (envelope, following) := by
  cases envelope with
  | mk tag payload =>
    cases tag with
    | mk version domain =>
      simp [encodeEnvelope, decodeEnvelope,
        decodePayload_encodePayload_append, magic₀, magic₁]

/-- Decode one frame only when both its semantic version and domain match. -/
def decodeFor (expected : FormatTag) (bytes : Bytes) :
    Option (Bytes × Bytes) :=
  match decodeEnvelope bytes with
  | none => none
  | some (envelope, following) =>
      if envelope.tag = expected then
        some (envelope.payload, following)
      else
        none

/-- Canonical bytes framed for one version and domain. -/
def encodeFrame (tag : FormatTag) (payload : Bytes) : Bytes :=
  encodeEnvelope ⟨tag, payload⟩

/-- The tagged frame codec round-trips while preserving following bytes. -/
theorem decodeFor_encodeFrame_append
    (tag : FormatTag) (payload following : Bytes) :
    decodeFor tag (encodeFrame tag payload ++ following) =
      some (payload, following) := by
  simp [decodeFor, encodeFrame, decodeEnvelope_encodeEnvelope_append]

/-- Version and domain separation are enforced, not display metadata: a frame
encoded for one tag is refused by every distinct tag. -/
theorem decodeFor_encodeFrame_ne (expected actual : FormatTag)
    (different : actual ≠ expected) (payload following : Bytes) :
    decodeFor expected (encodeFrame actual payload ++ following) = none := by
  simp [decodeFor, encodeFrame, decodeEnvelope_encodeEnvelope_append,
    different]

/-- Frame and then interpret a value using its canonical first-order codec. -/
def encodeValue {α : Type} (codec : CanonicalCodec α)
    (tag : FormatTag) (value : α) : Bytes :=
  encodeFrame tag (codec.encode value)

/-- Decode and interpret one value, refusing noncanonical payload bytes even
when the surrounding envelope is well-formed. -/
def decodeValue {α : Type} (codec : CanonicalCodec α)
    (tag : FormatTag) (bytes : Bytes) : Option (α × Bytes) := do
  let (payload, following) ← decodeFor tag bytes
  let value ← codec.decode payload
  if codec.encode value = payload then
    some (value, following)
  else
    none

/-- Value encoding and decoding round-trip through both codec layers. -/
theorem decodeValue_encodeValue_append {α : Type}
    (codec : CanonicalCodec α) (tag : FormatTag)
    (value : α) (following : Bytes) :
    decodeValue codec tag (encodeValue codec tag value ++ following) =
      some (value, following) := by
  simp [decodeValue, encodeValue, decodeFor_encodeFrame_append,
    codec.decode_encode]

/-! ## Torn frames: every pre-terminator stopping point. -/

/-- `TornFrame tag payload bytes` describes every place an append of that
frame can stop before writing its terminator: in the header, between payload
pairs, or between a data tag and its byte.  The relation says nothing about
whether a real storage system can only produce these images. -/
inductive TornFrame (tag : FormatTag) (payload : Bytes) : Bytes → Prop where
  | empty : TornFrame tag payload []
  | afterMagic₀ : TornFrame tag payload [magic₀]
  | afterMagic₁ : TornFrame tag payload [magic₀, magic₁]
  | afterVersion : TornFrame tag payload [magic₀, magic₁, tag.version]
  | atDataBoundary (done pending : Bytes)
      (split : payload = done ++ pending) :
      TornFrame tag payload
        ([magic₀, magic₁, tag.version, tag.domain] ++ encodeData done)
  | afterDataTag (done pending : Bytes) (next : UInt8)
      (split : payload = done ++ next :: pending) :
      TornFrame tag payload
        ([magic₀, magic₁, tag.version, tag.domain] ++
          encodeData done ++ [dataTag])

/-- Every explicitly torn frame is refused; recovery never invents a partial
payload. -/
theorem decodeFor_tornFrame {tag : FormatTag} {payload torn : Bytes}
    (h : TornFrame tag payload torn) : decodeFor tag torn = none := by
  cases h with
  | empty => simp [decodeFor, decodeEnvelope]
  | afterMagic₀ => simp [decodeFor, decodeEnvelope]
  | afterMagic₁ => simp [decodeFor, decodeEnvelope]
  | afterVersion => simp [decodeFor, decodeEnvelope]
  | atDataBoundary done pending split =>
      simp [decodeFor, decodeEnvelope, decodePayload_encodeData_none,
        magic₀, magic₁]
  | afterDataTag done pending next split =>
      simp [decodeFor, decodeEnvelope, decodePayload_encodeData_tag_none,
        magic₀, magic₁]

/-- A torn-frame witness really is a byte prefix of the complete frame. -/
theorem tornFrame_isPrefix {tag : FormatTag} {payload torn : Bytes}
    (h : TornFrame tag payload torn) :
    torn.IsPrefix (encodeFrame tag payload) := by
  cases h with
  | empty =>
      exact ⟨encodeFrame tag payload, rfl⟩
  | afterMagic₀ =>
      refine ⟨magic₁ :: tag.version :: tag.domain ::
        encodePayload payload, ?_⟩
      simp [encodeFrame, encodeEnvelope]
  | afterMagic₁ =>
      refine ⟨tag.version :: tag.domain :: encodePayload payload, ?_⟩
      simp [encodeFrame, encodeEnvelope]
  | afterVersion =>
      refine ⟨tag.domain :: encodePayload payload, ?_⟩
      simp [encodeFrame, encodeEnvelope]
  | atDataBoundary done pending split =>
      subst payload
      refine ⟨encodeData pending ++ [endTag], ?_⟩
      simp [encodeFrame, encodeEnvelope, encodePayload, encodeData_append,
        List.append_assoc]
  | afterDataTag done pending next split =>
      subst payload
      refine ⟨next :: encodeData pending ++ [endTag], ?_⟩
      simp [encodeFrame, encodeEnvelope, encodePayload, encodeData,
        encodeData_append,
        List.append_assoc]

/-- A torn frame is not the complete frame: the former refuses while the
latter decodes. -/
theorem tornFrame_ne_encodeFrame {tag : FormatTag} {payload torn : Bytes}
    (h : TornFrame tag payload torn) : torn ≠ encodeFrame tag payload := by
  intro equal
  have refused := decodeFor_tornFrame h
  have complete := decodeFor_encodeFrame_append tag payload []
  simp only [List.append_nil] at complete
  rw [equal, complete] at refused
  contradiction

/-- Thus every `TornFrame` is a proper byte prefix, not merely a refused
arbitrary string. -/
theorem tornFrame_isProperPrefix {tag : FormatTag} {payload torn : Bytes}
    (h : TornFrame tag payload torn) :
    torn.IsPrefix (encodeFrame tag payload) ∧
      torn ≠ encodeFrame tag payload :=
  ⟨tornFrame_isPrefix h, tornFrame_ne_encodeFrame h⟩

/-! ## Append-only journals and prefix recovery. -/

/-- The canonical journal encoding is concatenation of canonical frames. -/
def encodeJournal (tag : FormatTag) : List Bytes → Bytes
  | [] => []
  | payload :: rest => encodeFrame tag payload ++ encodeJournal tag rest

/-- Append one complete frame to an existing byte image.  Correct use starts
from a canonical journal; appending to arbitrary corrupt bytes is intentionally
not repaired or reinterpreted. -/
def append (tag : FormatTag) (journal payload : Bytes) : Bytes :=
  journal ++ encodeFrame tag payload

theorem encodeJournal_append (tag : FormatTag) (left right : List Bytes) :
    encodeJournal tag (left ++ right) =
      encodeJournal tag left ++ encodeJournal tag right := by
  induction left with
  | nil => simp [encodeJournal]
  | cons payload rest ih => simp [encodeJournal, ih, List.append_assoc]

/-- Appending at the byte layer agrees with snoc at the logical record layer. -/
theorem append_encodeJournal (tag : FormatTag)
    (records : List Bytes) (payload : Bytes) :
    append tag (encodeJournal tag records) payload =
      encodeJournal tag (records ++ [payload]) := by
  simp [append, encodeJournal_append, encodeJournal]

/-- Fuel makes recovery total even on malicious frames that fail to consume
bytes.  `recover` supplies byte length as fuel; canonical frames consume at
least one byte, so this is more than enough for canonical journals. -/
def recoverFuel (tag : FormatTag) : Nat → Bytes → List Bytes
  | 0, _ => []
  | fuel + 1, bytes =>
      match decodeFor tag bytes with
      | none => []
      | some (payload, following) =>
          payload :: recoverFuel tag fuel following

/-- Recover the maximal leading sequence of complete, correctly tagged
frames, stopping at the first refusal. -/
def recover (tag : FormatTag) (bytes : Bytes) : List Bytes :=
  recoverFuel tag bytes.length bytes

/-- One frame always contributes at least one byte. -/
theorem one_le_length_encodeFrame (tag : FormatTag) (payload : Bytes) :
    1 ≤ (encodeFrame tag payload).length := by
  simp [encodeFrame, encodeEnvelope]

/-- A canonical journal contains at least as many bytes as records. -/
theorem length_le_length_encodeJournal (tag : FormatTag) (records : List Bytes) :
    records.length ≤ (encodeJournal tag records).length := by
  induction records with
  | nil => simp [encodeJournal]
  | cons payload rest ih =>
      simp only [List.length_cons, encodeJournal, List.length_append]
      calc
        rest.length + 1 ≤ (encodeJournal tag rest).length + 1 :=
          Nat.add_le_add_right ih 1
        _ ≤ (encodeJournal tag rest).length + (encodeFrame tag payload).length :=
          Nat.add_le_add_left (one_le_length_encodeFrame tag payload)
            (encodeJournal tag rest).length
        _ = (encodeFrame tag payload).length +
              (encodeJournal tag rest).length := Nat.add_comm _ _

/-- With enough fuel, a complete canonical journal decodes exactly. -/
theorem recoverFuel_encodeJournal (tag : FormatTag) (records : List Bytes) :
    ∀ fuel, records.length ≤ fuel →
      recoverFuel tag fuel (encodeJournal tag records) = records := by
  induction records with
  | nil =>
      intro fuel h
      cases fuel <;> simp [recoverFuel, encodeJournal, decodeFor, decodeEnvelope]
  | cons payload rest ih =>
      intro fuel h
      cases fuel with
      | zero => simp at h
      | succ fuel =>
          simp only [List.length_cons, Nat.succ_le_succ_iff] at h
          simp [recoverFuel, encodeJournal, decodeFor_encodeFrame_append,
            ih fuel h]

/-- Canonical journals round-trip exactly through recovery. -/
theorem recover_encodeJournal (tag : FormatTag) (records : List Bytes) :
    recover tag (encodeJournal tag records) = records := by
  apply recoverFuel_encodeJournal
  exact length_le_length_encodeJournal tag records

/-- Recovery after a canonical append returns the old records followed by the
new payload. -/
theorem recover_append (tag : FormatTag)
    (records : List Bytes) (payload : Bytes) :
    recover tag (append tag (encodeJournal tag records) payload) =
      records ++ [payload] := by
  rw [append_encodeJournal, recover_encodeJournal]

/-- A complete prefix followed by any refused suffix recovers the complete
prefix, provided the byte image supplies the evident record-count fuel. -/
theorem recoverFuel_encodeJournal_append_refused
    (tag : FormatTag) (records : List Bytes) (suffix : Bytes)
    (refused : decodeFor tag suffix = none) :
    ∀ fuel, records.length ≤ fuel →
      recoverFuel tag fuel (encodeJournal tag records ++ suffix) = records := by
  induction records with
  | nil =>
      intro fuel h
      cases fuel with
      | zero => rfl
      | succ fuel => simp [recoverFuel, encodeJournal, refused]
  | cons payload rest ih =>
      intro fuel h
      cases fuel with
      | zero => simp at h
      | succ fuel =>
          simp only [List.length_cons, Nat.succ_le_succ_iff] at h
          rw [encodeJournal]
          rw [List.append_assoc]
          simp [recoverFuel, decodeFor_encodeFrame_append, ih fuel h]

/-- **Crash-prefix recovery.** A canonical journal followed by one torn next
frame recovers exactly the complete journal.  This is a theorem about an image
already proved to be `TornFrame`, not a theorem about storage hardware. -/
theorem recover_crashPrefix (tag : FormatTag) (records : List Bytes)
    {next torn : Bytes} (h : TornFrame tag next torn) :
    recover tag (encodeJournal tag records ++ torn) = records := by
  apply recoverFuel_encodeJournal_append_refused tag records torn
    (decodeFor_tornFrame h)
  change records.length ≤ (encodeJournal tag records ++ torn).length
  rw [List.length_append]
  exact Nat.le_trans (length_le_length_encodeJournal tag records)
    (Nat.le_add_right _ _)

/-- **Crash-prefix monotonicity.** If the complete record prefix in one valid
crash image is a list prefix of another, recovery preserves that order. -/
theorem recover_crashPrefix_monotone (tag : FormatTag)
    {earlier later : List Bytes} (grows : earlier.IsPrefix later)
    {next₁ torn₁ next₂ torn₂ : Bytes}
    (h₁ : TornFrame tag next₁ torn₁) (h₂ : TornFrame tag next₂ torn₂) :
    (recover tag (encodeJournal tag earlier ++ torn₁)).IsPrefix
      (recover tag (encodeJournal tag later ++ torn₂)) := by
  rw [recover_crashPrefix tag earlier h₁,
    recover_crashPrefix tag later h₂]
  exact grows

/-! ## The deployment boundary, named but not assumed. -/

/-- Premises a deployment needs before applying the logical crash-prefix
theorems to real storage.  This module constructs no inhabitant.

`observedPrefix` must connect each observed post-crash byte image to the
attempted append as either complete frames plus a `TornFrame`; `appendOrder`
must exclude reordering complete records; `flushDurable` must state the
platform-specific persistence guarantee.  Their exact quantification belongs
to a deployment model, so this semantic rung records them only as propositions
and consumes none of them. -/
structure DeploymentAssumptions where
  observedPrefix : Prop
  appendOrder : Prop
  flushDurable : Prop

end Uwueave.Durable
