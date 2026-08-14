/-
# Uwueave.Preo.ArtifactJournalKernel — executable recovery for artifact journals

This module is the kernel-facing journal policy for canonical preoscript
artifacts.  The logical journal is exactly a concatenation of
`ArtifactDurable.projectionBytes`; this file neither wraps those frames in a
second codec nor gives Rust permission to reconstruct semantic proofs.

The scanner validates every completed payload with `artifactCodec`, reports
the exact half-open byte boundary `[startOffset, endOffset)` of every accepted
record, and stops at the first non-record.  The stop is classified as:

* `cleanEOF` — the byte image ends exactly after a completed frame;
* `tornFinal` — the remaining suffix is a strict syntactic prefix of a
  correctly tagged v2 frame; or
* `corrupt` — bad magic, a wrong complete version/domain field, an unknown
  framing tag, or a framed payload that is not one canonical
  `ArtifactEncoding`.

The distinction is deliberately syntactic.  Framing cannot detect an
arbitrary mutation of an opaque payload data byte.  A mutation is reported
only when it makes the artifact payload noncanonical; integrity against other
mutations belongs to a separate authenticated/checksummed physical record
layer.  Likewise, no theorem here says that a filesystem observation is a
prefix, that a flush reached stable media, or that a host checksum implements
any particular digest.

Wire constants inherited without reinterpretation from `ArtifactDurable`:

```
D5 4A 02 A1 (00 payload-byte)* 01
```

Thus a payload of length `n` occupies exactly `5 + 2*n` journal bytes.
-/
import Uwueave.Preo.ArtifactDurableCore

namespace Uwueave.Preo.ArtifactJournalKernel

open Uwueave
open Uwueave.Preo.Artifact
open Uwueave.Preo.ArtifactDurable

set_option autoImplicit false

abbrev Bytes := Durable.Bytes

/-! ## §1. Stable wire facts and exact one-frame validation -/

/-- The exact bytes at the beginning of every v2 artifact frame. -/
def frameHeader : Bytes :=
  [Durable.magic₀, Durable.magic₁,
    artifactFormat.version, artifactFormat.domain]

/-- Validate exactly one canonical artifact frame.  A valid first frame with
trailing bytes is refused: callers scanning a stream must use `scan` and its
returned boundaries instead. -/
def validateOne (bytes : Bytes) : Option ArtifactEncoding :=
  match decodeProjection bytes with
  | some (value, []) => some value
  | _ => none

theorem validateOne_projectionBytes (value : ArtifactEncoding) :
    validateOne (projectionBytes value) = some value := by
  simp [validateOne, decodeProjection_projectionBytes]

/-- Successful exact-one validation means that the supplied host bytes were
already the canonical projection of the returned value.  Validation does not
decode and silently re-encode a different byte string. -/
theorem validateOne_some_exact {bytes : Bytes} {value : ArtifactEncoding}
    (accepted : validateOne bytes = some value) :
    bytes = projectionBytes value := by
  unfold validateOne at accepted
  cases decoded : decodeProjection bytes with
  | none => simp [decoded] at accepted
  | some result =>
      cases result with
      | mk decodedValue following =>
          cases following with
          | nil =>
              simp only [decoded, Option.some.injEq] at accepted
              subst decodedValue
              have exactBytes := Durable.encodeValue_append_of_decodeValue
                artifactCodec artifactFormat decoded
              simpa [projectionBytes] using exactBytes.symm
          | cons byte rest => simp [decoded] at accepted

/-- The boolean tested by the host validator accepts exactly canonical
artifact projections, with the semantic value existentially hidden from the
Rust side of the boundary. -/
theorem validateOne_isSome_iff_exists_projection (bytes : Bytes) :
    (validateOne bytes).isSome = true ↔
      ∃ value : ArtifactEncoding, bytes = projectionBytes value := by
  constructor
  · intro accepted
    cases decoded : validateOne bytes with
    | none => simp [decoded] at accepted
    | some value => exact ⟨value, validateOne_some_exact decoded⟩
  · rintro ⟨value, rfl⟩
    simp [validateOne_projectionBytes]

theorem validateOne_projectionBytes_append_cons_refused
    (value : ArtifactEncoding) (byte : UInt8) (trailing : Bytes) :
    validateOne (projectionBytes value ++ byte :: trailing) = none := by
  rw [validateOne]
  rw [decodeProjection_projectionBytes_append]

theorem length_projectionBytes (value : ArtifactEncoding) :
    (projectionBytes value).length = 5 + 2 * (artifactCodec.encode value).length := by
  simp [projectionBytes, Durable.encodeValue, Durable.encodeFrame,
    Durable.encodeEnvelope, Durable.encodePayload]
  induction artifactCodec.encode value with
  | nil => simp [Durable.encodeData]
  | cons byte rest ih =>
      simp only [Durable.encodeData, List.length_cons]
      omega

/-! ## §2. One-frame diagnostic parsing -/

/-- The first reason a suffix is not a complete canonical v2 artifact frame.
`fuelExhausted` is totalization only; `scan` supplies one more unit of fuel
than the byte length, and the canonical/torn/corrupt theorems below never
produce it. -/
inductive Fault where
  | badMagic0 (actual : UInt8)
  | badMagic1 (actual : UInt8)
  | wrongVersion (actual : UInt8)
  | wrongDomain (actual : UInt8)
  | unknownBodyTag (actual : UInt8)
  | noncanonicalPayload
  | impossibleAcceptedTerminator
  | fuelExhausted
  deriving DecidableEq

/-- Diagnostic result for a suffix already known not to decode as a frame. -/
inductive Refusal where
  | torn
  | corrupt (relativeOffset : Nat) (fault : Fault)
  deriving DecidableEq

/-- Diagnose a refused payload body.  EOF at a pair boundary or immediately
after a data tag is a torn append.  Every other body tag is corruption. -/
def diagnoseBody (offset : Nat) : Bytes → Refusal
  | [] => .torn
  | [tag] =>
      if tag = Durable.endTag then
        .corrupt offset .impossibleAcceptedTerminator
      else if tag = Durable.dataTag then
        .torn
      else
        .corrupt offset (.unknownBodyTag tag)
  | tag :: _byte :: rest =>
      if tag = Durable.endTag then
        .corrupt offset .impossibleAcceptedTerminator
      else if tag = Durable.dataTag then
        diagnoseBody (offset + 2) rest
      else
        .corrupt offset (.unknownBodyTag tag)

/-- Diagnose a suffix for which `Durable.decodeFor artifactFormat` refused.
Wrong tag bytes become corruption as soon as the respective field is present;
a matching but incomplete header is torn. -/
def diagnoseRefusal : Bytes → Refusal
  | [] => .torn
  | m0 :: after0 =>
      if m0 = Durable.magic₀ then
        match after0 with
        | [] => .torn
        | m1 :: after1 =>
            if m1 = Durable.magic₁ then
              match after1 with
              | [] => .torn
              | version :: afterVersion =>
                  if version = artifactFormat.version then
                    match afterVersion with
                    | [] => .torn
                    | domain :: body =>
                        if domain = artifactFormat.domain then
                          diagnoseBody 4 body
                        else
                          .corrupt 3 (.wrongDomain domain)
                  else
                    .corrupt 2 (.wrongVersion version)
            else
              .corrupt 1 (.badMagic1 m1)
      else
        .corrupt 0 (.badMagic0 m0)

/-- Result of inspecting the next record.  `consumed` is the length of the
accepted first frame, not the length of the complete input suffix. -/
inductive FrameInspection where
  | accepted (value : ArtifactEncoding) (following : Bytes) (consumed : Nat)
  | torn
  | corrupt (relativeOffset : Nat) (fault : Fault)
  deriving DecidableEq

/-- Inspect exactly the next frame.  Successful semantic decoding is delegated
to `decodeProjection`; syntactic diagnosis is used only after that decoder has
refused. -/
def inspectFrame (bytes : Bytes) : FrameInspection :=
  match decodeProjection bytes with
  | some (value, following) =>
      .accepted value following (bytes.length - following.length)
  | none =>
      match Durable.decodeFor artifactFormat bytes with
      | some (_, following) =>
          .corrupt (bytes.length - following.length - 1) .noncanonicalPayload
      | none =>
          match diagnoseRefusal bytes with
          | .torn => .torn
          | .corrupt offset fault => .corrupt offset fault

theorem inspectFrame_projectionBytes_append
    (value : ArtifactEncoding) (trailing : Bytes) :
    inspectFrame (projectionBytes value ++ trailing) =
      .accepted value trailing (projectionBytes value).length := by
  unfold inspectFrame
  rw [decodeProjection_projectionBytes_append]
  simp

/-! ## §3. Journal scan and exact record boundaries -/

/-- One accepted record and its exact half-open byte range. -/
structure Record where
  startOffset : Nat
  endOffset : Nat
  value : ArtifactEncoding
  deriving DecidableEq

/-- Why scanning stopped.  Corruption reports both the beginning of the
refused record and the first byte diagnosed within it. -/
inductive Stop where
  | cleanEOF
  | tornFinal (recordStart observedEnd : Nat)
  | corrupt (recordStart faultOffset : Nat) (fault : Fault)
  deriving DecidableEq

/-- A maximal completed prefix.  `completedPrefixLength` is the exact byte
offset after its last accepted frame (zero for an empty prefix). -/
structure ScanResult where
  records : List Record
  completedPrefixLength : Nat
  stop : Stop
  deriving DecidableEq

def cleanAt (offset : Nat) : ScanResult :=
  ⟨[], offset, .cleanEOF⟩

def tornAt (offset observed : Nat) : ScanResult :=
  ⟨[], offset, .tornFinal offset (offset + observed)⟩

def corruptAt (offset relative : Nat) (fault : Fault) : ScanResult :=
  ⟨[], offset, .corrupt offset (offset + relative) fault⟩

def prependRecord (record : Record) (tail : ScanResult) : ScanResult :=
  { tail with records := record :: tail.records }

/-- Fuel-totalized scanner.  Fuel counts attempted records, not bytes. -/
def scanFuel : Nat → Nat → Bytes → ScanResult
  | 0, offset, bytes =>
      if bytes = [] then cleanAt offset
      else corruptAt offset 0 .fuelExhausted
  | fuel + 1, offset, bytes =>
      match inspectFrame bytes with
      | .accepted value following consumed =>
          prependRecord ⟨offset, offset + consumed, value⟩
            (scanFuel fuel (offset + consumed) following)
      | .torn =>
          if bytes = [] then cleanAt offset
          else tornAt offset bytes.length
      | .corrupt relative fault => corruptAt offset relative fault

/-- Scan a journal.  `length + 1` gives even a one-byte corrupt/torn suffix a
diagnostic step after all completed records. -/
def scan (bytes : Bytes) : ScanResult :=
  scanFuel (bytes.length + 1) 0 bytes

/-- Canonical concatenation at the semantic artifact level. -/
def encodeJournal : List ArtifactEncoding → Bytes
  | [] => []
  | value :: rest => projectionBytes value ++ encodeJournal rest

/-- The artifact-level journal is definitionally the generic durable journal
of the canonical artifact payloads. -/
theorem encodeJournal_eq_durable (values : List ArtifactEncoding) :
    encodeJournal values =
      Durable.encodeJournal artifactFormat (values.map artifactCodec.encode) := by
  induction values with
  | nil => rfl
  | cons value rest ih =>
      simp [encodeJournal, Durable.encodeJournal, projectionBytes,
        Durable.encodeValue, ih]

/-- Pairwise evidence that a host-returned body list and a semantic value list
have the same shape and that each body passed exact one-frame validation. -/
inductive ValidatedBodies : List Bytes → List ArtifactEncoding → Prop where
  | nil : ValidatedBodies [] []
  | cons {body : Bytes} {value : ArtifactEncoding}
      {bodies : List Bytes} {values : List ArtifactEncoding}
      (head : validateOne body = some value)
      (tail : ValidatedBodies bodies values) :
      ValidatedBodies (body :: bodies) (value :: values)

/-- Per-body success bits, which are all the current host FFI reveals, suffice
to obtain a semantic value list related by `ValidatedBodies`. -/
theorem exists_validatedBodies_of_all_isSome (bodies : List Bytes)
    (accepted : bodies.all (fun body => (validateOne body).isSome) = true) :
    ∃ values : List ArtifactEncoding, ValidatedBodies bodies values := by
  induction bodies with
  | nil => exact ⟨[], .nil⟩
  | cons body rest ih =>
      simp only [List.all_cons, Bool.and_eq_true] at accepted
      obtain ⟨acceptedBody, acceptedRest⟩ := accepted
      cases decoded : validateOne body with
      | none => simp [decoded] at acceptedBody
      | some value =>
          obtain ⟨values, validatedRest⟩ := ih acceptedRest
          exact ⟨value :: values, .cons decoded validatedRest⟩

/-- Exact bodies accepted one by one concatenate to the canonical semantic
journal for the values returned by the Lean decoder. -/
theorem validatedBodies_flatten_eq_encodeJournal
    {bodies : List Bytes} {values : List ArtifactEncoding}
    (accepted : ValidatedBodies bodies values) :
    bodies.flatten = encodeJournal values := by
  induction accepted with
  | nil => rfl
  | cons acceptedBody acceptedRest ih =>
      rw [List.flatten_cons, validateOne_some_exact acceptedBody,
        encodeJournal, ih]

/-- A host list of complete bodies admitted by the existing Lean validator
satisfies the generic durable recovery law exactly.  This starts from the
bodies returned by a host scanner and makes no claim about how a filesystem or
power loss produced those bytes. -/
theorem recover_validatedBodies
    {bodies : List Bytes} {values : List ArtifactEncoding}
    (accepted : ValidatedBodies bodies values) :
    Durable.recover artifactFormat bodies.flatten =
      values.map artifactCodec.encode := by
  rw [validatedBodies_flatten_eq_encodeJournal accepted,
    encodeJournal_eq_durable, Durable.recover_encodeJournal]

/-- Existential recovery form matching the host's boolean-only validation
surface: all accepted complete bodies recover as some exact canonical artifact
payload list. -/
theorem exists_recovery_of_all_isSome (bodies : List Bytes)
    (accepted : bodies.all (fun body => (validateOne body).isSome) = true) :
    ∃ values : List ArtifactEncoding,
      Durable.recover artifactFormat bodies.flatten =
        values.map artifactCodec.encode := by
  obtain ⟨values, validated⟩ :=
    exists_validatedBodies_of_all_isSome bodies accepted
  exact ⟨values, recover_validatedBodies validated⟩

/-- Expected record boundaries for a canonical semantic journal. -/
def recordsAt : Nat → List ArtifactEncoding → List Record
  | _, [] => []
  | offset, value :: rest =>
      let next := offset + (projectionBytes value).length
      ⟨offset, next, value⟩ :: recordsAt next rest

def resultAt (offset : Nat) (values : List ArtifactEncoding) (stop : Stop) :
    ScanResult :=
  match values with
  | [] => ⟨[], offset, stop⟩
  | value :: rest =>
      let next := offset + (projectionBytes value).length
      prependRecord ⟨offset, next, value⟩ (resultAt next rest stop)

@[simp] theorem resultAt_records (offset : Nat)
    (values : List ArtifactEncoding) (stop : Stop) :
    (resultAt offset values stop).records = recordsAt offset values := by
  induction values generalizing offset with
  | nil => rfl
  | cons value rest ih =>
      simp [resultAt, recordsAt, prependRecord, ih]

def endOffset : Nat → List ArtifactEncoding → Nat
  | offset, [] => offset
  | offset, value :: rest =>
      endOffset (offset + (projectionBytes value).length) rest

theorem endOffset_eq (offset : Nat) (values : List ArtifactEncoding) :
    endOffset offset values = offset + (encodeJournal values).length := by
  induction values generalizing offset with
  | nil => simp [endOffset, encodeJournal]
  | cons value rest ih =>
      simp only [endOffset, encodeJournal, List.length_append]
      rw [ih]
      omega

theorem recordsAt_values (offset : Nat) (values : List ArtifactEncoding) :
    (recordsAt offset values).map Record.value = values := by
  induction values generalizing offset with
  | nil => rfl
  | cons value rest ih =>
      simp [recordsAt, ih]

@[simp] theorem resultAt_completedPrefixLength (offset : Nat)
    (values : List ArtifactEncoding) (stop : Stop) :
    (resultAt offset values stop).completedPrefixLength = endOffset offset values := by
  induction values generalizing offset with
  | nil => rfl
  | cons value rest ih =>
      simp [resultAt, prependRecord, endOffset, ih]

theorem scanFuel_encodeJournal (values : List ArtifactEncoding) :
    ∀ fuel offset, values.length ≤ fuel →
      scanFuel fuel offset (encodeJournal values) =
        resultAt offset values (.cleanEOF) := by
  induction values with
  | nil =>
      intro fuel offset enough
      cases fuel <;> simp [scanFuel, encodeJournal, inspectFrame,
        decodeProjection, Durable.decodeValue, Durable.decodeFor,
        Durable.decodeEnvelope, diagnoseRefusal, cleanAt, resultAt]
  | cons value rest ih =>
      intro fuel offset enough
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          simp only [List.length_cons, Nat.succ_le_succ_iff] at enough
          rw [encodeJournal]
          rw [scanFuel]
          rw [inspectFrame_projectionBytes_append]
          simp only [resultAt, prependRecord]
          rw [ih fuel (offset + (projectionBytes value).length) enough]

theorem length_le_encodeJournal (values : List ArtifactEncoding) :
    values.length ≤ (encodeJournal values).length := by
  induction values with
  | nil => simp [encodeJournal]
  | cons value rest ih =>
      simp only [List.length_cons, encodeJournal, List.length_append]
      have framePositive : 1 ≤ (projectionBytes value).length := by
        simp [projectionBytes, Durable.encodeValue, Durable.encodeFrame,
          Durable.encodeEnvelope]
      calc
        rest.length + 1 ≤ (encodeJournal rest).length + 1 :=
          Nat.add_le_add_right ih 1
        _ ≤ (encodeJournal rest).length + (projectionBytes value).length :=
          Nat.add_le_add_left framePositive (encodeJournal rest).length
        _ = (projectionBytes value).length + (encodeJournal rest).length :=
          Nat.add_comm _ _

/-- Reopening a complete canonical journal recovers every exact artifact and
every exact boundary, and stops at clean EOF. -/
theorem scan_encodeJournal (values : List ArtifactEncoding) :
    scan (encodeJournal values) = resultAt 0 values (.cleanEOF) := by
  unfold scan
  apply scanFuel_encodeJournal
  exact Nat.le_trans (length_le_encodeJournal values)
    (Nat.le_add_right _ 1)

theorem scan_encodeJournal_records (values : List ArtifactEncoding) :
    (scan (encodeJournal values)).records = recordsAt 0 values := by
  rw [scan_encodeJournal]
  exact resultAt_records 0 values .cleanEOF

theorem scan_encodeJournal_values (values : List ArtifactEncoding) :
    (scan (encodeJournal values)).records.map Record.value = values := by
  rw [scan_encodeJournal_records, recordsAt_values]

theorem scan_encodeJournal_completedPrefixLength
    (values : List ArtifactEncoding) :
    (scan (encodeJournal values)).completedPrefixLength =
      (encodeJournal values).length := by
  rw [scan_encodeJournal, resultAt_completedPrefixLength, endOffset_eq]
  simp

/-- Byte append agrees exactly with semantic snoc. -/
theorem encodeJournal_append (left right : List ArtifactEncoding) :
    encodeJournal (left ++ right) = encodeJournal left ++ encodeJournal right := by
  induction left with
  | nil => simp [encodeJournal]
  | cons value rest ih => simp [encodeJournal, ih, List.append_assoc]

theorem append_projectionBytes (values : List ArtifactEncoding)
    (value : ArtifactEncoding) :
    encodeJournal values ++ projectionBytes value =
      encodeJournal (values ++ [value]) := by
  simp [encodeJournal_append, encodeJournal]

/-- Exact append/reopen law at the API surface. -/
theorem scan_append (values : List ArtifactEncoding)
    (value : ArtifactEncoding) :
    scan (encodeJournal values ++ projectionBytes value) =
      resultAt 0 (values ++ [value]) (.cleanEOF) := by
  rw [append_projectionBytes, scan_encodeJournal]

/-! ## §4. First-refusal policy -/

def stopFor (offset : Nat) (suffix : Bytes) : FrameInspection → Stop
  | .accepted _ _ _ => .corrupt offset offset .fuelExhausted
  | .torn => .tornFinal offset (offset + suffix.length)
  | .corrupt relative fault => .corrupt offset (offset + relative) fault

theorem scanFuel_encodeJournal_append_refused
    (values : List ArtifactEncoding) (suffix : Bytes)
    (nonempty : suffix ≠ [])
    (refused : match inspectFrame suffix with
      | .accepted _ _ _ => False
      | _ => True) :
    ∀ fuel offset, values.length + 1 ≤ fuel →
      scanFuel fuel offset (encodeJournal values ++ suffix) =
        resultAt offset values (stopFor (endOffset offset values) suffix
          (inspectFrame suffix)) := by
  induction values with
  | nil =>
      intro fuel offset enough
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          simp only [encodeJournal, List.nil_append]
          cases inspected : inspectFrame suffix with
          | accepted value following consumed =>
              simp [inspected] at refused
          | torn =>
              cases suffix with
              | nil =>
                  contradiction
              | cons byte rest =>
                  simp [scanFuel, inspected, resultAt, stopFor, endOffset,
                    tornAt]
          | corrupt relative fault =>
              cases suffix with
              | nil =>
                  contradiction
              | cons byte rest =>
                  simp [scanFuel, inspected, resultAt, stopFor, endOffset,
                    corruptAt]
  | cons value rest ih =>
      intro fuel offset enough
      cases fuel with
      | zero => simp at enough
      | succ fuel =>
          simp only [List.length_cons, Nat.succ_add, Nat.succ_le_succ_iff] at enough
          rw [encodeJournal, List.append_assoc, scanFuel]
          rw [inspectFrame_projectionBytes_append]
          simp only [resultAt, prependRecord, endOffset]
          rw [ih fuel
            (offset + (projectionBytes value).length) enough]

/-- A refused suffix after canonical records cannot make scanning skip ahead to
later bytes.  The completed prefix and its boundaries are exactly the records
before that suffix. -/
theorem scan_stops_at_first_refusal
    (values : List ArtifactEncoding) (suffix : Bytes)
    (nonempty : suffix ≠ [])
    (refused : match inspectFrame suffix with
      | .accepted _ _ _ => False
      | _ => True) :
    scan (encodeJournal values ++ suffix) =
      resultAt 0 values
        (stopFor (endOffset 0 values) suffix (inspectFrame suffix)) := by
  apply scanFuel_encodeJournal_append_refused values suffix nonempty refused
  have recordsBound : values.length ≤ (encodeJournal values).length :=
    length_le_encodeJournal values
  have suffixPositive : 1 ≤ suffix.length :=
    Nat.one_le_iff_ne_zero.mpr (by simpa using nonempty)
  simp only [List.length_append]
  omega

/-- Recover the byte-exact completed prefix named by `scan`; the complementary
suffix begins at the first torn/corrupt record. -/
def completedPrefix (bytes : Bytes) : Bytes :=
  bytes.take (scan bytes).completedPrefixLength

def refusedSuffix (bytes : Bytes) : Bytes :=
  bytes.drop (scan bytes).completedPrefixLength

theorem scan_stops_at_first_refusal_completedPrefixLength
    (values : List ArtifactEncoding) (suffix : Bytes)
    (nonempty : suffix ≠ [])
    (refused : match inspectFrame suffix with
      | .accepted _ _ _ => False
      | _ => True) :
    (scan (encodeJournal values ++ suffix)).completedPrefixLength =
      (encodeJournal values).length := by
  rw [scan_stops_at_first_refusal values suffix nonempty refused,
    resultAt_completedPrefixLength, endOffset_eq]
  simp

/-! ## §5. Torn frames and concrete cross-language fixtures -/

theorem diagnoseBody_encodeData (done : Bytes) (offset : Nat) :
    diagnoseBody offset (Durable.encodeData done) = .torn := by
  induction done generalizing offset with
  | nil => rfl
  | cons byte rest ih =>
      simp [Durable.encodeData, diagnoseBody, Durable.dataTag,
        Durable.endTag, ih]

theorem diagnoseBody_encodeData_afterTag
    (done : Bytes) (offset : Nat) :
    diagnoseBody offset (Durable.encodeData done ++ [Durable.dataTag]) = .torn := by
  induction done generalizing offset with
  | nil => rfl
  | cons byte rest ih =>
      simp only [Durable.encodeData, List.cons_append]
      change diagnoseBody offset
        (Durable.dataTag :: byte ::
          (Durable.encodeData rest ++ [Durable.dataTag])) = .torn
      simp only [diagnoseBody, Durable.dataTag, Durable.endTag,
        ↓reduceIte]
      exact ih (offset + 2)

theorem diagnoseRefusal_tornFrame {payload torn : Bytes}
    (h : Durable.TornFrame artifactFormat payload torn) :
    diagnoseRefusal torn = .torn := by
  cases h with
  | empty => rfl
  | afterMagic₀ => simp [diagnoseRefusal]
  | afterMagic₁ => simp [diagnoseRefusal]
  | afterVersion => simp [diagnoseRefusal]
  | atDataBoundary done pending split =>
      simp [diagnoseRefusal, diagnoseBody_encodeData]
  | afterDataTag done pending next split =>
      simp [diagnoseRefusal, diagnoseBody_encodeData_afterTag]

theorem inspectFrame_tornFrame {payload torn : Bytes}
    (h : Durable.TornFrame artifactFormat payload torn) :
    inspectFrame torn = .torn := by
  unfold inspectFrame
  rw [Durable.decodeFor_tornFrame h]
  have decodedValue : decodeProjection torn = none := by
    unfold decodeProjection Durable.decodeValue
    rw [Durable.decodeFor_tornFrame h]
    rfl
  rw [decodedValue]
  rw [diagnoseRefusal_tornFrame h]

/-- An explicit torn final append recovers the exact canonical prefix and is
reported as torn, never clean or corrupt. -/
theorem scan_torn_final (values : List ArtifactEncoding)
    {nextPayload torn : Bytes}
    (h : Durable.TornFrame artifactFormat nextPayload torn)
    (nonempty : torn ≠ []) :
    scan (encodeJournal values ++ torn) =
      resultAt 0 values
        (.tornFinal (endOffset 0 values)
          (endOffset 0 values + torn.length)) := by
  have inspected : inspectFrame torn = .torn := inspectFrame_tornFrame h
  have stopped := scan_stops_at_first_refusal values torn nonempty (by
    rw [inspected]
    trivial)
  rw [stopped, inspected]
  rfl

namespace Fixtures

/-- Small canonical artifacts keep the shared fixture byte arrays compact. -/
def first : ArtifactEncoding :=
  ⟨⟨1, 2, 1⟩, [], [], [], [], [], []⟩

def second : ArtifactEncoding :=
  ⟨⟨2, 2, 1⟩, [], [], [], [], [], []⟩

def third : ArtifactEncoding :=
  ⟨⟨3, 2, 1⟩, [], [], [], [], [], []⟩

def cleanTwo : Bytes := encodeJournal [first, second]

/-- Every byte prefix before the terminator of the third complete frame.  A
host implementation can consume this list directly as the torn-tail fixture
matrix instead of hand-selecting a few cut points. -/
def thirdStrictTruncations : List Bytes :=
  (List.range (projectionBytes third).length).map
    (fun length => (projectionBytes third).take length)

theorem thirdStrictTruncations_count :
    thirdStrictTruncations.length = (projectionBytes third).length := by
  simp [thirdStrictTruncations]

set_option maxRecDepth 4000 in
/-- The complete truncation matrix exercises every possible stopped write of
the third canonical frame, not merely one representative header cut. -/
theorem every_third_strict_truncation_is_torn :
    thirdStrictTruncations.all
      (fun bytes => decide (inspectFrame bytes = .torn)) = true := by
  decide

/-- Header-only strict prefix of the third record. -/
def tornThird : Bytes :=
  [Durable.magic₀, Durable.magic₁, artifactFormat.version]

def twoThenTorn : Bytes := cleanTwo ++ tornThird

def wrongMagic : Bytes := [0]
def wrongVersion : Bytes :=
  [Durable.magic₀, Durable.magic₁, 1, artifactFormat.domain, Durable.endTag]
def wrongDomain : Bytes :=
  [Durable.magic₀, Durable.magic₁, artifactFormat.version, 162, Durable.endTag]
def unknownBodyTag : Bytes :=
  frameHeader ++ [7]

def noncanonicalPayload : Bytes :=
  Durable.encodeFrame artifactFormat [2]

def corruptMiddle : Bytes :=
  projectionBytes first ++ unknownBodyTag ++ projectionBytes second

def wrongVersionMiddle : Bytes :=
  projectionBytes first ++ wrongVersion ++ projectionBytes second

theorem clean_fixture :
    scan cleanTwo = resultAt 0 [first, second] .cleanEOF := by
  exact scan_encodeJournal [first, second]

theorem torn_fixture :
    scan twoThenTorn = resultAt 0 [first, second]
      (.tornFinal (endOffset 0 [first, second])
        (endOffset 0 [first, second] + tornThird.length)) := by
  apply scan_torn_final [first, second]
    (nextPayload := artifactCodec.encode third)
  · exact Durable.TornFrame.afterVersion
  · decide

theorem wrong_magic_fixture :
    inspectFrame wrongMagic = .corrupt 0 (.badMagic0 0) := by decide

theorem wrong_version_fixture :
    inspectFrame wrongVersion = .corrupt 2 (.wrongVersion 1) := by decide

theorem wrong_domain_fixture :
    inspectFrame wrongDomain = .corrupt 3 (.wrongDomain 162) := by decide

theorem unknown_body_tag_fixture :
    inspectFrame unknownBodyTag = .corrupt 4 (.unknownBodyTag 7) := by decide

theorem noncanonical_payload_fixture :
    inspectFrame noncanonicalPayload = .corrupt 6 .noncanonicalPayload := by decide

theorem corrupt_middle_fixture :
    scan corruptMiddle = resultAt 0 [first]
      (.corrupt (endOffset 0 [first]) (endOffset 0 [first] + 4)
        (.unknownBodyTag 7)) := by
  unfold corruptMiddle
  apply scan_stops_at_first_refusal [first]
    (unknownBodyTag ++ projectionBytes second)
  · decide
  · change True
    trivial

theorem wrong_version_middle_fixture :
    scan wrongVersionMiddle = resultAt 0 [first]
      (.corrupt (endOffset 0 [first]) (endOffset 0 [first] + 2)
        (.wrongVersion 1)) := by
  unfold wrongVersionMiddle
  apply scan_stops_at_first_refusal [first]
    (wrongVersion ++ projectionBytes second)
  · decide
  · change True
    trivial

end Fixtures

/-! ## §6. Narrow host adapter -/

/-- Convert the host-owned `ByteArray` into the logical byte list without
changing byte order. -/
def ofByteArray (input : ByteArray) : Bytes := input.data.toList

/-- One output byte: `1` iff the input is exactly one canonical v2 artifact
frame, `0` otherwise.  This lets a pure-Rust storage layer validate a complete
frame without implementing a second artifact decoder.  It exposes no artifact
constructor and performs no filesystem operation. -/
def validateOneKernelBytes (input : ByteArray) : ByteArray :=
  ByteArray.empty.push
    (if (validateOne (ofByteArray input)).isSome then 1 else 0)

/-- The exact success byte returned across the current FFI boundary is
equivalent to existence of a semantic artifact whose canonical projection is
the unchanged input byte list. -/
theorem validateOneKernelBytes_accepts_iff (input : ByteArray) :
    validateOneKernelBytes input = ByteArray.empty.push 1 ↔
      ∃ value : ArtifactEncoding,
        ofByteArray input = projectionBytes value := by
  cases accepted : (validateOne (ofByteArray input)).isSome with
  | false =>
      have noValue : ¬ ∃ value : ArtifactEncoding,
          ofByteArray input = projectionBytes value := by
        intro existsValue
        have := (validateOne_isSome_iff_exists_projection
          (ofByteArray input)).mpr existsValue
        simp [accepted] at this
      simp only [validateOneKernelBytes, accepted, Bool.false_eq_true,
        ↓reduceIte, noValue, iff_false]
      decide
  | true =>
      have existsValue := (validateOne_isSome_iff_exists_projection
        (ofByteArray input)).mp accepted
      simp [validateOneKernelBytes, accepted, existsValue]

@[export uwueave_preo_artifact_v2_validate_one]
def validateOneKernel (input : ByteArray) : ByteArray :=
  validateOneKernelBytes input

/-! ## §7. Physical integrity is a separate parameterized layer -/

/-- A host may place an unchanged logical frame in a physical record carrying
sequence, length, and digest fields.  The checksum type and function are
parameters: this structure does not pretend that Lean's logic implements or
verifies BLAKE3, stable-media writes, or any filesystem protocol. -/
structure PhysicalRecord (Digest : Type) where
  formatVersion : Nat
  domain : Nat
  sequence : Nat
  declaredLength : Nat
  frame : Bytes
  checksum : Digest
/-- The exact semantic obligations for accepting a physical record.  The host
chooses the outer version/domain and checksum function, but the inner frame
must still pass the one canonical ArtifactDurable-v2 decoder. -/
def PhysicalRecord.Valid {Digest : Type}
    (expectedVersion expectedDomain : Nat)
    (digest : Nat → Nat → Nat → Bytes → Digest)
    [DecidableEq Digest] (record : PhysicalRecord Digest) : Prop :=
  record.formatVersion = expectedVersion
  ∧ record.domain = expectedDomain
  ∧ record.declaredLength = record.frame.length
  ∧ (validateOne record.frame).isSome
  ∧ digest record.formatVersion record.domain record.sequence record.frame =
      record.checksum

end Uwueave.Preo.ArtifactJournalKernel
