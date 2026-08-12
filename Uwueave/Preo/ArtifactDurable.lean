/-
# Uwueave.Preo.ArtifactDurable — public durable artifact surface

The canonical codec and framed-byte contract live in the data-only
ArtifactDurableCore leaf. This umbrella adds the checked nonempty examples and
preserves every original public declaration name for existing importers.
-/
import Uwueave.Preo.ArtifactDurableCore
import Uwueave.Preo.Artifact

namespace Uwueave.Preo.ArtifactDurable

open Uwueave
open Uwueave.Preo.Artifact

set_option autoImplicit false

/-! ## §6. Falsifiable, nonempty acceptance examples -/

namespace Examples

def fullArtifact : Artifact := Uwueave.Preo.Artifact.Examples.bundle

def fullEncoding : ArtifactEncoding := fullArtifact.canonicalEncoding

/-- The acceptance value exercises every top-level artifact list. -/
theorem fullArtifact_is_nonempty :
    fullArtifact.fields.length = 1
    ∧ fullArtifact.invariants.length = 2
    ∧ fullArtifact.futures.length = 1
    ∧ fullArtifact.sessions.length = 1
    ∧ fullArtifact.plans.length = 1
    ∧ fullArtifact.budgets.length = 1 := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The migrated product codec retains both exact five-currency vectors and
following bytes; the budget IDs are not reconstructed from list position. -/
def fullBudget : BudgetArtifactEncoding :=
  Uwueave.Preo.Artifact.Examples.budget.toArtifact.canonicalEncoding

set_option maxRecDepth 2000 in
theorem budget_wire_roundtrip_with_trailing :
    budgetWire.parse (budgetWire.encode fullBudget ++ [99]) =
      some (fullBudget, [99]) :=
  budgetWire.parse_encode_append fullBudget [99]

/-- The full nonempty artifact projection round-trips without consuming bytes
belonging to the next journal entry. -/
theorem fullArtifact_roundtrip_with_trailing :
    decodeProjection (projectionBytes fullEncoding ++ [91, 92, 93]) =
      some (fullEncoding, [91, 92, 93]) :=
  decodeProjection_projectionBytes_append fullEncoding [91, 92, 93]

/-- Every currency constructor has an explicit and distinct tag. -/
theorem every_currency_branch :
    currencyWire.parse (currencyWire.encode .peerBarrier ++ [99]) =
        some (.peerBarrier, [99])
    ∧ currencyWire.parse (currencyWire.encode .arbiterCut ++ [99]) =
        some (.arbiterCut, [99])
    ∧ currencyWire.parse (currencyWire.encode .networkRound ++ [99]) =
        some (.networkRound, [99])
    ∧ currencyWire.parse (currencyWire.encode .userPrompt ++ [99]) =
        some (.userPrompt, [99])
    ∧ currencyWire.parse (currencyWire.encode .rollback ++ [99]) =
        some (.rollback, [99]) := by
  decide

/-- Both branches of every option/sum-shaped artifact field are exercised. -/
theorem every_sum_and_option_branch :
    evidenceKeyWire.parse (evidenceKeyWire.encode .none ++ [99]) =
        some (.none, [99])
    ∧ evidenceKeyWire.parse (evidenceKeyWire.encode (.named 7) ++ [99]) =
        some (.named 7, [99])
    ∧ originWire.parse (originWire.encode .ambient ++ [99]) =
        some (.ambient, [99])
    ∧ originWire.parse (originWire.encode (.crossing 3) ++ [99]) =
        some (.crossing 3, [99])
    ∧ verdictWire.parse (verdictWire.encode .free ++ [99]) =
        some (.free, [99])
    ∧ verdictWire.parse
        (verdictWire.encode (.clash [1, 2] [3]) ++ [99]) =
        some (.clash [1, 2] [3], [99])
    ∧ natWire.option.parse (natWire.option.encode none ++ [99]) =
        some (none, [99])
    ∧ natWire.option.parse (natWire.option.encode (some 8) ++ [99]) =
        some (some 8, [99]) := by
  decide

/-- Length-delimited lists and concatenated products preserve trailing bytes. -/
theorem list_and_product_coverage :
    (natWire.prod natWire.list).parse
        ((natWire.prod natWire.list).encode (7, [2, 4, 6]) ++ [99]) =
      some ((7, [2, 4, 6]), [99]) :=
  (natWire.prod natWire.list).parse_encode_append (7, [2, 4, 6]) [99]

/-- Exact natural decoding rejects the concrete overlong zero and an unknown
constructor byte. -/
theorem noncanonical_naturals_are_refused :
    natCodec.decode [0, 0] = none ∧ natCodec.decode [2, 0] = none :=
  ⟨nat_overlong_zero_refused, nat_unknown_tag_refused⟩

/-- Exact artifact decoding refuses a canonical artifact followed by surplus
payload bytes. The prefix parser exposes those bytes; the canonical codec does
not silently absorb them. -/
theorem overlong_artifact_refused :
    artifactCodec.decode (artifactCodec.encode fullEncoding ++ [0]) = none := by
  exact canonicalCodecOfWire_append_cons_refused artifactWire fullEncoding 0 []

def secondEncoding : ArtifactEncoding :=
  { fullEncoding with
    declaration := { fullEncoding.declaration with schemaVersion := 2 } }

def thirdEncoding : ArtifactEncoding :=
  { fullEncoding with
    declaration := { fullEncoding.declaration with schemaVersion := 3 } }

def firstPayload : Bytes := artifactCodec.encode fullEncoding
def secondPayload : Bytes := artifactCodec.encode secondEncoding
def thirdPayload : Bytes := artifactCodec.encode thirdEncoding

/-- The third append stopped after magic and version, before domain or payload. -/
def tornThird : Bytes :=
  [Durable.magic₀, Durable.magic₁, artifactFormat.version]

theorem tornThird_is_torn :
    Durable.TornFrame artifactFormat thirdPayload tornThird :=
  Durable.TornFrame.afterVersion

def crashImage : Bytes :=
  Durable.encodeJournal artifactFormat [firstPayload, secondPayload] ++ tornThird

/-- Two complete frames followed by a torn third recover exactly the first two,
and their payloads decode to the exact two artifact encodings. This remains a
logical crash-prefix theorem; it assumes the supplied `TornFrame` witness. -/
theorem two_frames_then_torn_third :
    Durable.recover artifactFormat crashImage = [firstPayload, secondPayload]
    ∧ (Durable.recover artifactFormat crashImage).map artifactCodec.decode =
        [some fullEncoding, some secondEncoding] := by
  have recovered :
      Durable.recover artifactFormat crashImage = [firstPayload, secondPayload] := by
    unfold crashImage
    exact Durable.recover_crashPrefix artifactFormat
      [firstPayload, secondPayload] tornThird_is_torn
  refine ⟨recovered, ?_⟩
  rw [recovered]
  simp [firstPayload, secondPayload, artifactCodec.decode_encode]

/-- Wrong version and wrong domain are independently falsifiable on the full
nonempty example. -/
theorem wrong_projection_tags_are_refused :
    Durable.decodeValue artifactCodec wrongVersion
        (projectionBytes fullEncoding) = none
    ∧ Durable.decodeValue artifactCodec wrongDomain
        (projectionBytes fullEncoding) = none := by
  constructor
  · simpa using wrong_version_refused fullEncoding []
  · simpa using wrong_domain_refused fullEncoding []

end Examples

end Uwueave.Preo.ArtifactDurable
