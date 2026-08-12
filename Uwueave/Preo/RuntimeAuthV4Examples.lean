/-
# Uwueave.Preo.RuntimeAuthV4Examples — checked and byte-exact fixture

This opt-in leaf constructs one sidecar from the existing RuntimeAuthV4
fixture request, an exact ready-for-execution premise, and an active root grant.
It supplies stable bytes for host interoperability without entering any
runtime import closure.
-/
import Uwueave.Preo.RuntimeAuthV4Checked
import Uwueave.Preo.RuntimeAuthV4Durable
import Uwueave.Preo.RuntimeAuthV4Projection

namespace Uwueave.Preo.RuntimeAuthV4Examples

open Uwueave
open Uwueave.Preo.RuntimeAuthV4
open Uwueave.Preo.RuntimeAuthV4Projection

set_option autoImplicit false

def boundary : Uwueave.RuntimeAuthV4.VerificationBoundary where
  Accepts := fun _ _ _ => True

def resolver : Uwueave.RuntimeAuthV4.ResolverBoundary where
  Resolve := fun _ _ stable =>
    if stable = Uwueave.RuntimeAuthV4.fixtureNodeA.stable then
      some Uwueave.RuntimeAuthV4.fixtureNodeA.kernelIndex
    else if stable = Uwueave.RuntimeAuthV4.fixtureNodeB.stable then
      some Uwueave.RuntimeAuthV4.fixtureNodeB.kernelIndex
    else none

def acceptsAll : Uwueave.RuntimeAuthV4.SignedRequest → Prop := fun _ => True

def ready : Uwueave.RuntimeAuthV4.ReadyForExecution boundary resolver
    acceptsAll acceptsAll [] Uwueave.RuntimeAuthV4.fixtureRequest where
  verified := ⟨trivial⟩
  resolved := by
    constructor <;> decide
  fresh := by simp [Uwueave.RuntimeAuthV4.NonceFresh]
  authorized := trivial
  isMember := trivial

def grantState : Gated.GatedState :=
  (fun grant => grant == ((7 : Nat), (0 : Nat), (4 : Nat)),
    (fun _ => false, fun _ => false))

def grant : GrantReceipt Uwueave.RuntimeAuthV4.fixtureRequest where
  state := grantState
  grant := (7, 0, 4)
  active := .root (by decide) rfl
  parent_lt_id := by decide
  cite_exact := rfl
  child_covered := by decide

def context : ContextReceipt Uwueave.RuntimeAuthV4.fixtureRequest where
  substrateDigest := [31, 32]
  historyHeadDigest := [41, 42]
  originId := [51]
  versionId := [61]
  roster := [17]
  participants := [17]
  substrate_nonempty := by decide
  history_head_nonempty := by decide
  origin_nonempty := by decide
  version_nonempty := by decide
  roster_canonical := by decide
  participants_canonical := by decide
  issuer_mem := by decide
  participants_mem := by decide

def checked : CheckedManifest (boundary := boundary) (resolver := resolver)
    (authority := acceptsAll) (membership := acceptsAll) (seen := [])
    Uwueave.RuntimeAuthV4.fixtureRequest :=
  CheckedManifest.ofReady Uwueave.RuntimeAuthV4.fixtureRequest ready
    rfl grant context

def manifest : Manifest := checked.toManifest

theorem manifest_preserves_exact_request :
    manifest.move = SignedMoveRow.ofRequest Uwueave.RuntimeAuthV4.fixtureRequest := rfl

theorem source_signing_bytes_are_exact :
    checked.sourceSigningBytes =
      Uwueave.RuntimeAuthV4.signingBytesV4
        Uwueave.RuntimeAuthV4.fixtureRequest.content := rfl

def config : ValidationConfig where
  bounds :=
    { maxIdBytes := 8
      maxSignatureBytes := 8
      maxDigestBytes := 8
      maxRoster := 4
      maxParticipants := 4
      maxNatural := 100 }

def projection : Projection := Projection.ofManifest manifest

theorem validates : (validate config projection).isOk = true := by decide

def validated : ValidatedProjection :=
  (validate config projection).toOption.get (by decide)

def fixtureBytes : Durable.Bytes :=
  RuntimeAuthV4Durable.manifestBytes manifest

theorem fixture_bytes_decode_exact :
    RuntimeAuthV4Durable.decodeManifestExact fixtureBytes = some manifest :=
  RuntimeAuthV4Durable.decodeManifestExact_manifestBytes manifest

theorem changed_version_refused :
    Durable.decodeValue RuntimeAuthV4Durable.manifestCodec ⟨5, 162⟩ fixtureBytes =
      none :=
  by
    simpa only [fixtureBytes, List.append_nil] using
      RuntimeAuthV4Durable.changed_format_refused ⟨5, 162⟩
        (by decide) manifest []

theorem changed_domain_refused :
    Durable.decodeValue RuntimeAuthV4Durable.manifestCodec ⟨4, 163⟩ fixtureBytes =
      none :=
  by
    simpa only [fixtureBytes, List.append_nil] using
      RuntimeAuthV4Durable.changed_format_refused ⟨4, 163⟩
        (by decide) manifest []

def fixtureRust : String := renderRustSource validated

/-! Small exact refusals pin the principal hostile input classes. -/

private def validationError? {alpha : Type} :
    Except ValidationError alpha → Option ValidationError
  | .ok _ => none
  | .error error => some error

def wrongSchema : Projection := { projection with schema := "wrong/v4" }

theorem wrong_schema_refused :
    validationError? (validate config wrongSchema) =
      some (.wrongSchema RuntimeAuthV4Projection.schema "wrong/v4") := by decide

def wrongGrant : Projection :=
  { projection with manifest.context.citedGrant.id := 8 }

theorem wrong_grant_refused :
    validationError? (validate config wrongGrant) =
      some (.citeGrantMismatch 7 8) := by decide

def nonCanonicalRoster : Projection :=
  { projection with manifest.context.roster := [17, 17] }

theorem noncanonical_roster_refused :
    validationError? (validate config nonCanonicalRoster) =
      some (.nonCanonicalOrder .roster 17 17) := by decide

def outsiderParticipant : Projection :=
  { projection with manifest.context.participants := [18] }

theorem outsider_participant_refused :
    validationError? (validate config outsiderParticipant) =
      some (.participantNotInRoster 18) := by decide

def emptyNonce : Projection :=
  { projection with manifest.move.nonce := [] }

theorem empty_nonce_refused :
    validationError? (validate config emptyNonce) =
      some (.emptyBytes .nonce) := by decide

def emptySignature : Projection :=
  { projection with manifest.move.signature := [] }

theorem empty_signature_refused :
    validationError? (validate config emptySignature) =
      some (.emptyBytes .signature) := by decide

def emptyOrigin : Projection :=
  { projection with manifest.context.originId := [] }

theorem empty_origin_refused :
    validationError? (validate config emptyOrigin) =
      some (.emptyBytes .origin) := by decide

def emptyVersion : Projection :=
  { projection with manifest.context.versionId := [] }

theorem empty_version_refused :
    validationError? (validate config emptyVersion) =
      some (.emptyBytes .version) := by decide

def wrongAlgorithm : Projection :=
  { projection with manifest.move.signatureAlgorithm := 256 }

theorem wrong_algorithm_refused :
    validationError? (validate config wrongAlgorithm) =
      some (.algorithmOutOfRange 256) := by decide

def wrongIssuer : Projection :=
  { projection with manifest.move.issuer := UInt64.size }

theorem wrong_issuer_width_refused :
    validationError? (validate config wrongIssuer) =
      some (.uint64OutOfRange .issuer UInt64.size) := by decide

def outsideScope : Projection :=
  { projection with manifest.move.child.kernelIndex := 4 }

theorem outside_scope_refused :
    validationError? (validate config outsideScope) =
      some (.childOutsideGrantScope 4 4) := by decide

def malformedGrant : Projection :=
  { projection with manifest.context.citedGrant.parent := 7 }

theorem malformed_grant_refused :
    validationError? (validate config malformedGrant) =
      some (.nonCanonicalGrant 7 7) := by decide

def collidingDestination : NodeRow :=
  { stable := Uwueave.RuntimeAuthV4.fixtureNodeA.stable, kernelIndex := 4 }

def inconsistentNode : Projection :=
  { projection with manifest.move.destination := some collidingDestination }

theorem inconsistent_node_refused :
    validationError? (validate config inconsistentNode) =
      some (.inconsistentNodeIndex Uwueave.RuntimeAuthV4.fixtureNodeA.stable 3 4) :=
  by decide

def missingIssuer : Projection :=
  { projection with manifest.context.roster := [18] }

theorem missing_issuer_refused :
    validationError? (validate config missingIssuer) =
      some (.issuerNotInRoster 17) := by decide

end Uwueave.Preo.RuntimeAuthV4Examples
