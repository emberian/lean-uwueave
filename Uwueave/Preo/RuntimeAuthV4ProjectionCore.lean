/-
# Uwueave.Preo.RuntimeAuthV4ProjectionCore — bounded sidecar validation

This data-only validator checks the host projection schema, every byte/list/
numeric resource bound, required nonempty identities, exact cited-grant
reference, canonical roster/participant manifests, and membership relations.
It does not verify signatures, grants, digests, history, or membership proofs.
Only `RuntimeAuthV4Checked` projects those facts one-way from checked inputs.
-/
import Uwueave.Preo.RuntimeAuthV4Data

namespace Uwueave.Preo.RuntimeAuthV4Projection

open Uwueave.Preo.RuntimeAuthV4

set_option autoImplicit false

def schema : String := Uwueave.Preo.RuntimeAuthV4.schema

structure Projection where
  schema : String
  manifest : Manifest
  deriving DecidableEq

def Projection.ofManifest (manifest : Manifest) : Projection :=
  ⟨Uwueave.Preo.RuntimeAuthV4Projection.schema, manifest⟩

structure ValidationBounds where
  maxIdBytes : Nat
  maxSignatureBytes : Nat
  maxDigestBytes : Nat
  maxRoster : Nat
  maxParticipants : Nat
  maxNatural : Nat
  deriving DecidableEq

structure ValidationConfig where
  bounds : ValidationBounds
  deriving DecidableEq

inductive ByteField where
  | document
  | genesis
  | nonce
  | operation
  | child
  | destination
  | signature
  | substrateDigest
  | historyHeadDigest
  | origin
  | version
  deriving DecidableEq

inductive NaturalField where
  | signatureAlgorithm
  | issuer
  | keyEpoch
  | lamport
  | childIndex
  | destinationIndex
  | cite
  | grantId
  | grantParent
  | grantScope
  | rosterMember (index : Nat)
  | participant (index : Nat)
  deriving DecidableEq

inductive ListField where
  | roster
  | participants
  deriving DecidableEq

inductive ValidationError where
  | wrongSchema (expected found : String)
  | emptyBytes (field : ByteField)
  | bytesTooLarge (field : ByteField) (actual limit : Nat)
  | naturalTooLarge (field : NaturalField) (value limit : Nat)
  | algorithmOutOfRange (value : Nat)
  | uint64OutOfRange (field : NaturalField) (value : Nat)
  | listTooLarge (field : ListField) (actual limit : Nat)
  | nonCanonicalOrder (field : ListField) (previous current : Nat)
  | citeGrantMismatch (cite grantId : Nat)
  | nonCanonicalGrant (parent id : Nat)
  | childOutsideGrantScope (childIndex scope : Nat)
  | inconsistentNodeIndex (stable : Bytes) (child destination : Nat)
  | issuerNotInRoster (issuer : Nat)
  | participantNotInRoster (participant : Nat)
  deriving DecidableEq

abbrev ValidationResult (alpha : Type) := Except ValidationError alpha

structure ValidatedProjection where private mk ::
  projection : Projection
  config : ValidationConfig
  deriving DecidableEq

def ValidatedProjection.manifest (validated : ValidatedProjection) : Manifest :=
  validated.projection.manifest

private def checkBytes (field : ByteField) (bytes : Bytes) (limit : Nat) :
    ValidationResult Unit :=
  if bytes.isEmpty then throw (.emptyBytes field)
  else if bytes.length ≤ limit then pure ()
  else throw (.bytesTooLarge field bytes.length limit)

private def checkNatural (field : NaturalField) (value limit : Nat) :
    ValidationResult Unit :=
  if value ≤ limit then pure ()
  else throw (.naturalTooLarge field value limit)

private def firstNonIncreasing? : List Nat → Option (Nat × Nat)
  | [] | [_] => none
  | previous :: current :: rest =>
      if previous < current then firstNonIncreasing? (current :: rest)
      else some (previous, current)

private def checkCanonical (field : ListField) (values : List Nat) :
    ValidationResult Unit :=
  match firstNonIncreasing? values with
  | none => pure ()
  | some (previous, current) =>
      throw (.nonCanonicalOrder field previous current)

private def checkListBound (field : ListField) (actual limit : Nat) :
    ValidationResult Unit :=
  if actual ≤ limit then pure ()
  else throw (.listTooLarge field actual limit)

def validate (config : ValidationConfig) (projection : Projection) :
    ValidationResult ValidatedProjection := do
  if projection.schema = schema then pure ()
  else throw (.wrongSchema schema projection.schema)
  let move := projection.manifest.move
  let context := projection.manifest.context
  -- Fail resource bounds before reference and membership scans.
  checkListBound .roster context.roster.length config.bounds.maxRoster
  checkListBound .participants context.participants.length
    config.bounds.maxParticipants
  checkBytes .document move.document config.bounds.maxIdBytes
  checkBytes .genesis move.genesis config.bounds.maxIdBytes
  checkBytes .nonce move.nonce config.bounds.maxIdBytes
  checkBytes .operation move.operationId config.bounds.maxIdBytes
  checkBytes .child move.child.stable config.bounds.maxIdBytes
  match move.destination with
  | none => pure ()
  | some destination =>
      checkBytes .destination destination.stable config.bounds.maxIdBytes
  checkBytes .signature move.signature config.bounds.maxSignatureBytes
  checkBytes .substrateDigest context.substrateDigest config.bounds.maxDigestBytes
  checkBytes .historyHeadDigest context.historyHeadDigest config.bounds.maxDigestBytes
  checkBytes .origin context.originId config.bounds.maxIdBytes
  checkBytes .version context.versionId config.bounds.maxIdBytes
  if move.signatureAlgorithm ≤ UInt8.size - 1 then pure ()
  else throw (.algorithmOutOfRange move.signatureAlgorithm)
  let uint64Limit := UInt64.size - 1
  for (field, value) in [
      (.issuer, move.issuer), (.keyEpoch, move.keyEpoch), (.lamport, move.lamport)] do
    if value ≤ uint64Limit then pure ()
    else throw (.uint64OutOfRange field value)
  for (field, value) in [
      (.childIndex, move.child.kernelIndex), (.cite, move.cite),
      (.grantId, context.citedGrant.id), (.grantParent, context.citedGrant.parent),
      (.grantScope, context.citedGrant.scope)] do
    checkNatural field value config.bounds.maxNatural
  match move.destination with
  | none => pure ()
  | some destination =>
      checkNatural .destinationIndex destination.kernelIndex config.bounds.maxNatural
  for (value, index) in context.roster.zipIdx do
    checkNatural (.rosterMember index) value config.bounds.maxNatural
  for (value, index) in context.participants.zipIdx do
    checkNatural (.participant index) value config.bounds.maxNatural
  checkCanonical .roster context.roster
  checkCanonical .participants context.participants
  if move.cite = context.citedGrant.id then pure ()
  else throw (.citeGrantMismatch move.cite context.citedGrant.id)
  if context.citedGrant.parent < context.citedGrant.id then pure ()
  else throw (.nonCanonicalGrant context.citedGrant.parent context.citedGrant.id)
  if move.child.kernelIndex < context.citedGrant.scope then pure ()
  else throw (.childOutsideGrantScope move.child.kernelIndex context.citedGrant.scope)
  match move.destination with
  | some destination =>
      if destination.stable = move.child.stable ∧
          destination.kernelIndex ≠ move.child.kernelIndex then
        throw (.inconsistentNodeIndex destination.stable move.child.kernelIndex
          destination.kernelIndex)
      else pure ()
  | none => pure ()
  if context.roster.contains move.issuer then pure ()
  else throw (.issuerNotInRoster move.issuer)
  for participant in context.participants do
    if context.roster.contains participant then pure ()
    else throw (.participantNotInRoster participant)
  pure ⟨projection, config⟩

end Uwueave.Preo.RuntimeAuthV4Projection
