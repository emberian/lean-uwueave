/-
# Uwueave.Preo.RuntimeAuthV4Data — neutral runtime-auth manifest rows

This leaf is the first-order interchange boundary for one authenticated move
manifest sidecar.
It deliberately contains no signature verifier, authority predicate, world,
frontier, history, or proof.  Byte strings named `*Digest` below are opaque
deployment identities: equality is meaningful, but this module makes no hash
function, collision-resistance, or cryptographic-hardness claim.

The signed move fields mirror `Uwueave.RuntimeAuthV4.SignedRequest` without
importing that proof-rich module.  The context row additionally records the
exact cited grant scope, substrate/head/origin/version identities, and finite
roster/participant manifests.  `RuntimeAuthV4ProjectionCore` owns all
structural and resource validation.
-/
import Uwueave.Durable

namespace Uwueave.Preo.RuntimeAuthV4

set_option autoImplicit false

abbrev Bytes := Durable.Bytes
abbrev StableId := Bytes
abbrev Digest := Bytes

/-- Stable node identity together with the request-local kernel index. -/
structure NodeRow where
  stable : StableId
  kernelIndex : Nat
  deriving DecidableEq

/-- Exact grant tuple cited by the move.  Its authority and activity are not
reconstructed from this decoded row. -/
structure GrantScopeRow where
  id : Nat
  parent : Nat
  scope : Nat
  deriving DecidableEq

/-- Every field covered by the runtime request signature, expressed as neutral
first-order data. -/
structure SignedMoveRow where
  document : StableId
  genesis : StableId
  signatureAlgorithm : Nat
  issuer : Nat
  keyEpoch : Nat
  nonce : StableId
  operationId : StableId
  lamport : Nat
  child : NodeRow
  destination : Option NodeRow
  cite : Nat
  signature : Bytes
  deriving DecidableEq

/-- Deployment context retained beside the signed move.  The four identity
byte strings are authored bindings, not proof that any hash was computed.
`roster` and `participants` have a canonical strictly-increasing form enforced
by validation. -/
structure ContextRow where
  citedGrant : GrantScopeRow
  substrateDigest : Digest
  historyHeadDigest : Digest
  originId : StableId
  versionId : StableId
  roster : List Nat
  participants : List Nat
  deriving DecidableEq

/-- One runtime-auth manifest sidecar payload.  The outer durable format is
the sole byte-level version; the independent projection schema string belongs
only to the untrusted host `Projection`. -/
structure Manifest where
  move : SignedMoveRow
  context : ContextRow
  deriving DecidableEq

def schema : String := "uwueave/preo-runtime-auth/v4"

def Manifest.ofRows (move : SignedMoveRow) (context : ContextRow) : Manifest :=
  ⟨move, context⟩

end Uwueave.Preo.RuntimeAuthV4
