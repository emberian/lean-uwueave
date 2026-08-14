/-
# Wave30AuthRuntimeCommon — isolated kind-3 admission fixtures

Every canary runs in a fresh Lean process.  These are syntax, shape, width,
and exact-projection fixtures only; they manufacture no verification,
historical-context, authority, execution, or durability premise.
-/
import Uwueave.RuntimeAuthV4Kernel

namespace Canary.Wave30.AuthRuntimeCommon

open Uwueave.RuntimeAuthV4
open Uwueave.RuntimeAuthV4Kernel

def content : ContextSignedContent :=
  ⟨fixtureContent.document, fixtureContent.genesis,
    fixtureContent.signatureAlgorithm, fixtureContent.issuer,
    fixtureContent.keyEpoch, fixtureContent.nonce, fixtureMove, [40, 41]⟩

def request : ContextSignedRequest := ⟨content, fixtureRequest.signature⟩
def projection : AdmissionProjection := AdmissionProjection.ofRequest request
def canonicalBytes : List UInt8 := encodeContextRequest request
def exactBound : Nat := canonicalBytes.length

def project (candidate : ContextSignedRequest) : AdmissionOutcome :=
  projectAdmission (encodeContextRequest candidate).length
    (encodeContextRequest candidate)

def malformedBytes : List UInt8 := requestPrefixAt versionV4 contextMoveKind
def oldVersionBytes : List UInt8 :=
  requestPrefixAt 3 contextMoveKind ++ contextRequestPayloadWire.encode request

def emptyDocument : ContextSignedRequest :=
  ⟨{ content with document := [] }, request.signature⟩
def emptyGenesis : ContextSignedRequest :=
  ⟨{ content with genesis := [] }, request.signature⟩
def emptyContext : ContextSignedRequest :=
  ⟨{ content with contextCommitment := [] }, request.signature⟩
def emptyNonce : ContextSignedRequest :=
  ⟨{ content with nonce := [] }, request.signature⟩
def emptyOperationId : ContextSignedRequest :=
  ⟨{ content with move := { fixtureMove with operationId := [] } },
    request.signature⟩
def emptyChildId : ContextSignedRequest :=
  ⟨{ content with move :=
      { fixtureMove with child := ⟨[], fixtureNodeA.kernelIndex⟩ } },
    request.signature⟩
def emptyDestinationId : ContextSignedRequest :=
  ⟨{ content with move :=
      { fixtureMove with dest := some ⟨[], fixtureNodeB.kernelIndex⟩ } },
    request.signature⟩
def emptySignature : ContextSignedRequest := ⟨content, []⟩

def childTooLarge : ContextSignedRequest :=
  ⟨{ content with move := { fixtureMove with child :=
      ⟨fixtureNodeA.stable, maximumUInt64Nat + 1⟩ } }, request.signature⟩
def destinationTooLargeNode : NodeRef :=
  ⟨fixtureNodeB.stable, maximumInt64Nat + 1⟩
def destinationTooLarge : ContextSignedRequest :=
  ⟨{ content with move := { fixtureMove with dest := (some destinationTooLargeNode) } },
    request.signature⟩
def citeTooLarge : ContextSignedRequest :=
  ⟨{ content with move := { fixtureMove with cite := maximumUInt64Nat + 1 } },
    request.signature⟩

/- Each mutation is still valid kind-3 input.  The projection must preserve it
instead of substituting any field from the fixture or from host state. -/
def changedDocument : ContextSignedRequest :=
  ⟨{ content with document := [31] }, request.signature⟩
def changedGenesis : ContextSignedRequest :=
  ⟨{ content with genesis := [32] }, request.signature⟩
def changedContext : ContextSignedRequest :=
  ⟨{ content with contextCommitment := [42] }, request.signature⟩
def changedAlgorithm : ContextSignedRequest :=
  ⟨{ content with signatureAlgorithm := 3 }, request.signature⟩
def changedIssuer : ContextSignedRequest :=
  ⟨{ content with issuer := 23 }, request.signature⟩
def changedEpoch : ContextSignedRequest :=
  ⟨{ content with keyEpoch := 5 }, request.signature⟩
def changedNonce : ContextSignedRequest :=
  ⟨{ content with nonce := [33] }, request.signature⟩
def changedOperationId : ContextSignedRequest :=
  ⟨{ content with move := { fixtureMove with operationId := [34] } },
    request.signature⟩
def changedLamport : ContextSignedRequest :=
  ⟨{ content with move := { fixtureMove with lamport := 19 } },
    request.signature⟩
def changedChildStable : ContextSignedRequest :=
  ⟨{ content with move := { fixtureMove with child :=
      ⟨[35], fixtureNodeA.kernelIndex⟩ } }, request.signature⟩
def changedChildIndex : ContextSignedRequest :=
  ⟨{ content with move := { fixtureMove with child :=
      ⟨fixtureNodeA.stable, 13⟩ } }, request.signature⟩
def changedDestinationStableNode : NodeRef :=
  ⟨[36], fixtureNodeB.kernelIndex⟩
def changedDestinationStable : ContextSignedRequest :=
  ⟨{ content with move := { fixtureMove with dest :=
      (some changedDestinationStableNode) } }, request.signature⟩
def changedDestinationIndexNode : NodeRef := ⟨fixtureNodeB.stable, 14⟩
def changedDestinationIndex : ContextSignedRequest :=
  ⟨{ content with move := { fixtureMove with dest :=
      (some changedDestinationIndexNode) } }, request.signature⟩
def changedDestinationPresence : ContextSignedRequest :=
  ⟨{ content with move := { fixtureMove with dest := none } }, request.signature⟩
def changedCite : ContextSignedRequest :=
  ⟨{ content with move := { fixtureMove with cite := 15 } }, request.signature⟩
def changedSignature : ContextSignedRequest := ⟨content, [37]⟩

end Canary.Wave30.AuthRuntimeCommon
