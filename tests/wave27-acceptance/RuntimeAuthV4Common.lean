/-
# RuntimeAuthV4Common — checked request to canonical neutral sidecar

The verification, resolver, authority, membership, nonce, active-grant, and
finite-context receipts are explicit.  Only `CheckedManifest.ofReady` may
erase them into the neutral manifest carried by the durable codec.
-/
import Uwueave.Preo.RuntimeAuthV4Checked
import Uwueave.Preo.RuntimeAuthV4Durable
import Uwueave.Preo.RuntimeAuthV4Projection

namespace Canary.Wave27.RuntimeAuthV4Common

open Uwueave
open Uwueave.Preo.RuntimeAuthV4
open Uwueave.Preo.RuntimeAuthV4Projection

abbrev request := Uwueave.RuntimeAuthV4.fixtureRequest

def verification : Uwueave.RuntimeAuthV4.VerificationBoundary where
  Accepts := fun _ _ _ => True

def resolver : Uwueave.RuntimeAuthV4.ResolverBoundary where
  Resolve := fun _document _genesis stable =>
    if stable = request.content.move.child.stable then
      some request.content.move.child.kernelIndex
    else some Uwueave.RuntimeAuthV4.fixtureNodeB.kernelIndex

def allow (_ : Uwueave.RuntimeAuthV4.SignedRequest) : Prop := True

def ready : Uwueave.RuntimeAuthV4.ReadyForExecution verification resolver
    allow allow [] request where
  verified := ⟨trivial⟩
  resolved := by
    constructor
    · simp [resolver, request, Uwueave.RuntimeAuthV4.fixtureRequest,
        Uwueave.RuntimeAuthV4.fixtureContent,
        Uwueave.RuntimeAuthV4.fixtureMove,
        Uwueave.RuntimeAuthV4.fixtureNodeA]
    · intro node member
      simp [request, Uwueave.RuntimeAuthV4.fixtureRequest,
        Uwueave.RuntimeAuthV4.fixtureContent,
        Uwueave.RuntimeAuthV4.fixtureMove] at member
      subst node
      simp [resolver, request, Uwueave.RuntimeAuthV4.fixtureRequest,
        Uwueave.RuntimeAuthV4.fixtureContent,
        Uwueave.RuntimeAuthV4.fixtureMove,
        Uwueave.RuntimeAuthV4.fixtureNodeA,
        Uwueave.RuntimeAuthV4.fixtureNodeB]
  fresh := by simp [Uwueave.RuntimeAuthV4.NonceFresh]
  authorized := trivial
  isMember := trivial

def grant : Authority.Grant := (7, 0, 4)

def grantState : Gated.GatedState :=
  (fun candidate => decide (candidate = grant),
    (fun _ => false, fun _ => false))

def grantReceipt : GrantReceipt request where
  state := grantState
  grant := grant
  active := .root (by decide) (by decide)
  parent_lt_id := by decide
  cite_exact := rfl
  child_covered := by decide

def context : ContextReceipt request where
  substrateDigest := [201]
  historyHeadDigest := [202]
  originId := [203]
  versionId := [4]
  roster := [17]
  participants := [17]
  substrate_nonempty := by decide
  history_head_nonempty := by decide
  origin_nonempty := by decide
  version_nonempty := by decide
  roster_canonical := by decide
  participants_canonical := by decide
  issuer_mem := by decide
  participants_mem := by simp

def checked : CheckedManifest (boundary := verification) (resolver := resolver)
    (authority := allow) (membership := allow) (seen := []) request :=
  CheckedManifest.ofReady request ready rfl grantReceipt context

def manifest : Manifest := checked.toManifest

def projection : Projection := Projection.ofManifest manifest

def config : ValidationConfig where
  bounds :=
    { maxIdBytes := 16
      maxSignatureBytes := 16
      maxDigestBytes := 16
      maxRoster := 4
      maxParticipants := 4
      maxNatural := 32 }

theorem validation_ok : (validate config projection).isOk = true := by
  decide

def validated : ValidatedProjection :=
  Option.get (validate config projection).toOption (by decide)

def bytes : Uwueave.Preo.RuntimeAuthV4Durable.Bytes :=
  Uwueave.Preo.RuntimeAuthV4Durable.manifestBytes manifest

end Canary.Wave27.RuntimeAuthV4Common
