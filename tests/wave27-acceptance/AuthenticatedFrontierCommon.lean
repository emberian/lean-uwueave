/-
# AuthenticatedFrontierCommon — one exact issued progress event

The toy signature scheme is intentionally insecure, but its accepted trace is
still useful for testing the dependency shape: acceptance, receipt, genuine
issuance, roster membership, source binding, and lawful delivery advance are
all supplied separately.
-/
import Uwueave.AuthenticatedFrontier

namespace Canary.Wave27.AuthenticatedFrontierCommon

open Uwueave Uwueave.Catalog
open Uwueave.AuthenticatedFrontier

def progressEvent : Era.Event :=
  ⟨401, progressKind, 7, 7, 0⟩

def progressIssued : Authenticity.Issued :=
  fun issuer epoch payload =>
    issuer = 7 ∧ epoch = 1 ∧ payload = .event progressEvent

def progressRecord : Authenticity.SignedRecord Authenticity.toyScheme :=
  Authenticity.signRecord Authenticity.toyScheme 11 7 1 (.event progressEvent)

theorem progressRecord_accepted :
    Authenticity.Accepted Authenticity.toyScheme Authenticity.toyKeys
      Authenticity.noRevocations progressRecord := by
  apply Authenticity.signRecord_accepted
  · simp [Authenticity.toyKeys]
  · rfl

def acceptedProgressEvent : AuthenticatedAdmission.AcceptedEvent
    Authenticity.toyScheme Authenticity.toyKeys Authenticity.noRevocations :=
  ⟨progressRecord, progressEvent, rfl, progressRecord_accepted⟩

def receivedProgress : Authenticity.SignedRecord Authenticity.toyScheme → Prop :=
  fun record => record = progressRecord

theorem progress_trace_authentic :
    Authenticity.AuthenticIssuer Authenticity.toyScheme Authenticity.toyKeys
      Authenticity.noRevocations progressIssued receivedProgress := by
  intro record received _
  subst record
  exact ⟨rfl, rfl, rfl⟩

def roster : List Evidence.Source := [7]

def progress : AuthenticatedProgress Authenticity.toyScheme
    Authenticity.toyKeys Authenticity.noRevocations progressIssued
    receivedProgress roster :=
  AuthenticatedProgress.ofAuthenticIssuer acceptedProgressEvent rfl
    progress_trace_authentic rfl rfl (by change 7 ∈ [7]; simp)

def noCandidates : GSet (CandidateEvent Nat Nat) := fun _ => false

def codec : ProgressCodec Nat Nat where
  timeOf := fun _ => 0
  beforeOf := fun _ => Frontier.empty _
  afterOf := fun _ => Frontier.empty _
  issuedOf := fun _ => noCandidates
  deliveredBeforeOf := fun _ => noCandidates
  deliveredAfterOf := fun _ => noCandidates

def advance : AuthenticatedAdvance codec progress where
  source_settled := Frontier.complete_empty _
  lawful := Frontier.deliveryAdvance_refl (by
    intro event issued _
    exact Bool.noConfusion issued)

end Canary.Wave27.AuthenticatedFrontierCommon
