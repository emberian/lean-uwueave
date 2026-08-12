import AuthenticatedFrontierCommon
import Uwueave.TrustFloor

namespace Canary.Wave27.PositiveAuthenticatedFrontier

open Uwueave Uwueave.Catalog
open Uwueave.AuthenticatedFrontier
open Canary.Wave27.AuthenticatedFrontierCommon

example : progress.acceptedEvent = acceptedProgressEvent := rfl
example : Authenticity.WasIssued progressIssued progress.acceptedEvent.record :=
  progress.wasIssued
example : progress.source = 7 := rfl
example : progress.acceptedEvent.event.kind = progressKind :=
  progress.progress_domain
example : progress.acceptedEvent.record.issuer ∈ roster :=
  progress.issuer_mem_roster

example : Frontier.DeliveryAdvance candidateStamp advance.issued
    (codec.beforeOf progress.acceptedEvent.event)
    (codec.afterOf progress.acceptedEvent.event)
    advance.deliveredBefore advance.deliveredAfter :=
  advance.toDeliveryAdvance

example : progress.acceptedEvent.event.kind ≠ 0 ∧
    progress.acceptedEvent.event.kind ≠ 1 ∧
    progress.acceptedEvent.event.kind ≠ 2 ∧
    progress.acceptedEvent.event.kind ≠ 3 ∧
    progress.acceptedEvent.event.kind ≠ 4 :=
  progress.refuses_ordinary_kind

#audit_floor_prefix Canary.Wave27.AuthenticatedFrontierCommon

end Canary.Wave27.PositiveAuthenticatedFrontier
