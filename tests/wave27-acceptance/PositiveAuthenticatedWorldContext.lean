import Uwueave.AuthenticatedWorldContext
import Uwueave.TrustFloor

namespace Canary.Wave27.PositiveAuthenticatedWorldContext

open Uwueave Uwueave.Catalog
open Uwueave.AuthenticatedWorldContext

example : Authenticity.WasIssued positionIssued positionRecord :=
  issuedPosition.wasIssued

example : exactPositionClaim.candidate = positionCandidate := rfl
example : exactPositionClaim.signed = issuedPosition := rfl
example : WorldFuture.DeliveryFuture WorldFuture.wPending
    WorldFuture.wDelivered := authenticated_delivery_projects

example : beforeConsumption.consumed (2, 1, 4) = false ∧
    afterConsumption.consumed (2, 1, 4) = true := delegate_consumed_once

example : ¬ ∃ admitted : IssuedPositionEvent Authenticity.toyScheme
      AuthenticatedAdmission.moveKeys Authenticity.noRevocations positionIssued
      (fun record => record = forgedPositionRecord),
    admitted.accepted.record = forgedPositionRecord :=
  accepted_forgery_not_promoted

example : ¬ Nonempty (ContextualPositionClaim exactPositionClaim
    alternateConsumption usedDelegate positionHolder) :=
  stale_base_refuses_position

example : ¬ Nonempty (ContextualPositionClaim exactPositionClaim
    wrongOriginConsumption usedDelegate positionHolder) :=
  wrong_origin_refuses_position

example : ¬ Available afterConsumption positionCandidate.source (2, 1, 4) :=
  consumed_token_not_reusable

#audit_floor_prefix Uwueave.AuthenticatedWorldContext

end Canary.Wave27.PositiveAuthenticatedWorldContext
