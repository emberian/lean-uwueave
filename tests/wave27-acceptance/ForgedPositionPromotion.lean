import Uwueave.AuthenticatedWorldContext

namespace Canary.Wave27.ForgedPositionPromotion

open Uwueave
open Uwueave.AuthenticatedWorldContext

example : ∃ admitted : IssuedPositionEvent Authenticity.toyScheme
      AuthenticatedAdmission.moveKeys Authenticity.noRevocations positionIssued
      (fun record => record = forgedPositionRecord),
    admitted.accepted.record = forgedPositionRecord := by
  exact accepted_forgery_not_promoted

end Canary.Wave27.ForgedPositionPromotion
