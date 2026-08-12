import AuthenticatedFrontierCommon

namespace Canary.Wave27.ForgedSignature

open Uwueave
open Canary.Wave27.AuthenticatedFrontierCommon

def forgedRecord : Authenticity.SignedRecord Authenticity.toyScheme :=
  { progressRecord with signature := [] }

example : Authenticity.Accepted Authenticity.toyScheme Authenticity.toyKeys
    Authenticity.noRevocations forgedRecord := by
  refine ⟨11, ?_, ?_, ?_⟩
  · change (if 7 = 7 ∧ 1 = 1 then some 11 else none) = some 11
    simp
  · rfl
  · rfl

end Canary.Wave27.ForgedSignature
