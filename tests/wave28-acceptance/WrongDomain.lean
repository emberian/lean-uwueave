import AuthenticatedEraCertificateCommon

namespace Canary.Wave28.WrongDomain

open Uwueave
open Uwueave.AuthenticatedEraCertificate

-- An ordinary ERA join event cannot masquerade as the reserved progress
-- envelope used by the authenticated certificate bridge.
example : Fixtures.progress.acceptedEvent.event.kind = 0 := by
  decide

end Canary.Wave28.WrongDomain
