import AuthenticatedEraCertificateCommon

namespace Canary.Wave28.WrongReusableKey

open Uwueave Uwueave.AuthenticatedEraCertificate
open Canary.Wave28.AuthenticatedEraCertificateCommon

-- Reuse is licensed only by exact equality with the retained ERA key.  The
-- later announcement changes that key, so the refusal theorem cannot inhabit
-- the positive Matches proposition.
example : reusable.Matches wrongKey := by
  exact wrongKey_refused

end Canary.Wave28.WrongReusableKey
