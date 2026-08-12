import AuthenticatedEraCertificateCommon

namespace Canary.Wave28.AcceptedButUnissued

open Uwueave
open Uwueave.AuthenticatedEraCertificate

-- The toy signature accepts this record, but the exact issuance transcript
-- does not.  Acceptance alone must not cross into Verification.
example : Authenticity.WasIssued Fixtures.announcementIssued
    Fixtures.unissuedRecord := by
  exact Fixtures.unissuedRecord_not_issued

end Canary.Wave28.AcceptedButUnissued
