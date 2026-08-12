import AuthenticatedEraCertificateCommon

namespace Canary.Wave28.IncompleteAnnouncement

open Uwueave
open Uwueave.AuthenticatedEraCertificate

-- Reusing authentication while decoding an incomplete after-world must not
-- allow the complete announcement proof from the truthful codec to typecheck.
example : CompleteAnnouncement (codec := Fixtures.incompleteCodec)
    (progress := Fixtures.progress) Fixtures.advance := by
  exact Fixtures.complete

end Canary.Wave28.IncompleteAnnouncement
