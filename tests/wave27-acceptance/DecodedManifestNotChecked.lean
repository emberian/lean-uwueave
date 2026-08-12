import RuntimeAuthV4Common

namespace Canary.Wave27.DecodedManifestNotChecked

open Uwueave.Preo.RuntimeAuthV4
open Canary.Wave27.RuntimeAuthV4Common

-- Canonical decoding returns neutral rows.  It cannot be passed back as the
-- private proof-indexed checked boundary.
example : CheckedManifest (boundary := verification) (resolver := resolver)
    (authority := allow) (membership := allow) (seen := []) request :=
  manifest

end Canary.Wave27.DecodedManifestNotChecked
