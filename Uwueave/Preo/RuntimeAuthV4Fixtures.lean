/-
# Uwueave.Preo.RuntimeAuthV4Fixtures — exact sidecar golden metadata

This opt-in leaf pins framing and size for the complete Lean-produced manifest
sidecar. It is intentionally separate from runtime imports and from the old
`UWV4` request bytes. The external SHA-256 of the exact 369-byte
`fixtureBytes` value is
`a9f32051b0e1e328ab08b253a808ba54cc5c4a4e9cb2b5d2550c3811cf03b819`.
That digest is a host regression label, not a cryptographic theorem.
-/
import Uwueave.Preo.RuntimeAuthV4Examples

namespace Uwueave.Preo.RuntimeAuthV4Fixtures

open Uwueave.Preo.RuntimeAuthV4Examples

set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem fixture_bytes_length : fixtureBytes.length = 369 := by decide

theorem fixture_bytes_format_prefix : fixtureBytes.take 4 = [213, 74, 4, 162] :=
  by decide

theorem fixture_bytes_decode_exact :
    Uwueave.Preo.RuntimeAuthV4Durable.decodeManifestExact fixtureBytes =
      some manifest :=
  Uwueave.Preo.RuntimeAuthV4Examples.fixture_bytes_decode_exact

end Uwueave.Preo.RuntimeAuthV4Fixtures
