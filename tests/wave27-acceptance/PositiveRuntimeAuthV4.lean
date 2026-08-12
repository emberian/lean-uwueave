import RuntimeAuthV4Common
import Uwueave.TrustFloor

namespace Canary.Wave27.PositiveRuntimeAuthV4

open Uwueave
open Uwueave.Preo.RuntimeAuthV4
open Uwueave.Preo.RuntimeAuthV4Projection
open Canary.Wave27.RuntimeAuthV4Common

example : checked.toManifest = manifest := rfl
example : manifest.move = SignedMoveRow.ofRequest request := rfl
example : manifest.move.issuer = 17 := rfl
example : manifest.context.citedGrant.id = 7 := rfl
example : checked.sourceSigningBytes =
    Uwueave.RuntimeAuthV4.signingBytesV4 request.content := rfl

example : Uwueave.Preo.RuntimeAuthV4Durable.decodeManifestExact bytes =
    some manifest :=
  Uwueave.Preo.RuntimeAuthV4Durable.decodeManifestExact_manifestBytes manifest

example : (validate config projection).isOk = true := validation_ok
example : validated.manifest = manifest := by decide

#audit_floor_prefix Canary.Wave27.RuntimeAuthV4Common

end Canary.Wave27.PositiveRuntimeAuthV4
