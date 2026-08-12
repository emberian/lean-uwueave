/- Canonical V3 durable-byte examples, kept out of the codec closure. -/
import Uwueave.Preo.ArtifactV3Durable
import Uwueave.Preo.ProjectionV3Examples

namespace Uwueave.Preo.ArtifactV3Durable.Examples

open Uwueave.Preo.ProjectionV3

def fullBytes : Bytes := projectionBytes ProjectionV3.Examples.fullEncoding

theorem full_roundtrip :
    decodeProjection fullBytes = some (ProjectionV3.Examples.fullEncoding, []) :=
  decodeProjection_projectionBytes _

theorem v2_refuses_full_v3 :
    Uwueave.Preo.ArtifactDurable.decodeProjection fullBytes = none := by
  simpa [fullBytes] using v2_decoder_refuses_v3
    ProjectionV3.Examples.fullEncoding []

end Uwueave.Preo.ArtifactV3Durable.Examples
