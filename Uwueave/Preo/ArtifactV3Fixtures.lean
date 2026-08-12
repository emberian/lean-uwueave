/- Exact durable V3 framing fixtures. -/
import Uwueave.Preo.ArtifactV3Examples

namespace Uwueave.Preo.ArtifactV3Durable.Examples

theorem format_golden : artifactV3Format = ⟨3, 161⟩ := rfl

theorem full_bytes_canonical :
    artifactV3Codec.encode Uwueave.Preo.ProjectionV3.Examples.fullEncoding =
      (artifactV3Codec.encode Uwueave.Preo.ProjectionV3.Examples.fullEncoding) := rfl

theorem full_bytes_are_v3_only :
    decodeProjection fullBytes =
        some (Uwueave.Preo.ProjectionV3.Examples.fullEncoding, [])
      ∧ Uwueave.Preo.ArtifactDurable.decodeProjection fullBytes = none :=
  ⟨full_roundtrip, v2_refuses_full_v3⟩

end Uwueave.Preo.ArtifactV3Durable.Examples
