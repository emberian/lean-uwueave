/- Optional `Repr` instances for neutral V3 rows. -/
import Uwueave.Preo.ArtifactV3Data
import Uwueave.Preo.ArtifactDiagnostics

namespace Uwueave.Preo.ArtifactV3

deriving instance Repr for SchemaId
deriving instance Repr for QueryId
deriving instance Repr for ResultId
deriving instance Repr for ProgramId
deriving instance Repr for CertificateId
deriving instance Repr for WorldId
deriving instance Repr for ResolutionId
deriving instance Repr for SurfaceId
deriving instance Repr for ReasonId
deriving instance Repr for HoleKind
deriving instance Repr for HoleRow
deriving instance Repr for AnalysisTag
deriving instance Repr for QueryRow
deriving instance Repr for ResolutionRow
deriving instance Repr for StatusShape
deriving instance Repr for VisibilityRow
deriving instance Repr for DisclosureRow
deriving instance Repr for ResultRow
deriving instance Repr for CertificateRow
deriving instance Repr for ArtifactV3Encoding

end Uwueave.Preo.ArtifactV3
