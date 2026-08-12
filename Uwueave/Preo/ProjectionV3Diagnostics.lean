/- Optional `Repr` instances for V3 projection diagnostics. -/
import Uwueave.Preo.ProjectionV3Core
import Uwueave.Preo.ProjectionV2Diagnostics
import Uwueave.Preo.ArtifactV3Diagnostics

namespace Uwueave.Preo.ProjectionV3

deriving instance Repr for Projection
deriving instance Repr for ValidationBounds
deriving instance Repr for ValidationConfig
deriving instance Repr for BoundedList
deriving instance Repr for ValidationError
deriving instance Repr for ValidatedProjectionV3

end Uwueave.Preo.ProjectionV3
