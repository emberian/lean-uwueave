/-
# Uwueave.Preo.ProjectionV1Diagnostics — optional V1 pretty printers

The validator and renderer do not inspect their own Lean representations.
Keeping derived `Repr` code here preserves the original instance names for
callers that explicitly import diagnostics, without adding either artifact or
projection pretty-printer code to the production closure. `ProjectionV1`
itself intentionally does not import this module.
-/
import Uwueave.Preo.ProjectionV1Core
import Uwueave.Preo.ArtifactDiagnostics

namespace Uwueave.Preo.ProjectionV1

deriving instance Repr for Projection
deriving instance Repr for ValidationBounds
deriving instance Repr for ValidationConfig
deriving instance Repr for StableIdKind
deriving instance Repr for DeclarationRowKind
deriving instance Repr for WitnessSide
deriving instance Repr for DemandLocation
deriving instance Repr for BoundedList
deriving instance Repr for ValidationError
deriving instance Repr for ValidatedProjectionV1

end Uwueave.Preo.ProjectionV1
