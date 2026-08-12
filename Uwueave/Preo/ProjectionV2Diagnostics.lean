/-
# Uwueave.Preo.ProjectionV2Diagnostics — optional V2 pretty printers

This module restores the original V2 `Repr` instance names for explicit
diagnostic imports. It imports V1 diagnostics because V2's `.base` error
contains a V1 validation error; neither production core nor renderer imports
these pretty printers.
-/
import Uwueave.Preo.ProjectionV2Core
import Uwueave.Preo.ProjectionV1Diagnostics

namespace Uwueave.Preo.ProjectionV2

deriving instance Repr for Projection
deriving instance Repr for ValidationBounds
deriving instance Repr for ValidationConfig
deriving instance Repr for BudgetBoundedList
deriving instance Repr for ValidationError
deriving instance Repr for ValidatedProjectionV2

end Uwueave.Preo.ProjectionV2
