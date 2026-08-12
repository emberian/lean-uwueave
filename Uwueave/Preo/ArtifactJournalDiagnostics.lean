/-
# Uwueave.Preo.ArtifactJournalDiagnostics — optional journal pretty printers

The executable journal validator deliberately carries no Repr dependency.
This module restores the original derived diagnostics under the same public
namespace and instance names for proof, test, and operator-facing imports.
-/
import Uwueave.Preo.ArtifactJournalKernel
import Uwueave.Preo.ArtifactDiagnostics

namespace Uwueave.Preo.ArtifactJournalKernel

deriving instance Repr for Fault
deriving instance Repr for Refusal
deriving instance Repr for FrameInspection
deriving instance Repr for Record
deriving instance Repr for Stop
deriving instance Repr for ScanResult
deriving instance Repr for PhysicalRecord

end Uwueave.Preo.ArtifactJournalKernel
