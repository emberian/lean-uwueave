import Uwueave.Preo.ArtifactInspectionMain
import Uwueave.TrustFloor

-- Kept in a separate process from ArtifactEmitMain because both own `main`.
#audit_floor_module Uwueave.Preo.ArtifactInspectionMain

#assert_module_owns Uwueave.Preo.ArtifactInspectionMain main
