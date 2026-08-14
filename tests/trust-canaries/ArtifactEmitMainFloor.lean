import Uwueave.Preo.ArtifactEmitMain
import Uwueave.TrustFloor

-- The aggregate cannot import both root-main modules, so audit this exact
-- imported module by Lean's declaration ownership table.
#audit_floor_module Uwueave.Preo.ArtifactEmitMain

#assert_module_owns Uwueave.Preo.ArtifactEmitMain main
