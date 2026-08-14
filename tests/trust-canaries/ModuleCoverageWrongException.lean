import Uwueave.TrustFloor

open Uwueave.TrustFloor

-- Adding an exception that does not exist on disk must emit the real gate's
-- exception diagnostic, rather than fail through an unrelated proof tactic.
run_cmd do
  if let some failure :=
      moduleCoverageFailure?
        [`Uwueave.Loaded, `Uwueave.ExecutableMain]
        [`Uwueave.Loaded]
        [`Uwueave.ExecutableMain, `Uwueave.InventedMain] then
    throwError failure
