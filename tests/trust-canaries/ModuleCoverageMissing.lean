import Uwueave.TrustFloor

open Uwueave.TrustFloor

-- A disk module silently omitted from both the aggregate and the exception
-- list must emit the same gate-specific diagnostic as the real Audit command.
run_cmd do
  if let some failure :=
      moduleCoverageFailure?
        [`Uwueave.Loaded, `Uwueave.SilentlyOmitted]
        [`Uwueave.Loaded]
        [] then
    throwError failure
