import Uwueave.TrustFloor

open Uwueave.TrustFloor

-- One exact, real exception closes one exact disk gap.
example :
    uncoveredModules
        [`Uwueave.Loaded, `Uwueave.ExecutableMain]
        [`Uwueave.Loaded]
        [`Uwueave.ExecutableMain] = [] := by
  decide

-- Every declared exception must itself occur in the disk census.
example :
    absentExceptions
        [`Uwueave.Loaded, `Uwueave.ExecutableMain]
        [`Uwueave.ExecutableMain] = [] := by
  decide

example :
    moduleCoverageFailure?
        [`Uwueave.Loaded, `Uwueave.ExecutableMain]
        [`Uwueave.Loaded]
        [`Uwueave.ExecutableMain] = none := by
  decide
