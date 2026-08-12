import Uwueave.Preo.Quickstart
import Uwueave.Preo.ProjectionV3

namespace PreoBench.Wave26.V3Checked0

open Uwueave.Preo Uwueave.Preo.Quickstart

def mk (_ : Unit) : ProjectionV3.ValidationResult String :=
  ProjectionV3.validateAndRender validationConfig
    (ProjectionV3.Projection.ofEncoding v3Artifact)

end PreoBench.Wave26.V3Checked0
