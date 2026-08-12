import Uwueave.Preo.Elab

namespace PreoBench.Custom1

open Uwueave Uwueave.Preo

preo Subject where
  field f00 : (custom (Catalog.GSet Nat)) := fun _ => false

end PreoBench.Custom1
