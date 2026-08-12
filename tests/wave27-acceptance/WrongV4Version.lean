import RuntimeAuthV4Common

namespace Canary.Wave27.WrongV4Version

open Uwueave
open Canary.Wave27.RuntimeAuthV4Common

set_option maxRecDepth 20000

example : Durable.decodeValue
    Uwueave.Preo.RuntimeAuthV4Durable.manifestCodec ⟨3, 162⟩
    (Uwueave.Preo.RuntimeAuthV4Durable.manifestBytes manifest) =
      some (manifest, []) := by
  exact Uwueave.Preo.RuntimeAuthV4Durable.changed_format_refused
    ⟨3, 162⟩ (by decide) manifest []

end Canary.Wave27.WrongV4Version
