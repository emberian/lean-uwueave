import Uwueave.Preo.ProtocolSurface

namespace PreoBench.NativeProtocol

open Uwueave Uwueave.Preo.ProtocolSurface

preo_protocol Subject over Unit at () :=
  .seq [
    .operation { id := 1, crossings := 0, needs := [] },
    .repeat {
      count := 2,
      body := .sync {
        currency := .userPrompt,
        participants := [0],
        scope := 0,
        epoch := 0,
        evidence := .none,
        round := 0,
        barrier := 0 } } ]

end PreoBench.NativeProtocol
