import Uwueave.AuthenticatedWorldContext

namespace PreoBench.Wave27.AuthenticatedContext0

open Uwueave

def mk (_ : Unit) : AuthenticatedWorldContext.PositionCodec Nat Nat Nat where
  worldOf := fun _ => []
  valueOf := fun _ => 0
  positionOf := fun _ => ⟨[], 0, .field⟩
  originOf := fun _ => 0
  versionOf := fun _ => 0

end PreoBench.Wave27.AuthenticatedContext0
