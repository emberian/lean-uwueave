import Uwueave.AuthenticatedWorldContext

namespace PreoBench.Wave27.AuthenticatedContext1

open Uwueave

def mk (_ : Unit) : AuthenticatedWorldContext.PositionCodec Nat Nat Nat where
  worldOf := fun _ => []
  valueOf := fun _ => 0
  positionOf := fun _ => ⟨[], 0, .field⟩
  originOf := fun _ => 0
  versionOf := fun _ => 0

def C00 := mk ()

end PreoBench.Wave27.AuthenticatedContext1
