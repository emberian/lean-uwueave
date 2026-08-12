import Uwueave.AuthenticatedWorldContext

namespace PreoBench.Wave27.AuthenticatedContext16

open Uwueave

def mk (_ : Unit) : AuthenticatedWorldContext.PositionCodec Nat Nat Nat where
  worldOf := fun _ => []
  valueOf := fun _ => 0
  positionOf := fun _ => ⟨[], 0, .field⟩
  originOf := fun _ => 0
  versionOf := fun _ => 0

def C00 := mk ()
def C01 := mk ()
def C02 := mk ()
def C03 := mk ()
def C04 := mk ()
def C05 := mk ()
def C06 := mk ()
def C07 := mk ()
def C08 := mk ()
def C09 := mk ()
def C10 := mk ()
def C11 := mk ()
def C12 := mk ()
def C13 := mk ()
def C14 := mk ()
def C15 := mk ()

end PreoBench.Wave27.AuthenticatedContext16
