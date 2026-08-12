import Uwueave.AuthenticatedFrontier

namespace PreoBench.Wave27.Frontier16

open Uwueave Uwueave.Catalog

def none : GSet (AuthenticatedFrontier.CandidateEvent Nat Nat) := fun _ => false
def mk (_ : Unit) : AuthenticatedFrontier.ProgressCodec Nat Nat where
  timeOf := fun _ => 0
  beforeOf := fun _ => Frontier.empty _
  afterOf := fun _ => Frontier.empty _
  issuedOf := fun _ => none
  deliveredBeforeOf := fun _ => none
  deliveredAfterOf := fun _ => none
def F00 := mk ()
def F01 := mk ()
def F02 := mk ()
def F03 := mk ()
def F04 := mk ()
def F05 := mk ()
def F06 := mk ()
def F07 := mk ()
def F08 := mk ()
def F09 := mk ()
def F10 := mk ()
def F11 := mk ()
def F12 := mk ()
def F13 := mk ()
def F14 := mk ()
def F15 := mk ()

end PreoBench.Wave27.Frontier16
