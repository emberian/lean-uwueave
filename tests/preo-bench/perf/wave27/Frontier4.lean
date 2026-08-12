import Uwueave.AuthenticatedFrontier

namespace PreoBench.Wave27.Frontier4

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

end PreoBench.Wave27.Frontier4
