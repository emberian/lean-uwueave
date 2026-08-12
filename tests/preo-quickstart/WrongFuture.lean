import Uwueave.Preo.Quickstart

namespace Canary.PreoQuickstart.WrongFuture

open Uwueave Uwueave.Preo
open Uwueave.Preo.Quickstart

def OtherFuture : Future.FutureDecl appWorldModel where
  name := "quickstart/other-future"
  scope := .extension
  future := fun _ _ => True

def rejected : BoundResult.WorldBinding OtherFuture Journey.Result :=
  worldBinding

end Canary.PreoQuickstart.WrongFuture
