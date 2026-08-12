import Uwueave.Preo.Quickstart

namespace Canary.PreoQuickstart.WrongProjection

open Uwueave Uwueave.Preo
open Uwueave.Preo.Quickstart

def wrongProject (_state : AppState) : Expr.Env [.nat] :=
  .cons 0 .nil

preo_program Rejected over {
  state := AppState,
  schema := AppSchema,
  project := wrongProject,
  reach := [start],
  raw := .field 0,
  futureId := "wrong-projection",
  resolution := .preserveFork,
  policy := queryPolicy }

end Canary.PreoQuickstart.WrongProjection
