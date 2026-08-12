import Uwueave.Preo.StateProgramSurfaceTests

namespace PreoBench.Wave26.Program4

open Uwueave Uwueave.Preo
open Uwueave.Preo.StateProgramSurface.Tests

preo_program P00 over {
  state := AppState, schema := AppSchema, project := appProject,
  reach := [start, later], raw := .natSucc (.field 0),
  futureId := "bench/program/00", resolution := .preserveFork, policy := natPolicy }
preo_program P01 over {
  state := AppState, schema := AppSchema, project := appProject,
  reach := [start, later], raw := .natSucc (.field 0),
  futureId := "bench/program/01", resolution := .preserveFork, policy := natPolicy }
preo_program P02 over {
  state := AppState, schema := AppSchema, project := appProject,
  reach := [start, later], raw := .natSucc (.field 0),
  futureId := "bench/program/02", resolution := .preserveFork, policy := natPolicy }
preo_program P03 over {
  state := AppState, schema := AppSchema, project := appProject,
  reach := [start, later], raw := .natSucc (.field 0),
  futureId := "bench/program/03", resolution := .preserveFork, policy := natPolicy }

end PreoBench.Wave26.Program4
