import Uwueave.Preo.StateProgramSurfaceTests

namespace PreoBench.Wave26.Program16

open Uwueave Uwueave.Preo
open Uwueave.Preo.StateProgramSurface.Tests

preo_program P00 over { state := AppState, schema := AppSchema, project := appProject,
  reach := [start, later], raw := .natSucc (.field 0), futureId := "bench/program/00",
  resolution := .preserveFork, policy := natPolicy }
preo_program P01 over { state := AppState, schema := AppSchema, project := appProject,
  reach := [start, later], raw := .natSucc (.field 0), futureId := "bench/program/01",
  resolution := .preserveFork, policy := natPolicy }
preo_program P02 over { state := AppState, schema := AppSchema, project := appProject,
  reach := [start, later], raw := .natSucc (.field 0), futureId := "bench/program/02",
  resolution := .preserveFork, policy := natPolicy }
preo_program P03 over { state := AppState, schema := AppSchema, project := appProject,
  reach := [start, later], raw := .natSucc (.field 0), futureId := "bench/program/03",
  resolution := .preserveFork, policy := natPolicy }
preo_program P04 over { state := AppState, schema := AppSchema, project := appProject,
  reach := [start, later], raw := .natSucc (.field 0), futureId := "bench/program/04",
  resolution := .preserveFork, policy := natPolicy }
preo_program P05 over { state := AppState, schema := AppSchema, project := appProject,
  reach := [start, later], raw := .natSucc (.field 0), futureId := "bench/program/05",
  resolution := .preserveFork, policy := natPolicy }
preo_program P06 over { state := AppState, schema := AppSchema, project := appProject,
  reach := [start, later], raw := .natSucc (.field 0), futureId := "bench/program/06",
  resolution := .preserveFork, policy := natPolicy }
preo_program P07 over { state := AppState, schema := AppSchema, project := appProject,
  reach := [start, later], raw := .natSucc (.field 0), futureId := "bench/program/07",
  resolution := .preserveFork, policy := natPolicy }
preo_program P08 over { state := AppState, schema := AppSchema, project := appProject,
  reach := [start, later], raw := .natSucc (.field 0), futureId := "bench/program/08",
  resolution := .preserveFork, policy := natPolicy }
preo_program P09 over { state := AppState, schema := AppSchema, project := appProject,
  reach := [start, later], raw := .natSucc (.field 0), futureId := "bench/program/09",
  resolution := .preserveFork, policy := natPolicy }
preo_program P10 over { state := AppState, schema := AppSchema, project := appProject,
  reach := [start, later], raw := .natSucc (.field 0), futureId := "bench/program/10",
  resolution := .preserveFork, policy := natPolicy }
preo_program P11 over { state := AppState, schema := AppSchema, project := appProject,
  reach := [start, later], raw := .natSucc (.field 0), futureId := "bench/program/11",
  resolution := .preserveFork, policy := natPolicy }
preo_program P12 over { state := AppState, schema := AppSchema, project := appProject,
  reach := [start, later], raw := .natSucc (.field 0), futureId := "bench/program/12",
  resolution := .preserveFork, policy := natPolicy }
preo_program P13 over { state := AppState, schema := AppSchema, project := appProject,
  reach := [start, later], raw := .natSucc (.field 0), futureId := "bench/program/13",
  resolution := .preserveFork, policy := natPolicy }
preo_program P14 over { state := AppState, schema := AppSchema, project := appProject,
  reach := [start, later], raw := .natSucc (.field 0), futureId := "bench/program/14",
  resolution := .preserveFork, policy := natPolicy }
preo_program P15 over { state := AppState, schema := AppSchema, project := appProject,
  reach := [start, later], raw := .natSucc (.field 0), futureId := "bench/program/15",
  resolution := .preserveFork, policy := natPolicy }

end PreoBench.Wave26.Program16
