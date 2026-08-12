import Uwueave.Preo.StateProgramSurfaceTests

namespace PreoBench.Wave26.Observation4

open Uwueave Uwueave.Preo
open Uwueave.Preo.StateProgramSurface.Tests

def boundary : ResultProgram.ObservationBoundary AppState AppState where Authentic := Eq
def report : Journey.Report := Journey.reportAt start (by simp [Journey.StateReach])
def O00 := ResultProgram.ObservedReport.attach boundary start report rfl
def O01 := ResultProgram.ObservedReport.attach boundary start report rfl
def O02 := ResultProgram.ObservedReport.attach boundary start report rfl
def O03 := ResultProgram.ObservedReport.attach boundary start report rfl

end PreoBench.Wave26.Observation4
