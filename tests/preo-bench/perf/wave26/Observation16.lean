import Uwueave.Preo.StateProgramSurfaceTests

namespace PreoBench.Wave26.Observation16

open Uwueave Uwueave.Preo
open Uwueave.Preo.StateProgramSurface.Tests

def boundary : ResultProgram.ObservationBoundary AppState AppState where Authentic := Eq
def report : Journey.Report := Journey.reportAt start (by simp [Journey.StateReach])
def O00 := ResultProgram.ObservedReport.attach boundary start report rfl
def O01 := ResultProgram.ObservedReport.attach boundary start report rfl
def O02 := ResultProgram.ObservedReport.attach boundary start report rfl
def O03 := ResultProgram.ObservedReport.attach boundary start report rfl
def O04 := ResultProgram.ObservedReport.attach boundary start report rfl
def O05 := ResultProgram.ObservedReport.attach boundary start report rfl
def O06 := ResultProgram.ObservedReport.attach boundary start report rfl
def O07 := ResultProgram.ObservedReport.attach boundary start report rfl
def O08 := ResultProgram.ObservedReport.attach boundary start report rfl
def O09 := ResultProgram.ObservedReport.attach boundary start report rfl
def O10 := ResultProgram.ObservedReport.attach boundary start report rfl
def O11 := ResultProgram.ObservedReport.attach boundary start report rfl
def O12 := ResultProgram.ObservedReport.attach boundary start report rfl
def O13 := ResultProgram.ObservedReport.attach boundary start report rfl
def O14 := ResultProgram.ObservedReport.attach boundary start report rfl
def O15 := ResultProgram.ObservedReport.attach boundary start report rfl

end PreoBench.Wave26.Observation16
