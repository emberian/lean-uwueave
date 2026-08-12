import Uwueave.Preo.StateProgramSurfaceTests

namespace PreoBench.Wave26.Observation0

open Uwueave Uwueave.Preo
open Uwueave.Preo.StateProgramSurface.Tests

def boundary : ResultProgram.ObservationBoundary AppState AppState where
  Authentic := Eq

def report : Journey.Report := Journey.reportAt start (by simp [Journey.StateReach])

end PreoBench.Wave26.Observation0
