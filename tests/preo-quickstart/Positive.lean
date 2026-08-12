import Uwueave.Preo.Quickstart

namespace Canary.PreoQuickstart.Positive

open Uwueave.Preo
open Uwueave.Preo.Quickstart

example : Journey.StateReach = [start, later] := rfl
example : Journey.EnvReach = [project start, project later] := rfl
example : (show Nat from Journey.Eval start) = 3 := rfl
example : QueryFuture.name = "quickstart/projected-environment-equality" := rfl
example : certifiedStartReport.report.checked.state = startWorld := rfl
example : JourneyPlan.Plan.profile .peerBarrier = 1 := rfl
example : JourneyBudget = JourneyPlan.ProfileUpperBound := rfl
example : checkedQuery.toRow.reads = [StableId.countField] := rfl
example : checkedQuery.toRow.holes =
    [{ path := [0], field := StableId.countField, kind := .field }] := rfl
example : ArtifactV3Durable.decodeProjection v3Bytes = some (v3Artifact, []) :=
  v3_bytes_reopen_exact

end Canary.PreoQuickstart.Positive
