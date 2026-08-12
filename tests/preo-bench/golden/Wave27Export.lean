import Uwueave.Preo.ArtifactV3Surface
import Uwueave.Preo.Quickstart

namespace PreoBench.Golden.Wave27Export

open Uwueave Uwueave.Preo
open Uwueave.Preo.Quickstart

namespace Inspector

open Lean Elab Command Meta

private def canonicalType (name : Name) : CommandElabM String :=
  liftTermElabM do
    let type := (← getConstInfo name).type
    let rendered := (← withOptions (fun opts =>
      opts.setBool `pp.universes true
        |>.setBool `pp.explicit true
        |>.setBool `pp.fullNames true
        |>.set `pp.width (100000 : Nat)) <| ppExpr type).pretty
    return (rendered.replace "\n" " ").replace "\t" " "

syntax (name := wave27Inspect) "#wave27_inspect " ident : command

@[command_elab wave27Inspect]
def elabWave27Inspect : CommandElab := fun stx => do
  let targetStx := stx.getArgs.back!
  unless targetStx.isIdent do
    throwErrorAt targetStx "#wave27_inspect: expected a declaration prefix"
  let fullPrefix := (← getCurrNamespace) ++ targetStx.getId
  let env ← getEnv
  let names := env.constants.toList.filterMap (fun (name, _) =>
    if fullPrefix.isPrefixOf name then some name else none)
    |>.toArray |>.qsort Name.lt
  for name in names do
    logInfo m!"CONST\t{name}\t{← canonicalType name}"

end Inspector

open Inspector

def Boundary : ResultProgram.ObservationBoundary AppWorld AppState where
  Authentic := fun world state => world.state = state

def RunningReach : List AppWorld := [startWorld]

def Observed : ObservedBoundResult.ObservedCertifiedReport Boundary worldBinding
    RunningReach queryKey QueryAccepted startIndex :=
  ObservedBoundResult.attachAtWorld Boundary worldBinding RunningReach
    startIndex rfl (by change startWorld ∈ [startWorld]; simp)
    (by change startWorld ∈ [startWorld]; simp) QueryCertificate

/- The late work-cap refusal occurs after the command has attempted several
declarations. Successful exact-name reuse proves whole-prefix rollback. -/
/--
error: preo_export_v3: the automatic V3 route exceeded `maxWork`
-/
#guard_msgs (error, substring := true) in
preo_export_v3 Export from Journey := {
  base := baseArtifact,
  futureDecl := QueryFuture,
  binding := worldBinding,
  index := startIndex,
  observed := Observed,
  certificate := QueryCertificate,
  plan := artifactPlan,
  budget := artifactBudget,
  query := checkedQuery,
  future := artifactFuture,
  world := checkedWorld,
  resolutionId := fun _ => ⟨0⟩,
  surfaceId := StableId.surface,
  reasonId := fun _ => ⟨0⟩,
  certificateId := StableId.certificate,
  branch := exactStartBranch,
  maxWork := 0,
  config := validationConfig }

preo_export_v3 Export from Journey := {
  base := baseArtifact,
  futureDecl := QueryFuture,
  binding := worldBinding,
  index := startIndex,
  observed := Observed,
  certificate := QueryCertificate,
  plan := artifactPlan,
  budget := artifactBudget,
  query := checkedQuery,
  future := artifactFuture,
  world := checkedWorld,
  resolutionId := fun _ => ⟨0⟩,
  surfaceId := StableId.surface,
  reasonId := fun _ => ⟨0⟩,
  certificateId := StableId.certificate,
  branch := exactStartBranch,
  maxWork := 64,
  config := validationConfig }

#wave27_inspect Export

example : Export.StateProgram = Journey := rfl
example : Export.ObservedReport = Observed := rfl
example : Export.Encoding = v3Artifact := rfl
example : Export.Bytes = v3Bytes := rfl
example : Export.Validation.isOk = true := Export.validation_ok

end PreoBench.Golden.Wave27Export
