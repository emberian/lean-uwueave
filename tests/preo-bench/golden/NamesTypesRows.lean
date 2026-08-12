import Uwueave.Preo.Elab
import Uwueave.Preo.ProtocolSurface

namespace PreoBench.Golden.NamesTypesRows

open Uwueave Uwueave.Preo Uwueave.Preo.ProtocolSurface

namespace Inspector

open Lean Elab Command Meta

private def rowKindName : RowKind → String
  | .field => "field"
  | .invariant => "invariant"
  | .cross => "cross"
  | .derive => "derive"
  | .typedDerive => "typedDerive"
  | .future => "future"
  | .protocol => "protocol"
  | .session => "session"

private def canonicalType (name : Name) : CommandElabM String :=
  liftTermElabM do
    let type := (← getConstInfo name).type
    let rendered := (← withOptions (fun opts =>
      opts.setBool `pp.universes true
        |>.setBool `pp.explicit true
        |>.setBool `pp.fullNames true
        |>.set `pp.width (100000 : Nat)) <| ppExpr type).pretty
    return (rendered.replace "\n" " ").replace "\t" " "

syntax (name := preoBenchInspect) "#preo_bench_inspect " ident : command

@[command_elab preoBenchInspect]
def elabPreoBenchInspect : CommandElab := fun stx => do
      let targetStx := stx.getArgs.back!
      unless targetStx.isIdent do
        throwErrorAt targetStx "#preo_bench_inspect: expected a declaration prefix"
      let ns ← getCurrNamespace
      let fullPrefix := ns ++ targetStx.getId
      let env ← getEnv
      let names := env.constants.toList.filterMap (fun (name, _) =>
        if fullPrefix.isPrefixOf name then some name else none)
        |>.toArray |>.qsort Name.lt
      for name in names do
        logInfo m!"CONST\t{name}\t{← canonicalType name}"
      let rows := preoExt.getState env
      for row in rows do
        if fullPrefix == row.decl then
          logInfo m!"ROW\t{rowKindName row.kind}\t{row.name}\t{row.detail}\t{row.detail₂}\t{row.evidence}\t{row.isObligation}"

end Inspector

open Inspector

def config : ProjectionV2.ValidationConfig where
  bounds := {
    maxFields := 8, maxInvariants := 8, maxFutures := 8,
    maxSessions := 8, maxPlans := 8, maxBudgets := 8,
    maxObligationsPerSession := 8, maxActionsPerPlan := 8,
    maxProfileEntriesPerPlan := 5, maxProfileEntriesPerBudget := 5,
    maxParticipantsPerDemand := 8, maxWitnessWords := 8 }

preo_protocol Native over Unit at () :=
  .sync {
    currency := .peerBarrier,
    participants := [0],
    scope := 1,
    epoch := 2,
    evidence := .none,
    round := 3,
    barrier := 4 }

preo Subject where
  field marker : Counter
  invariant nonnegative : marker ≤ marker
  future Delivered on (Future.evidenceWorldModel Holes.Val) :=
    Future.Delivery Holes.Val
  typed derive Next over {
    schema := [.nat, .nat], reach := [Incremental.before]
  } := .natSucc (.field 0)
  protocol P over Unit := Protocol.coalescingProtocol
  session S runs P at ()

preo_certificate Certificate :
    Future.CheckedCertificate Subject.Delivered (fun _ => ())
      (fun _ => ()) (fun _ => True) Future.quiescedIndex := by
  refine { accepted := True.intro, soundForAll := ?_ }
  intro _ _ _ _
  rfl

preo_budget Accepted for Subject.S : Subject.S.plan.profile :=
  Subject.S.exactProfileUpperBound

preo_export Output from Subject : config :=
  declaration := { id := 100, stateType := 101, schema := 1 }
  | field marker := { id := 102, kind := 10, carrier := 101, key := none }
  | invariant nonnegative := {
    id := 103, carrier := 101, codec := Uwueave.Preo.Export.Examples.natCodec,
    answered := rfl }
  | future Delivered := {
    certificate := Certificate, id := 104, world := 105, relation := 106 }
  | budget Accepted for S := {
    id := 109, session := 107, plan := 108, samePlan := rfl }

#preo_bench_inspect Native
#preo_bench_inspect Subject
#preo_bench_inspect Certificate
#preo_bench_inspect Accepted
#preo_bench_inspect Output

end PreoBench.Golden.NamesTypesRows
