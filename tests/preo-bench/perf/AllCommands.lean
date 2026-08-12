import Uwueave.Preo.Elab
import Uwueave.Preo.ProtocolSurface

namespace PreoBench.AllCommands

open Uwueave Uwueave.Preo Uwueave.Preo.ProtocolSurface

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
    participants := [0, 1],
    scope := 7,
    epoch := 3,
    evidence := .named(11),
    round := 0,
    barrier := 5 }

preo Subject where
  field marker : Counter
  field tags : GrowSet Nat
  field external : (custom (Catalog.GSet Nat)) := fun _ => false
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
  | field tags := { id := 103, kind := 11, carrier := 107, key := none }
  | field external := { id := 108, kind := 12, carrier := 107, key := none }
  | invariant nonnegative := {
    id := 104, carrier := 101, codec := Uwueave.Preo.Export.Examples.natCodec,
    answered := rfl }
  | future Delivered := {
    certificate := Certificate, id := 105, world := 106, relation := 107 }
  | budget Accepted for S := {
    id := 111, session := 109, plan := 110, samePlan := rfl }

end PreoBench.AllCommands
