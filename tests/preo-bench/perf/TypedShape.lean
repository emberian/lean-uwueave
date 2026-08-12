import Uwueave.Preo.Elab

namespace PreoBench.TypedShape

open Lean Elab Command
open Uwueave Uwueave.Preo

preo Subject where
  field marker : Counter
  typed derive D00 over {
    schema := [.nat, .nat], reach := [Incremental.before]
  } := .natSucc (.field 0)

/-- The optimization deliberately suppresses only compiler metadata.  The
public constructor and dependent projections remain directly usable. -/
def rebuildReachReport (report : Subject.D00.ReachReport) :
    Subject.D00.ReachReport :=
  Subject.D00.ReachReport.mk report.checked report.inReach

private partial def exprNodes : Expr → Nat
  | .bvar _ | .fvar _ | .mvar _ | .sort _ | .const .. | .lit _ => 1
  | .app fn argument => 1 + exprNodes fn + exprNodes argument
  | .lam _ domain body _ | .forallE _ domain body _ =>
      1 + exprNodes domain + exprNodes body
  | .letE _ type value body _ =>
      1 + exprNodes type + exprNodes value + exprNodes body
  | .mdata _ body | .proj _ _ body => 1 + exprNodes body

run_cmd do
  let targetPrefix : Name := .str (.str (.str .anonymous "PreoBench") "TypedShape") "Subject"
  let constants := (← getEnv).constants.toList
    |>.filter (fun (name, _) => targetPrefix.isPrefixOf name)
    |>.toArray
    |>.qsort (fun left right => left.1.toString < right.1.toString)
  let mut totalType := 0
  let mut totalValue := 0
  for (name, info) in constants do
    let typeNodes := exprNodes info.type
    let valueNodes := info.value?.map exprNodes |>.getD 0
    totalType := totalType + typeNodes
    totalValue := totalValue + valueNodes
    logInfo m!"SHAPE\t{name}\t{typeNodes}\t{valueNodes}"
  logInfo m!"TOTAL\t{constants.size}\t{totalType}\t{totalValue}"

end PreoBench.TypedShape
