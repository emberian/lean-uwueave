/-
# Uwueave.Preo.Elab.Report — `#preo_report` rendering core.

The report remains a readback of checked constants.  It stores no verdict and
registers no command elaborator; the facade owns the sole public handler.
-/
import Uwueave.Preo.Elab.Internal
import Uwueave.Preo.Elab.Readback

namespace Uwueave.Preo.Elab.Report

open Lean Elab Command Uwueave.Preo.Elab.Internal Uwueave.Preo.Elab.Readback

private def pad (s : String) (w : Nat) : String :=
  if s.length ≥ w then s else s ++ "".pushn ' ' (w - s.length)

/-- Non-registered implementation of `#preo_report`.  Answer columns are
reduced from each row's checked `Classification` at print time. -/
def elabPreoReportCore : CommandElab := fun stx => withEnvTransaction do
  let `(command| #preo_report $n:ident) := stx | throwError "preo: malformed report"
  let ns ← getCurrNamespace
  let all := preoExt.getState (← getEnv)
  let want := ns ++ n.getId
  let rows := all.filter fun r => r.decl == want || r.decl == n.getId
  let rows := if rows.isEmpty then all.filter (fun r => n.getId.isSuffixOf r.decl) else rows
  if rows.isEmpty then
    let known := (all.map (·.decl)).toList.eraseDups
    throwErrorAt n "#preo_report: no `preo` declaration named `{n.getId}`. \
      Known: {known}"
  let decl := rows[0]!.decl
  let mut out := s!"preo {decl}\n  state    {decl}.State  \
    (MergeState by inferInstance — checked by an emitted `example`)\n"
  out := out ++ "\n  FIELD                 KIND                  CARRIER\n"
  for r in rows do
    if r.kind == .field then
      out := out ++ s!"  {pad r.name 20}  {pad r.detail 20}  {r.detail₂}\n"
  if rows.any (fun r => r.kind == .invariant || r.kind == .cross) then
    out := out ++ "\n  INVARIANT             READS            GLOBAL      SEAM        ROUTES\n"
    for r in rows do
      if r.kind == .invariant || r.kind == .cross then
        let global ←
          match ← readAnswer r.evidence with
          | some (some true) => pure "FREE"
          | some (some false) => pure "ESCALATES"
          | some none => pure "UNRESOLVED"
          | none => pure "?? (the classification did not reduce — report this)"
        let seam := if r.seamCite.isEmpty then "—" else "FREE·seg"
        let tag := if r.kind == .cross then " [cross]" else ""
        out := out ++
          s!"  {pad (r.name ++ tag) 20}  {pad r.detail 15}  {pad global 10}  \
{pad seam 10}  {r.detail₂}\n"
        out := out ++ s!"      ↳ {r.cite}\n"
        unless r.seamCite.isEmpty do
          out := out ++ s!"      ↳ SEAM: {r.seamCite}\n"
  if rows.any (fun r => r.kind == .typedDerive) then
    out := out ++ "\n  TYPED DERIVE          SCHEMA                RAW PROGRAM\n"
    for r in rows do
      if r.kind == .typedDerive then
        out := out ++ s!"  {pad r.name 20}  {pad r.detail 20}  {r.detail₂}\n"
        out := out ++ s!"      ↳ {r.cite}\n"
  if rows.any (fun r => r.kind == .derive) then
    out := out ++ "\n  DERIVE                READS       MERGEABILITY    ROUTE\n"
    for r in rows do
      if r.kind == .derive then
        let m ←
          match ← readMergeAnswer r.evidence with
          | some (some s) => pure s
          | some none => pure "UNRESOLVED"
          | none => pure "?? (the classification did not reduce — report this)"
        out := out ++
          s!"  {pad r.name 20}  {pad r.detail 10}  {pad m 14}  {r.detail₂}\n"
        out := out ++ s!"      ↳ {r.cite}\n"
  if rows.any (fun r => r.kind == .future) then
    out := out ++ "\n  FUTURE                WORLD MODEL           DECLARATION\n"
    for r in rows do
      if r.kind == .future then
        out := out ++ s!"  {pad r.name 20}  {pad r.detail 20}  {r.detail₂}\n"
        out := out ++ s!"      ↳ {r.cite}\n"
  if rows.any (fun r => r.kind == .protocol) then
    out := out ++ "\n  PROTOCOL              STRATEGY              TYPED TERM\n"
    for r in rows do
      if r.kind == .protocol then
        out := out ++ s!"  {pad r.name 20}  {pad r.detail 20}  {r.detail₂}\n"
        out := out ++ s!"      ↳ {r.cite}\n"
  if rows.any (fun r => r.kind == .session) then
    out := out ++ "\n  SESSION               PROTOCOL(S)           ELABORATION\n"
    for r in rows do
      if r.kind == .session then
        out := out ++ s!"  {pad r.name 20}  {pad r.detail 20}  {r.detail₂}\n"
        out := out ++ s!"      ↳ {r.cite}\n"
  if rows.any (fun r => r.kind == .invariant || r.kind == .cross ||
      r.kind == .derive || r.kind == .typedDerive) then
    out := out ++ "\n  Every VERDICT column above is REDUCED out of the row's `.classification`\n"
    out := out ++ "  constant at print time — `Classification.answer` and `.mergeAnswer`,\n"
    out := out ++ "  whose order-independence is `Preo.run_answer_congr`. No verdict is stored.\n"
    out := out ++ "  FREE rows are also stated at document scale as `<invariant>.onState`;\n"
    out := out ++ "  SEAM rows as `<invariant>.seamOnState` (`Preo.seamAlong` — the clash is\n"
    out := out ++ "  transported by PLANTING the field replicas in a document, which is what\n"
    out := out ++ "  fragment 1 said it could not synthesize).\n"
    if rows.any (fun r => r.kind == .typedDerive) then
      out := out ++ "  TYPED DERIVE rows expose `.Holes`, `.Reads`, `.MergeSafe?`,\n"
      out := out ++ "  `.MonotoneSafe?`, `.buildCache`, `.updateCache`, `.Result`, and\n"
      out := out ++ "  membership-gated `.reportAt`;\n"
      out := out ++ "  positive badges are\n"
      out := out ++ "  proof values, while `none` remains an honest non-answer.\n"
  if rows.any (fun r => r.kind == .future || r.kind == .protocol || r.kind == .session) then
    out := out ++ "\n  FUTURE/PROTOCOL/SESSION rows have no verdict column: they name typed\n"
    out := out ++ "  semantic artifacts, and their cited constructors carry the proofs.\n"
  logInfo out

end Uwueave.Preo.Elab.Report
