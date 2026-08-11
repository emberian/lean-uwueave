/-
# Uwueave.Audit — the trust gate, total.

One command, whole-tree coverage: `#audit_floor` walks **every constant in the
`Uwueave` namespace** — not a curated list — and fails the build if any of them
depends on an axiom outside Lean's own floor:

    propext · Classical.choice · Quot.sound

That floor is what "a Lean proof" already means; the gate exists for what it
EXCLUDES. `sorry` compiles to `sorryAx` (a plain `lake build` only *warns* on
sorry — without a gate, a hole in a proof ships green). `native_decide`
compiles to `Lean.ofReduceBool`/`ofReduceNat` (trusting the compiled
evaluator). Any future custom axiom lands the same way. All of them are hard
build failures here, for every theorem — including ones written five minutes
ago that no list was updated to mention.

## Why this replaced 113 per-theorem `#guard_msgs` pins (2026-08-10)

The previous design pinned each keystone's exact axiom list as a message
string. Honest accounting of what that bought and cost:

  * It DID make `sorry`/`native_decide` a build failure — but only for the
    113 pinned names, lagging the tree by construction (~226 theorems).
  * The per-name footprint strings were noise: whether a proof uses
    `Classical.choice` *within the floor* changes nothing anyone should
    decide by, and the exact-string format broke builds over formatting,
    never over trust.
  * Every lane spent effort ferrying verbatim footprints into the pin file,
    and counts advertised in prose rotted on schedule.

The total gate keeps the tripwire (stronger: total, zero-lag), deletes the
ritual, and drops the within-floor vanity distinctions. Per-theorem axiom
profiles remain one command away for anyone curious: `#print axioms <name>`.
The curated public surface lives in `docs/MAP.md`'s keystone ledger — a
*reading* aid, no longer a trust mechanism.

The gate also carries a vacuity tripwire: if the namespace walk ever audits
suspiciously few constants (an import breaks, a rename empties the filter),
it fails rather than passing on nothing. A gate that cannot go red is not a
gate.

## What this gate does NOT prove — `docs/TRUST.md`

`#audit_floor` establishes **logical hygiene, not semantic adequacy** (the
distinction is codex's, from an external review of this repo). A green gate
says every constant in the namespace was built from `propext`,
`Classical.choice` and `Quot.sound` and nothing else. It says nothing about
whether a theorem's statement corresponds to the protocol we meant; whether a
model is missing an operation or a failure mode; whether the states a theorem
quantifies over are reachable through the shipping API; whether the serialized
bytes implement the abstract state that was proved about; or whether any
docstring — including this one — accurately describes what it sits above. Those
are read by humans and other models, not by the elaborator, and the gate is
blind to all of them by construction. This file is also *not itself a theorem*:
it is an unverified metaprogram auditing the tree from inside the tree.
`docs/TRUST.md` carries the full accounting as three separate ledgers —
logical TCB, execution TCB, environment/model premises — each row classified as
an irreducible premise or a transmutable obligation with a named next step.
-/
import Lean
import Uwueave.Choreo
import Uwueave.Weave
import Uwueave.ORSet
import Uwueave.Causality
import Uwueave.MVRegister
import Uwueave.Segmented
import Uwueave.Undo
import Uwueave.Delta
import Uwueave.Sequence
import Uwueave.ORMap
import Uwueave.Automata
import Uwueave.Authority
import Uwueave.ExecRefine
import Uwueave.Ceiling
import Uwueave.Seams
import Uwueave.Necessity
import Uwueave.CausalReach
import Uwueave.Liveness
import Uwueave.Traces
import Uwueave.Nary
import Uwueave.KernelCFCS
import Uwueave.SeqKernel
import Uwueave.Era
import Uwueave.EraKernel
import Uwueave.Gated
import Uwueave.Fugue
import Uwueave.WeaveState
import Uwueave.GatedEra
import Uwueave.Ancestral
import Uwueave.RALin
import Uwueave.SeamAlgebra
import Uwueave.Gluing
import Uwueave.Holes
import Uwueave.Cost
import Uwueave.JoinHom
import Uwueave.Evidence
import Uwueave.Wellformed
import Uwueave.Exits
import Uwueave.CoordEffect
import Uwueave.SeamColoring
import Uwueave.Budget
import Uwueave.WorldFuture
import Uwueave.MinimalSummary
import Uwueave.Repair
import Uwueave.MergeModel
import Uwueave.ResultStatus
import Uwueave.Recoverable
import Uwueave.HonestRender
import Uwueave.Histories
import Uwueave.HistoryBase
import Uwueave.RenderSix
import Uwueave.Bounds
import Uwueave.MenuTotality
import Uwueave.Preo.Demo
import Uwueave.Tactics

open Lean Elab Command in
/-- Fail the build unless every constant in the `Uwueave` namespace stays
within the axiom floor `{propext, Classical.choice, Quot.sound}`. Offenders
are named (first 20) in the error. This is logical hygiene, not semantic
adequacy: see the header and `docs/TRUST.md` for what a green gate does not
say. -/
elab "#audit_floor" : command => do
  let env ← getEnv
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let targets := env.constants.toList.filterMap fun (n, _) =>
    if (`Uwueave).isPrefixOf n then some n else none
  let mut blamed : Array String := #[]
  for n in targets do
    let axs ← collectAxioms n
    for ax in axs do
      unless allowed.contains ax do
        if blamed.size < 20 then
          blamed := blamed.push s!"{n} ← {ax}"
  unless blamed.isEmpty do
    throwError "audit floor violated — first offenders: {blamed.toList}"
  if targets.length < 300 then
    throwError "audit vacuity tripwire: only {targets.length} constants in the Uwueave namespace — the walk is not seeing the tree"
  logInfo m!"#audit_floor: {targets.length} constants audited, all within the floor"

open Lean Elab Command in
/-- Fail the build if any module the ROOT (`Uwueave.lean`) imports is absent
from this file's environment — i.e. if the gate's walk does not cover the
library. `#audit_floor` can only see constants from modules it has imported, so
a module in the root and not here is silently unaudited. The root cannot be
imported (it imports this file), so coverage is *checked against the file on
disk* rather than inherited. Found by `docs/COHERENCE.md`: `Choreo` sat in the
root and outside the gate for a full wave, beneath four "total by construction"
claims, and a hand-maintained import list reproduces that gap once per wave. -/
elab "#gate_covers_root" : command => do
  let env ← getEnv
  let root ← IO.FS.readFile "Uwueave.lean"
  let wanted := root.splitOn "\n" |>.filterMap fun l =>
    if l.startsWith "import Uwueave" && l != "import Uwueave.Audit" then
      some (l.drop "import ".length).toString
    else none
  let loaded := env.header.moduleNames.toList.map toString
  let missing := wanted.filter fun m => !(loaded.contains m)
  unless missing.isEmpty do
    throwError "gate coverage hole: the root imports {missing} which this file does not \
      reach, so #audit_floor cannot see their constants. Add the import(s) here."
  if wanted.length < 20 then
    throwError "gate-coverage tripwire: parsed only {wanted.length} root imports — the parse is broken"
  logInfo m!"#gate_covers_root: {wanted.length} root modules, all reached by the gate"

#gate_covers_root

#audit_floor
