/-
# Uwueave.TrustFloor — one axiom policy, reusable at every proof-producing edge.

The repository's logical floor is intentionally tiny and intentionally defined
once.  `Uwueave.Audit` applies it to the whole public namespace, while the
Preoscript elaborator applies the same `offFloor` function before publishing a
generated facet.  Downstream projects can run `#audit_floor_prefix Their.Name`
after importing this module; a missing prefix is a hard failure rather than a
vacuous green check.

This remains a metaprogrammed gate, not a theorem of Lean's metatheory.  Its
success means only that the selected constants depend on Lean's ordinary
classical/quotient floor and on no additional axioms.
-/
import Lean

namespace Uwueave.TrustFloor

open Lean

/-- The complete allowed axiom floor.  Keep policy here rather than copying it
into auditors or elaborators. -/
def allowedAxioms : List Name :=
  [``propext, ``Classical.choice, ``Quot.sound]

/-- The axioms used by `c` which are not in `allowedAxioms`.

The weak monadic interface is deliberate: both command elaborators and other
environment readers can call this exact implementation. -/
def offFloor {m : Type → Type} [Monad m] [MonadEnv m]
    (c : Name) : m (Array Name) := do
  let axioms ← collectAxioms c
  return axioms.filter fun ax => !(allowedAxioms.contains ax)

/-- All constants currently visible below a namespace prefix. -/
def constantsUnder (env : Environment) (ns : Name) : List Name :=
  env.constants.toList.filterMap fun (name, _) =>
    if ns.isPrefixOf name then some name else none

/-- At most `limit` offending dependency edges below `prefix`, for a bounded
and useful diagnostic even if a bad axiom has spread widely. -/
def firstViolations {m : Type → Type} [Monad m] [MonadEnv m]
    (ns : Name) (limit : Nat := 20) : m (List Name × Array String) := do
  let targets := constantsUnder (← getEnv) ns
  let mut blamed : Array String := #[]
  for name in targets do
    for ax in (← offFloor name) do
      if blamed.size < limit then
        blamed := blamed.push s!"{name} ← {ax}"
  return (targets, blamed)

/-- Parse a Lean source header with Lean's own header parser and return its
direct imports.  Whitespace, comments, `public`/`meta` modifiers, and future
header syntax therefore cannot drift from a handwritten line scanner. -/
def directImports (path : System.FilePath) : IO (Array Import) := do
  let input ← IO.FS.readFile path
  let (imports, _, messages) ← Lean.Elab.parseImports input (some path.toString)
  if messages.hasErrors then
    throw <| IO.userError s!"Lean rejected the module header in {path}"
  return imports

end Uwueave.TrustFloor

namespace Uwueave.TrustFloor.Commands

open Lean Elab Command

private def auditPrefix (ns : Name) (minimum : Nat) (legacy : Bool) : CommandElabM Unit := do
  let (targets, blamed) ← Uwueave.TrustFloor.firstViolations ns
  unless blamed.isEmpty do
    if legacy then
      throwError "audit floor violated — first offenders: {blamed.toList}"
    else
      throwError "audit floor violated below `{ns}` — first offenders: {blamed.toList}"
  if targets.length < minimum then
    if legacy then
      throwError "audit vacuity tripwire: only {targets.length} constants in the Uwueave namespace — the walk is not seeing the tree"
    else
      throwError "audit vacuity tripwire: only {targets.length} constants below `{ns}`; expected at least {minimum}"
  if legacy then
    logInfo m!"#audit_floor: {targets.length} constants audited, all within the floor"
  else
    logInfo m!"#audit_floor_prefix {ns}: {targets.length} constants audited, all within the floor"

/-- Audit a downstream namespace with the same exact policy as Uwueave.  The
prefix must already contain at least one constant, preventing typo-vacuity. -/
syntax "#audit_floor_prefix " ident : command

elab_rules : command
  | `(command| #audit_floor_prefix $ns:ident) =>
      auditPrefix ns.getId 1 false

/-- The repository-wide compatibility command.  Its 300-constant vacuity
threshold and diagnostics are preserved from `Uwueave.Audit`. -/
elab "#audit_floor" : command =>
  auditPrefix `Uwueave 300 true

end Uwueave.TrustFloor.Commands
