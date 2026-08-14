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

/-- The source module which contributed an imported declaration.  Declarations
from the file currently being elaborated have no imported-module index yet. -/
def declarationModule? (env : Environment) (declaration : Name) : Option Name := do
  let index ← env.getModuleIdxFor? declaration
  env.header.moduleNames[index.toNat]?

/-- All constants owned by imported modules below `prefix`, regardless of the
namespace in which those constants were declared.  This closes the loophole in
a name-prefix-only walk: a root-namespace axiom in `Uwueave/Foo.lean` is still
owned by module `Uwueave.Foo`. -/
def constantsFromModulePrefix (env : Environment) (modulePrefix : Name) : List Name :=
  env.constants.toList.filterMap fun (name, _) =>
    match declarationModule? env name with
    | some moduleName => if modulePrefix.isPrefixOf moduleName then some name else none
    | none => none

/-- All constants owned by one exact imported module. -/
def constantsFromModule (env : Environment) (moduleName : Name) : List Name :=
  env.constants.toList.filterMap fun (name, _) =>
    if declarationModule? env name == some moduleName then some name else none

/-- Constants declared while elaborating the current source module.  Imported
constants have an entry in Lean's module ownership table; current declarations
do not receive one until the module is serialized and imported elsewhere. -/
def constantsFromCurrentModule (env : Environment) : List Name :=
  env.constants.toList.filterMap fun (name, _) =>
    if (declarationModule? env name).isNone then some name else none

/-- At most `limit` off-floor dependencies among an explicit target list. -/
def firstTargetViolations {m : Type → Type} [Monad m] [MonadEnv m]
    (targets : List Name) (limit : Nat := 20) : m (Array String) := do
  let mut blamed : Array String := #[]
  for name in targets do
    for ax in (← offFloor name) do
      if blamed.size < limit then
        blamed := blamed.push s!"{name} ← {ax}"
  return blamed

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

/-! ## Filesystem-to-module coverage -/

/-- Disk modules which are neither loaded nor explicitly exempted.  Kept pure
so subprocess canaries can prove that both missing modules and an incomplete
exception list make the gate go red. -/
def uncoveredModules (disk loaded exceptions : List Name) : List Name :=
  disk.filter fun moduleName =>
    !(loaded.contains moduleName) && !(exceptions.contains moduleName)

/-- Listed exceptions which do not name a real module on disk. -/
def absentExceptions (disk exceptions : List Name) : List Name :=
  exceptions.filter fun moduleName => !(disk.contains moduleName)

/-- The shared, gate-specific failure text for one disk/loaded/allowlist
comparison.  Both the real aggregate gate and subprocess canaries use this
function so a red canary cannot succeed merely on an unrelated tactic error. -/
def moduleCoverageFailure?
    (disk loaded exceptions : List Name) : Option String :=
  let absent := absentExceptions disk exceptions
  if !absent.isEmpty then
    some s!"disk-coverage exception(s) do not exist: {absent}"
  else
    let missing := uncoveredModules disk loaded exceptions
    if !missing.isEmpty then
      some s!"disk coverage hole: module(s) {missing} are neither loaded nor allowlisted"
    else
      none

private partial def leanSourcePathsUnder
    (directory : System.FilePath) : IO (Array System.FilePath) := do
  let rootMetadata ← directory.symlinkMetadata
  unless rootMetadata.type == .dir do
    throw <| IO.userError s!"trust coverage root is not a real directory: {directory}"
  let mut paths := #[]
  for entry in (← directory.readDir) do
    let path := entry.path
    let metadata ← path.symlinkMetadata
    match metadata.type with
    | .symlink =>
        throw <| IO.userError s!"trust coverage refuses symlinked source paths: {path}"
    | .dir =>
        paths := paths ++ (← leanSourcePathsUnder path)
    | .file =>
        if path.extension == some "lean" then
          paths := paths.push path
    | .other => pure ()
  return paths

def moduleNameOfLeanPath (path : System.FilePath) : IO Name := do
  unless path.extension == some "lean" do
    throw <| IO.userError s!"not a Lean source path: {path}"
  let components := path.withExtension "" |>.components
  if components.isEmpty || components.any fun component =>
      component.isEmpty || component == "." || component == ".." then
    throw <| IO.userError s!"invalid Lean module path: {path}"
  return components.foldl Name.mkStr .anonymous

/-- Enumerate every real `.lean` file below a relative source directory and
derive its module name from the path.  Duplicate module names and symlinks are
hard failures rather than silently collapsed coverage. -/
def leanModulesUnder (directory : System.FilePath) : IO (List Name) := do
  let paths ← leanSourcePathsUnder directory
  let mut modules := []
  for path in paths do
    let moduleName ← moduleNameOfLeanPath path
    if modules.contains moduleName then
      throw <| IO.userError s!"duplicate Lean module path for {moduleName}: {path}"
    modules := moduleName :: modules
  return modules

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

private def auditTargets (label : MessageData) (targets : List Name)
    (minimum : Nat := 1) : CommandElabM Unit := do
  let blamed ← Uwueave.TrustFloor.firstTargetViolations targets
  unless blamed.isEmpty do
    throwError "audit floor violated for {label} — first offenders: {blamed.toList}"
  if targets.length < minimum then
    throwError "audit vacuity tripwire for {label}: only {targets.length} owned constants; expected at least {minimum}"
  logInfo m!"audit floor for {label}: {targets.length} owned constants, all within the floor"

/-- Audit a downstream namespace with the same exact policy as Uwueave.  The
prefix must already contain at least one constant, preventing typo-vacuity. -/
syntax "#audit_floor_prefix " ident : command

elab_rules : command
  | `(command| #audit_floor_prefix $ns:ident) =>
      auditPrefix ns.getId 1 false

/-- Audit every constant owned by imported modules below a module prefix.  The
declaration's namespace is irrelevant; ownership comes from Lean's imported
module table. -/
syntax "#audit_floor_modules " ident : command

elab_rules : command
  | `(command| #audit_floor_modules $modulePrefix:ident) => do
      let env ← getEnv
      let minimum := if modulePrefix.getId == `Uwueave then 300 else 1
      auditTargets m!"modules below `{modulePrefix.getId}`"
        (Uwueave.TrustFloor.constantsFromModulePrefix env modulePrefix.getId)
        minimum

/-- Audit every constant owned by one exact imported module.  This is used for
executable `Main` modules which cannot coexist in the aggregate environment. -/
syntax "#audit_floor_module " ident : command

elab_rules : command
  | `(command| #audit_floor_module $moduleName:ident) => do
      let env ← getEnv
      auditTargets m!"module `{moduleName.getId}`"
        (Uwueave.TrustFloor.constantsFromModule env moduleName.getId)

/-- Audit declarations added by the source file currently being elaborated.
Unlike imported-module audits this deliberately permits zero declarations: the
top-level aggregate is an import-only module.  The command mechanically requires
effective EOF (comments and whitespace are permitted), so no later declaration
can sit outside its snapshot of the current environment. -/
elab "#audit_floor_current" : command => do
  let stx ← getRef
  let fileMap ← getFileMap
  let some trailingTail := stx.getTrailingTailPos? (canonicalOnly := true)
    | throwError "#audit_floor_current cannot verify its source position"
  unless trailingTail == fileMap.source.rawEndPos do
    throwError "#audit_floor_current must be the final command in its source file (only trailing whitespace/comments are permitted)"
  let env ← getEnv
  auditTargets m!"current module `{env.mainModule}`"
    (Uwueave.TrustFloor.constantsFromCurrentModule env) 0

/-- Require one declaration to be owned by the current module. -/
syntax "#assert_current_owns " ident : command

elab_rules : command
  | `(command| #assert_current_owns $declaration:ident) => do
      let env ← getEnv
      unless (Uwueave.TrustFloor.constantsFromCurrentModule env).contains declaration.getId do
        throwError "current module `{env.mainModule}` does not own required declaration `{declaration.getId}`"

/-- Require one declaration to be owned by one exact imported module. -/
syntax "#assert_module_owns " ident ident : command

elab_rules : command
  | `(command| #assert_module_owns $moduleName:ident $declaration:ident) => do
      let env ← getEnv
      unless (Uwueave.TrustFloor.constantsFromModule env moduleName.getId).contains declaration.getId do
        throwError "module `{moduleName.getId}` does not own required declaration `{declaration.getId}`"

/-- The repository-wide compatibility command.  Its 300-constant vacuity
threshold and diagnostics are preserved from `Uwueave.Audit`. -/
elab "#audit_floor" : command =>
  auditPrefix `Uwueave 300 true

end Uwueave.TrustFloor.Commands
