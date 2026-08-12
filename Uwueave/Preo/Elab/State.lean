/-
# Uwueave.Preo.Elab.State -- field normalization and document-state emission
-/
import Uwueave.Preo.Elab.Internal

namespace Uwueave.Preo.Elab.State

open Lean Elab Command Term
open Uwueave.Preo.Elab.Internal

/-- The normalized field/state data consumed by all later declaration phases.

Every field-indexed array has exactly `size` entries and shares one indexing
scheme: source declaration order. -/
structure Context where
  declName : Name
  ns : Name
  fullDecl : Name
  stateId : Ident
  fieldIdents : Array Ident
  fieldNames : Array Name
  fieldKinds : Array String
  fieldKeys : Array (Option Term)
  carriers : Array Term
  defaults : Array Term
  deriving Inhabited

def Context.size (ctx : Context) : Nat := ctx.carriers.size

private structure ParsedField where
  name : Ident
  key? : Option Term
  baseCarrier : Term
  baseDefault : Term
  kindLabel : String
  custom : Bool
  deriving Inhabited

private def carrierOf (kind : Ident) (argument? : Option Term) : CommandElabM Term := do
  let spelling := kind.getId.toString
  match spelling, argument? with
  | "GrowSet", some argument => `(Uwueave.Catalog.GSet $argument)
  | "Slot", some argument => `(Uwueave.Preo.Slot $argument)
  | "Escrow", some argument => `(Uwueave.Catalog.Escrow $argument)
  | "Quota", some argument => `(Uwueave.Preo.Quota $argument)
  | "Counter", none => `(Nat)
  | "LWW", none => `(Uwueave.Catalog.LWW)
  | "GrowSet", none | "Slot", none | "Escrow", none | "Quota", none =>
      throwErrorAt kind "preo: field kind `{spelling}` needs an element type — write \
        `{spelling} Nat`, `{spelling} (Fin 3)`, … (the carrier is a map out of it, so the \
        elaborator cannot guess one)."
  | "Counter", some _ =>
      throwErrorAt kind "preo: `Counter` takes no argument — its carrier is \
        `Nat` under `max` (`Catalog.instMergeStateNatMax`). For a per-replica \
        counter use `Escrow ι`."
  | "LWW", some _ =>
      throwErrorAt kind "preo: `LWW` takes no argument — `Catalog.LWW` is a \
        concrete (timestamp, value) register. Put the key before the colon: \
        `field <name> per <Key> : LWW`."
  | _, _ =>
      throwErrorAt kind "preo: unknown built-in field kind `{spelling}`. Use one of six: \
        `GrowSet α` (grow-only set), `Slot α` (a grow-only set carrying a \
        uniqueness ceiling), `Escrow ι` (per-replica quota spend), `Quota ι` \
        (allocation PLUS spend — the carrier the seam lives on), `Counter` \
        (`Nat` under max), `LWW` (last-writer-wins register). Each supplies a \
        carrier and a proved `MergeState` from `Uwueave.Catalog` or \
        `Uwueave.Segmented`. For an application carrier write \
        `field <name> : (custom <Carrier>) := <seed>`; its `MergeState` must \
        already exist and its seed is never inferred."

private def defaultOf (kind : Ident) (argument? : Option Term) : CommandElabM Term := do
  let spelling := kind.getId.toString
  match spelling, argument? with
  | "GrowSet", some argument => `((fun _ => false : Uwueave.Catalog.GSet $argument))
  | "Slot", some argument => `((fun _ => false : Uwueave.Preo.Slot $argument))
  | "Escrow", some argument => `((fun _ => 0 : Uwueave.Catalog.Escrow $argument))
  | "Quota", some argument =>
      `((((fun _ => 0), (fun _ => 0)) : Uwueave.Preo.Quota $argument))
  | "Counter", _ => `((0 : Nat))
  | "LWW", _ => `((⟨0, 0⟩ : Uwueave.Catalog.LWW))
  | _, _ => throwErrorAt kind "preo: internal — no default for kind `{spelling}`"

/-- Parse fields, emit their carrier/state/accessor/plant declarations in the
historical order, and return the aligned context plus field report rows. -/
def emit (declId : Ident) (fields : Array Syntax) :
    CommandElabM (Context × Array Row) := do
  let declName := declId.getId
  let ns ← getCurrNamespace
  let fullDecl := ns ++ declName
  if fields.isEmpty then
    throwErrorAt declId "preo: `{declName}` declares no fields — a state type \
      with no fields has nothing to classify. Add `field <name> : <kind>`."

  let mut fieldIdents : Array Ident := #[]
  let mut fieldKinds : Array String := #[]
  let mut fieldKeys : Array (Option Term) := #[]
  let mut carriers : Array Term := #[]
  let mut defaults : Array Term := #[]
  let mut customFields : Array Bool := #[]
  for field in fields do
    let `(preoField| field $name:ident $[per $key:term]? : $body:preoFieldBody) := field
      | throwErrorAt field "preo: malformed field"
    let parsed : ParsedField ← match body with
      | `(preoFieldBody| (custom $carrierTy:term) := $seed:term) =>
          pure (⟨name, key, carrierTy, seed,
            "custom " ++ renderSyntax carrierTy, true⟩ : ParsedField)
      | `(preoFieldBody| $kind:ident $[$argument:term]?) =>
          pure (⟨name, key, ← carrierOf kind argument, ← defaultOf kind argument,
            renderSyntax kind ++
              (argument.map (fun term => " " ++ renderSyntax term)).getD "", false⟩ :
            ParsedField)
      | _ => throwErrorAt body "preo: malformed field body"
    if fieldIdents.any (·.getId == parsed.name.getId) then
      throwErrorAt parsed.name "preo: duplicate field `{parsed.name.getId}`"
    let carrier : Term ← match parsed.key? with
      | none => pure parsed.baseCarrier
      | some key => `($key → $(parsed.baseCarrier))
    let default : Term ← match parsed.key? with
      | none => pure parsed.baseDefault
      | some key => `(fun (_ : $key) => $(parsed.baseDefault))
    unless ← canSynth (← `(Uwueave.MergeState $carrier)) do
      throwErrorAt field "preo: field `{parsed.name.getId}` has carrier \
        `{renderSyntax carrier}`, but no `MergeState` instance is available. A custom \
        carrier reuses an application merge model; the seed supplies a planting \
        value, not a merge operation. Define and prove the instance before this \
        declaration."
    fieldIdents := fieldIdents.push parsed.name
    fieldKinds := fieldKinds.push
      ((parsed.key?.map (fun key => "per " ++ renderSyntax key ++ " : ")).getD "" ++
        parsed.kindLabel)
    fieldKeys := fieldKeys.push parsed.key?
    carriers := carriers.push carrier
    defaults := defaults.push default
    customFields := customFields.push parsed.custom

  let n := carriers.size
  let fieldNames := fieldIdents.map (·.getId)
  for i in [0:n] do
    let fieldName := fieldIdents[i]!.getId
    let carrierId := mkIdent (declName ++ (fieldName ++ `Carrier))
    emitRequired (← `(command|
      /-- The checked carrier of this field, named for manifests and adapters. -/
      abbrev $carrierId : Type := $(carriers[i]!)))
    if customFields[i]! then
      let seedId := mkIdent (declName ++ (fieldName ++ `seed))
      emitRequired (← `(command|
        /-- The author-supplied planting seed for this application carrier. -/
        def $seedId : $carrierId := $(defaults[i]!)))
      floorCheck fieldIdents[i]! "custom field seed"
        (fullDecl ++ (fieldName ++ `seed))
      defaults := defaults.set! i seedId
      let mergeId := mkIdent (declName ++ (fieldName ++ `mergeState))
      emitRequired (← `(command|
        /-- The application's existing merge model, checked and retained. -/
        abbrev $mergeId : Uwueave.MergeState $carrierId := inferInstance))
      floorCheck fieldIdents[i]! "custom field MergeState"
        (fullDecl ++ (fieldName ++ `mergeState))

  let mut stateType : Term := carriers[n - 1]!
  for i in [0:n-1] do
    stateType ← `($(carriers[n - 2 - i]!) × $stateType)
  let stateId := mkIdent (declName ++ `State)
  emitRequired (← `(command|
    /-- The declared state: the field carriers, right-nested. Its `MergeState`
    is inherited from the product and pointwise instances. -/
    abbrev $stateId : Type := $stateType))

  for i in [0:n] do
    let fieldName := fieldIdents[i]!.getId
    let accessorId := mkIdent (declName ++ fieldName)
    let body ← projPath i n
    emitRequired (← `(command|
      abbrev $accessorId (s : $stateId) : $(carriers[i]!) := $body))
    let homId := mkIdent (declName ++ (fieldName ++ `merge_hom))
    emitRequired (← `(command|
      theorem $homId (x y : $stateId) :
          $accessorId (Uwueave.MergeState.merge x y) =
            Uwueave.MergeState.merge ($accessorId x) ($accessorId y) := rfl))
    let plantId := mkIdent (declName ++ (fieldName ++ `plant))
    let plant ← plantFn i n defaults
    emitRequired (← `(command|
      /-- A document holding the given field value and planting seeds elsewhere. -/
      def $plantId : $(carriers[i]!) → $stateId := $plant))
    emitRequired (← `(command|
      theorem $(mkIdent (declName ++ (fieldName ++ `plant_proj)))
          (a : $(carriers[i]!)) : $accessorId ($plantId a) = a := rfl))
    emitRequired (← `(command|
      theorem $(mkIdent (declName ++ (fieldName ++ `plant_merge)))
          (a b : $(carriers[i]!)) :
          $accessorId (Uwueave.MergeState.merge ($plantId a) ($plantId b)) =
            Uwueave.MergeState.merge a b := rfl))
    emitRequired (← `(command|
      theorem $(mkIdent (declName ++ (fieldName ++ `surj))) :
          ∀ a : $(carriers[i]!), ∃ s : $stateId, $accessorId s = a :=
        fun a => ⟨$plantId a, rfl⟩))
  emitRequired (← `(command| example : Uwueave.MergeState $stateId := inferInstance))

  let ctx : Context := {
    declName, ns, fullDecl, stateId, fieldIdents, fieldNames, fieldKinds,
    fieldKeys, carriers, defaults }
  let mut rows : Array Row := #[]
  for i in [0:n] do
    rows := rows.push {
      decl := fullDecl, kind := .field, name := fieldIdents[i]!.getId.toString
      detail := fieldKinds[i]!, detail₂ := renderSyntax carriers[i]!
      evidence := fullDecl ++ (fieldIdents[i]!.getId ++ `merge_hom)
      isObligation := false, cite := "MergeState by inferInstance (checked)"
      seamCite := "" }
  return (ctx, rows)

end Uwueave.Preo.Elab.State
