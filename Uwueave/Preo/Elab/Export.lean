/-
# Uwueave.Preo.Elab.Export — checked export-manifest elaboration

This module owns the complete `preo_export` expansion, but deliberately does
not register a command elaborator.  `Uwueave.Preo.Elab` remains the single
registration point and delegates to `elabPreoExportCore`, so importing this
leaf cannot install a second handler for the same syntax kind.

The expansion is one-way and validation-first.  Manifest rows extend one
heterogeneous `Export.DeclarationBundle` term in source order; proof indices
are erased only after that fold.  The generated durable bytes and V2 projection
are first-order data, and Rust source is emitted only through the private
validated boundary.  All emitted names and types are compatibility-sensitive:
downstream users rely on the exact `E.*` surface assembled by `Names.ofSurface`.

Failures remain atomic at the enclosing command boundary.  In particular, a
bad row, a composed profile posing as an ordinary protocol elaboration, an
exact-plan mismatch, a V2 validation refusal, or a trust-floor violation must
leave none of the declarations below behind.
-/
import Uwueave.Preo.Elab.Internal
import Uwueave.Preo.Syntax
import Uwueave.Preo.Export
import Uwueave.Preo.ArtifactDurable
import Uwueave.Preo.ProjectionV2
import Uwueave.Protocol

namespace Uwueave.Preo.Elab.Export

open Lean Elab Command Term Meta

/-- The compatibility-sensitive generated declaration names for one export.
Keeping their construction in one value makes additions auditable and prevents
one stage from silently drifting to a differently suffixed constant. -/
structure Names where
  state : Ident
  declaration : Ident
  bundle : Ident
  artifact : Ident
  projection : Ident
  encoding : Ident
  durableFormat : Ident
  durableBytes : Ident
  projectionV2 : Ident
  validationConfig : Ident
  validation : Ident
  validationOk : Ident
  validated : Ident
  rendered : Ident
  renderResult : Ident

/-- Construct exactly the historical `preo_export` name surface. -/
def Names.ofSurface (exportId declId : Ident) : Names :=
  let exportName := exportId.getId
  let declName := declId.getId
  {
    state := mkIdent (declName ++ `State)
    declaration := mkIdent (exportName ++ `Declaration)
    bundle := mkIdent (exportName ++ `Bundle)
    artifact := mkIdent (exportName ++ `Artifact)
    projection := mkIdent (exportName ++ `Projection)
    encoding := mkIdent (exportName ++ `Encoding)
    durableFormat := mkIdent (exportName ++ `ArtifactDurableFormat)
    durableBytes := mkIdent (exportName ++ `ArtifactDurableBytes)
    projectionV2 := mkIdent (exportName ++ `ProjectionV2)
    validationConfig := mkIdent (exportName ++ `ValidationConfig)
    validation := mkIdent (exportName ++ `Validation)
    validationOk := mkIdent (exportName ++ `validation_ok)
    validated := mkIdent (exportName ++ `Validated)
    rendered := mkIdent (exportName ++ `Rendered)
    renderResult := mkIdent (exportName ++ `RenderResult)
  }

/- The pure name constructor is easy to pin locally and catches accidental
suffix drift without registering or executing an export command. -/
private example :
    (Names.ofSurface (mkIdent `E) (mkIdent `D)).state.getId = `D.State := rfl

private example :
    (Names.ofSurface (mkIdent `E) (mkIdent `D)).durableBytes.getId =
      `E.ArtifactDurableBytes := rfl

private example :
    (Names.ofSurface (mkIdent `E) (mkIdent `D)).validationOk.getId =
      `E.validation_ok := rfl

private example :
    (Names.ofSurface (mkIdent `E) (mkIdent `D)).renderResult.getId =
      `E.RenderResult := rfl

/-- Extend the proof-indexed bundle once for each manifest row, in written
order.  Every branch reconstructs the same checked builder application as the
original monolithic elaborator. -/
private def foldManifest (declName : Name) (initial : Term)
    (items : Array (TSyntax `preoExportItem)) : CommandElabM Term := do
  let mut bundle := initial
  for item in items do
    if item.raw.getKind == ``preoExportField then
      let `(preoExportItem| | field $fieldId:ident := {
          id := $id, kind := $kindId, carrier := $carrierId, key := $keyId }) := item
        | throwErrorAt item "preo_export: malformed field row"
      let carrierName := mkIdent (declName ++ (fieldId.getId ++ `Carrier))
      bundle ← `(Uwueave.Preo.Export.DeclarationBundle.addField
        (Carrier := $carrierName) $bundle ⟨$id⟩ $kindId $carrierId $keyId)
    else if item.raw.getKind == ``preoExportInvariant then
      let `(preoExportItem| | invariant $invId:ident := {
          id := $id, carrier := $carrierId, codec := $codec,
          answered := $answered }) := item
        | throwErrorAt item "preo_export: malformed invariant row"
      let classificationName :=
        mkIdent (declName ++ (invId.getId ++ `classification))
      bundle ← `(Uwueave.Preo.Export.DeclarationBundle.addClassification
        $bundle $classificationName $answered ⟨$id⟩ $carrierId $codec)
    else if item.raw.getKind == ``preoExportFuture then
      let `(preoExportItem| | future $futureId:ident := {
          certificate := $certificate:ident, id := $id,
          world := $worldId, relation := $relationId }) := item
        | throwErrorAt item "preo_export: malformed future row"
      let futureName := mkIdent (declName ++ futureId.getId)
      bundle ← `(Uwueave.Preo.Export.DeclarationBundle.addCertifiedFuture
        $bundle $futureName $certificate ⟨$id⟩ $worldId $relationId)
    else if item.raw.getKind == ``preoExportSession then
      let `(preoExportItem| | session $sessionId:ident := {
          id := $id, plan := $planId }) := item
        | throwErrorAt item "preo_export: malformed session row"
      let sessionName := mkIdent (declName ++ sessionId.getId)
      unless ← Uwueave.Preo.Elab.Internal.isProtocolElaborationTerm sessionName do
        throwErrorAt sessionId "preo_export: session `{sessionId.getId}` must be a \
          generated `Protocol.Elaboration`. Composed `ProfilePlan` values are \
          refused in V2: `DeclarationBundle` has no checked builder that can \
          project one as a single session/plan pair."
      bundle ← `(Uwueave.Preo.Export.DeclarationBundle.addElaboration
        $bundle $sessionName ⟨$id⟩ ⟨$planId⟩)
    else if item.raw.getKind == ``preoExportBudget then
      let `(preoExportItem| | budget $budget:ident for $sessionId:ident := {
          id := $budgetId, session := $stableSessionId,
          plan := $stablePlanId, samePlan := $samePlan }) := item
        | throwErrorAt item "preo_export: malformed budget row"
      let sessionName := mkIdent (declName ++ sessionId.getId)
      unless ← Uwueave.Preo.Elab.Internal.isProtocolElaborationTerm sessionName do
        throwErrorAt sessionId "preo_export: budget `{budget.getId}` must be tied \
          to a generated `Protocol.Elaboration`; composed `ProfilePlan` values \
          have no exact plan-indexed budget builder in V2."
      bundle ← `(Uwueave.Preo.Export.DeclarationBundle.addElaborationWithBudget
        $bundle $sessionName ⟨$stableSessionId⟩ ⟨$stablePlanId⟩
          ⟨$budgetId⟩ $budget $samePlan)
    else
      throwErrorAt item "preo_export: unknown manifest row"
  return bundle

/-- Emit the checked bundle, first-order projections, durable bytes, fail-closed
V2 validation boundary, and deterministic Rust source.  Declaration order is
part of the compatibility contract: later definitions refer only backward. -/
private def emitOutputs (names : Names) (config bundle : Term) : CommandElabM Unit := do
  Uwueave.Preo.Elab.Internal.emitRequired (← `(command|
    /-- The one proof-indexed builder chain, in manifest row order. -/
    noncomputable def $(names.bundle) :
        Uwueave.Preo.Export.DeclarationBundle $(names.state) := $bundle))
  Uwueave.Preo.Elab.Internal.emitRequired (← `(command|
    /-- The checked bundle with all proof indices eliminated to neutral data. -/
    noncomputable def $(names.artifact) : Uwueave.Preo.Artifact.Artifact :=
      Uwueave.Preo.Export.DeclarationBundle.toArtifact $(names.bundle)))
  Uwueave.Preo.Elab.Internal.emitRequired (← `(command|
    /-- Artifact paired with its uniquely canonical first-order encoding. -/
    noncomputable def $(names.projection) :
        Uwueave.Preo.Export.DeclarationBundle.Projection :=
      Uwueave.Preo.Export.DeclarationBundle.project $(names.bundle)))
  Uwueave.Preo.Elab.Internal.emitRequired (← `(command|
    /-- The canonical first-order encoding selected by the checked projection. -/
    noncomputable def $(names.encoding) : Uwueave.Preo.Artifact.ArtifactEncoding :=
      ($(names.projection)).encoding))
  Uwueave.Preo.Elab.Internal.emitRequired (← `(command|
    /-- The explicit durable format tag for this generated byte sequence. -/
    def $(names.durableFormat) : Uwueave.Durable.FormatTag :=
      Uwueave.Preo.ArtifactDurable.artifactFormat))
  Uwueave.Preo.Elab.Internal.emitRequired (← `(command|
    /-- Canonical, versioned bytes of the neutral encoding; no runtime FFI. -/
    noncomputable def $(names.durableBytes) : Uwueave.Preo.ArtifactDurable.Bytes :=
      Uwueave.Preo.ArtifactDurable.projectionBytes $(names.encoding)))
  Uwueave.Preo.Elab.Internal.emitRequired (← `(command|
    /-- The raw V2 input, still requiring fail-closed validation. -/
    noncomputable def $(names.projectionV2) : Uwueave.Preo.ProjectionV2.Projection :=
      Uwueave.Preo.ProjectionV2.Projection.ofEncoding $(names.encoding)))
  Uwueave.Preo.Elab.Internal.emitRequired (← `(command|
    /-- The application's explicit finite validation policy. -/
    def $(names.validationConfig) : Uwueave.Preo.ProjectionV2.ValidationConfig :=
      $config))
  Uwueave.Preo.Elab.Internal.emitRequired (← `(command|
    /-- Validation result before private-boundary extraction. -/
    noncomputable def $(names.validation) :
        Uwueave.Preo.ProjectionV2.ValidationResult
          Uwueave.Preo.ProjectionV2.ValidatedProjectionV2 :=
      Uwueave.Preo.ProjectionV2.validate $(names.validationConfig)
        $(names.projectionV2)))
  Uwueave.Preo.Elab.Internal.emitRequired (← `(command|
    /-- Compile-time validation gate. Literal duplicate stable IDs, invalid
    references, noncanonical profiles and bounds violations cannot pass it. -/
    theorem $(names.validationOk) : ($(names.validation)).isOk = true := by decide))
  Uwueave.Preo.Elab.Internal.emitRequired (← `(command|
    /-- The private validated boundary, obtained only from successful
    `ProjectionV2.validate`; the error branch contradicts `validation_ok`. -/
    noncomputable def $(names.validated) :
        Uwueave.Preo.ProjectionV2.ValidatedProjectionV2 :=
      match h : $(names.validation) with
      | .ok value => value
      | .error _ => False.elim (by
          have accepted := $(names.validationOk)
          rw [h] at accepted
          cases accepted)))
  Uwueave.Preo.Elab.Internal.emitRequired (← `(command|
    /-- Deterministic data-only source rendered from the validated boundary. -/
    noncomputable def $(names.rendered) : String :=
      Uwueave.Preo.ProjectionV2.renderRustSource $(names.validated)))
  Uwueave.Preo.Elab.Internal.emitRequired (← `(command|
    /-- The public validation-first render route, retained for direct equality
    checks against the separately named validated output. -/
    noncomputable def $(names.renderResult) :
        Uwueave.Preo.ProjectionV2.ValidationResult String :=
      Uwueave.Preo.ProjectionV2.validateAndRender $(names.validationConfig)
        $(names.projectionV2)))

/-- Implementation of the export expansion. The public core below supplies the
whole-environment transaction around this sequence of required commands. -/
private def elabPreoExportCoreImpl : CommandElab := fun stx => do
  let `(command| preo_export $exportId from $declId : $config :=
    declaration := {
      id := $declarationId, stateType := $stateTypeId,
      schema := $schemaVersion }
    $items:preoExportItem*) := stx
    | throwError "preo_export: malformed manifest"
  let names := Names.ofSurface exportId declId
  let declName := declId.getId

  Uwueave.Preo.Elab.Internal.emitRequired (← `(command|
    /-- The declaration row, indexed by the actual elaborated state type. -/
    def $(names.declaration) :
        Uwueave.Preo.Artifact.CheckedDeclaration $(names.state) :=
      Uwueave.Preo.Artifact.CheckedDeclaration.ofState
        ⟨$declarationId⟩ $stateTypeId $schemaVersion))

  let initial : Term ←
    `(Uwueave.Preo.Export.DeclarationBundle.ofDeclaration $(names.declaration))
  let bundle ← foldManifest declName initial items
  emitOutputs names config bundle

  let ns ← getCurrNamespace
  Uwueave.Preo.Elab.Internal.floorCheck exportId "export bundle"
    (ns ++ names.bundle.getId)
  Uwueave.Preo.Elab.Internal.floorCheck exportId "validated export"
    (ns ++ names.validated.getId)

/-- The non-registered `preo_export` core.  The registered command elaborator
in `Uwueave.Preo.Elab` delegates here, preserving one syntax handler and wrapping
the complete declaration sequence in an environment/message transaction. -/
def elabPreoExportCore : CommandElab := fun stx =>
  Uwueave.Preo.Elab.Internal.withEnvTransaction
    (elabPreoExportCoreImpl stx)

end Uwueave.Preo.Elab.Export
