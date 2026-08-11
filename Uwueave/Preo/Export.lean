/-
# Uwueave.Preo.Export — checked declarations to one neutral artifact

`Preo.Artifact` defines the first-order transport types and the individual
checked projections.  This module supplies the missing declaration-level seam:
one proof-indexed builder consumes checked language meanings and emits exactly
one `Artifact.Artifact` plus its canonical structural `ArtifactEncoding`. That
encoding is first-order data, not a byte serialization; `Preo.ArtifactDurable`
provides the canonical byte projection and logical torn-tail layer.

The builder accepts six kinds of source:

* a `CheckedDeclaration` and typed fields;
* `Spec.Verdict` terms together with an explicit witness codec;
* answered `Preo.Classification` values, whose checked verdict is eliminated
  immediately together with the same explicit codec;
* a `Preo.Future.FutureDecl` together with a checked certificate at an exact
  world index;
* a `Protocol.Elaboration`, whose checked session and plan are projected
  together; and
* stable declaration, field, invariant, future, session, plan, type, kind and
  relation IDs supplied by the caller.

No ID is derived from a Lean or source name.  No report string, Boolean verdict
or host-authored verdict tag enters a checked constructor.  Certificates,
verdict proofs, relations and protocol terms are deliberately erased at the
neutral boundary only after their types have constrained construction.

The direction is one-way.  `ArtifactEncoding.decode` returns an
`Artifact.Artifact`; it does not return a `DeclarationBundle`,
`Spec.Verdict`, `Future.CheckedCertificate`, or `Scheduling.Plan`.  This is an
API-shape claim, not a theorem that *no arbitrary Lean function* from wire data
to a proposition could ever be written: for an already-provable invariant a
constant function could ignore its input.  What is enforced here is that this
module exposes no decoded-artifact-to-proof constructor, and the private bundle
constructor cannot be reached through decoding.  Section 5 makes the positive,
expressible statement: arbitrary wire verdict tags decode only to first-order
`VerdictEvidence`, without any semantic invariant index.
-/
import Uwueave.Preo.Artifact
import Uwueave.Preo.Future
import Uwueave.Protocol

namespace Uwueave.Preo.Export

open Uwueave

set_option autoImplicit false

universe u

/-! ## §1. The proof-indexed declaration builder -/

/-- A declaration bundle under construction.  Its constructor is private:
semantic rows enter through the checked builders below.  Heterogeneous Lean
carriers and proofs are eliminated one row at a time into the neutral lists,
while the declaration's state index remains on the bundle. -/
structure DeclarationBundle (State : Type u) where private mk ::
  declaration : Artifact.CheckedDeclaration State
  fields : List Artifact.FieldArtifact
  invariants : List Artifact.InvariantArtifact
  futures : List Artifact.FutureArtifact
  sessions : List Artifact.SessionArtifact
  plans : List Artifact.PlanArtifact

namespace DeclarationBundle

/-- Begin one export from an already checked state declaration. -/
def ofDeclaration {State : Type u}
    (declaration : Artifact.CheckedDeclaration State) :
    DeclarationBundle State :=
  ⟨declaration, [], [], [], [], []⟩

/-- Add a typed field.  Every stable identity and representation identity is
an explicit input; `none` versus `some keyTypeId` is never inferred from a
field name. -/
def addField {State : Type u} {Carrier : Type u}
    (bundle : DeclarationBundle State)
    (id : Artifact.FieldId) (kindId carrierTypeId : Nat)
    (keyTypeId : Option Nat := none) : DeclarationBundle State :=
  let checked : Artifact.CheckedField Carrier :=
    Artifact.CheckedField.ofCarrier bundle.declaration id kindId carrierTypeId keyTypeId
  ⟨bundle.declaration, bundle.fields ++ [checked.toArtifact],
    bundle.invariants, bundle.futures, bundle.sessions, bundle.plans⟩

/-- Add a checked global verdict.  The artifact's verdict tag is obtained only
by eliminating `verdict`; the caller supplies no tag.  The explicit codec is
used only if the verdict carries a clash witness. -/
def addVerdict {State S : Type u} [MergeState S]
    (bundle : DeclarationBundle State) {I : Invariant S}
    (id : Artifact.InvariantId) (carrierTypeId : Nat)
    (verdict : Spec.Verdict I) (codec : Artifact.FirstOrderCodec S) :
    DeclarationBundle State :=
  let checked : Artifact.CheckedInvariant I :=
    Artifact.CheckedInvariant.ofVerdict bundle.declaration id carrierTypeId verdict codec
  ⟨bundle.declaration, bundle.fields,
    bundle.invariants ++ [checked.toArtifact], bundle.futures,
    bundle.sessions, bundle.plans⟩

/-- Add an answered semantic classification. The answer equality is the
licence: `Classification.checkedVerdict` eliminates the classification
immediately to its global verdict, or—when no global facet exists—to the
clash carried by its seam. An unresolved classification supplies no such
equality and therefore has no call path.

Only the checked facets and the explicit witness codec cross this boundary.
Route names, citations, obligation text, seam readings, and report strings are
not inspected or exported. -/
def addClassification {State S : Type} [MergeState S]
    (bundle : DeclarationBundle State) {I : Invariant S}
    {R : Type} {f : S → R} (classification : Preo.Classification I f)
    {answer : Bool} (answered : classification.answer = some answer)
    (id : Artifact.InvariantId) (carrierTypeId : Nat)
    (codec : Artifact.FirstOrderCodec S) : DeclarationBundle State :=
  bundle.addVerdict id carrierTypeId (classification.checkedVerdict answered) codec

/-- Add a future only while holding a real world-indexed certificate for the
same `FutureDecl`.  `futureId`, `worldTypeId`, and `relationId` are manifest
inputs; the declaration's `String` name is neither hashed nor exported as
semantic authority. -/
def addCertifiedFuture {State : Type u}
    (bundle : DeclarationBundle State)
    {M : Future.WorldModel} (futureDecl : Future.FutureDecl M)
    {K R : Type} {answer : M.World → R} {key : M.World → K}
    {C : K → Prop} {index : Future.WorldIndex M}
    (_certificate : Future.CheckedCertificate futureDecl answer key C index)
    (futureId : Artifact.FutureId) (worldTypeId relationId : Nat) :
    DeclarationBundle State :=
  let checked : Artifact.CheckedFuture futureDecl.future :=
    Artifact.CheckedFuture.ofRelation bundle.declaration futureId worldTypeId relationId
  ⟨bundle.declaration, bundle.fields, bundle.invariants,
    bundle.futures ++ [checked.toArtifact], bundle.sessions, bundle.plans⟩

/-- Add the session and plan projected from one proof-carrying protocol
elaboration.  They cannot drift: the plan is indexed by `result.session`, and
both stable IDs are explicit. -/
def addElaboration {State : Type u}
    (bundle : DeclarationBundle State)
    {Strategy : Type} {term : Protocol.Term Strategy} {strategy : Strategy}
    (result : Protocol.Elaboration term strategy)
    (sessionId : Artifact.SessionId) (planId : Artifact.PlanId) :
    DeclarationBundle State :=
  let checkedSession : Artifact.CheckedSession result.session :=
    Artifact.CheckedSession.ofSession bundle.declaration sessionId
  let checkedPlan : Artifact.CheckedPlan checkedSession result.plan :=
    Artifact.CheckedPlan.ofPlan planId
  ⟨bundle.declaration, bundle.fields, bundle.invariants, bundle.futures,
    bundle.sessions ++ [checkedSession.toArtifact],
    bundle.plans ++ [checkedPlan.toArtifact]⟩

/-! ## §2. The unique first-order projection -/

/-- Eliminate the checked declaration index into one neutral artifact. -/
def toArtifact {State : Type u} (bundle : DeclarationBundle State) :
    Artifact.Artifact :=
  ⟨bundle.declaration.toArtifact, bundle.fields, bundle.invariants,
    bundle.futures, bundle.sessions, bundle.plans⟩

/-- The paired output of an export.  Its private constructor ensures the
encoding shipped beside an artifact is the canonical one. -/
structure Projection where private mk ::
  artifact : Artifact.Artifact
  encoding : Artifact.ArtifactEncoding
  canonical : encoding = artifact.canonicalEncoding

/-- Project exactly one artifact and its canonical encoding. -/
def project {State : Type u} (bundle : DeclarationBundle State) : Projection :=
  ⟨bundle.toArtifact, bundle.toArtifact.canonicalEncoding, rfl⟩

/-- Canonical transport roundtrips to the exact artifact emitted beside it. -/
@[simp] theorem Projection.decode_encoding (projection : Projection) :
    projection.encoding.decode = projection.artifact := by
  rw [projection.canonical]
  exact Artifact.ArtifactEncoding.decode_canonicalEncoding projection.artifact

end DeclarationBundle

/-! ## §3. A nonempty export from real language meanings -/

namespace Examples

open DeclarationBundle

/-- The example's stable manifest IDs are all literal inputs. -/
def declaration : Artifact.CheckedDeclaration Nat :=
  Artifact.CheckedDeclaration.ofState ⟨400⟩ 401 1

def natCodec : Artifact.FirstOrderCodec Nat where
  encode value := [value]
  decode
    | [value] => some value
    | _ => none
  decode_encode := by intro value; rfl

def nonnegative : Invariant Nat := fun state => state ≤ state

def nonnegativeVerdict : Spec.Verdict nonnegative :=
  .free (fun _ _ _ _ => Nat.le_refl _)

/-- A representative answered FREE classification. -/
def nonnegativeClassification : Preo.Classification nonnegative (fun _ => ()) where
  global := [nonnegativeVerdict]
  seams := []
  mergeability := []
  obligations := []

/-- Exporting the FREE classification is exactly direct checked-verdict export;
there is no intermediate Boolean verdict or report interpretation. -/
theorem addClassification_free_agrees_with_addVerdict :
    DeclarationBundle.addClassification
        (DeclarationBundle.ofDeclaration declaration) nonnegativeClassification rfl
        ⟨409⟩ 401 natCodec
      = DeclarationBundle.addVerdict
        (DeclarationBundle.ofDeclaration declaration) ⟨409⟩ 401
        nonnegativeVerdict natCodec :=
  rfl

/-- The identity seam for the artifact module's concrete Boolean-set clash.
It is deliberately constructed from semantic fields only; its display reading
below is not used by export. -/
def atMostOneBoolSeam :
    Spec.SegVerdict Artifact.Examples.atMostOneBool (Catalog.GSet Bool) where
  σ := id
  seamFree := by
    intro left right same hleft _
    change left = right at same
    subst right
    exact ⟨by simpa only [merge_idem] using hleft,
      by simp only [id_eq, merge_idem]⟩
  x := Artifact.Examples.leftBool
  y := Artifact.Examples.rightBool
  hx := by
    simp [Artifact.Examples.atMostOneBool, Artifact.Examples.leftBool]
  hy := by
    simp [Artifact.Examples.atMostOneBool, Artifact.Examples.rightBool]
  hbad := by
    intro merged
    exact merged rfl rfl

def atMostOneBoolSeamFacet : Preo.SeamFacet Artifact.Examples.atMostOneBool :=
  ⟨Catalog.GSet Bool, atMostOneBoolSeam, "display-only seam reading"⟩

/-- A representative classification answered by a seam alone. -/
def atMostOneBoolClassification :
    Preo.Classification Artifact.Examples.atMostOneBool (fun _ => ()) where
  global := []
  seams := [atMostOneBoolSeamFacet]
  mergeability := []
  obligations := []

/-- Seam export is exactly direct export of the seam's carried clash. The
facet's `reading` string is absent from both sides. -/
theorem addClassification_seam_agrees_with_addVerdict :
    DeclarationBundle.addClassification
        (DeclarationBundle.ofDeclaration declaration) atMostOneBoolClassification rfl
        ⟨410⟩ 402 Artifact.Examples.boolSetCodec
      = DeclarationBundle.addVerdict
        (DeclarationBundle.ofDeclaration declaration) ⟨410⟩ 402
        atMostOneBoolSeam.toClash Artifact.Examples.boolSetCodec :=
  rfl

/-- The unresolved representative has neither a global nor seam facet. -/
def unresolvedClassification : Preo.Classification nonnegative (fun _ => ()) :=
  Preo.Classification.empty

/-- **API boundary:** an unresolved classification cannot supply the equality
required by `addClassification`, hence cannot originate an invariant artifact
through that builder. -/
theorem unresolved_classification_has_no_export_licence :
    ¬ ∃ answer, unresolvedClassification.answer = some answer :=
  Preo.Classification.no_checkedVerdict_licence_of_answer_none
    unresolvedClassification rfl

/-- A real future declaration and proof-carrying certificate from
`Preo.Future`, not a relation tag authored for the artifact. -/
abbrev eraFuture : Future.FutureDecl Future.eraWorldModel := Future.EraDelivery

def eraCertificate :
    Future.CheckedCertificate eraFuture EraCertificate.finalView
      EraCertificate.eraKey EraCertificate.settledCert Future.eraPreIndex :=
  Future.eraSettledCertificate

/-- A real protocol AST elaboration.  Its two crossing-origin needs elaborate
to a checked session and identity plan. -/
def protocolResult :
    Protocol.Elaboration Protocol.coalescingProtocol () :=
  Protocol.elaborate Protocol.coalescingProtocol ()

/-- All five row classes are nonempty.  Stable IDs, type IDs, kind IDs,
relation IDs and the witness codec occur explicitly at their builder calls. -/
def bundle : DeclarationBundle Nat :=
  DeclarationBundle.addElaboration
    (DeclarationBundle.addCertifiedFuture
      (DeclarationBundle.addVerdict
        (DeclarationBundle.addField (Carrier := Nat)
          (DeclarationBundle.ofDeclaration declaration) ⟨402⟩ 10 401)
        ⟨403⟩ 401 nonnegativeVerdict natCodec)
      eraFuture eraCertificate ⟨404⟩ 405 406)
    protocolResult ⟨407⟩ ⟨408⟩

/-! ## §4. The corresponding hand composition -/

def checkedField : Artifact.CheckedField Nat :=
  Artifact.CheckedField.ofCarrier declaration ⟨402⟩ 10 401

def checkedInvariant : Artifact.CheckedInvariant nonnegative :=
  Artifact.CheckedInvariant.ofVerdict declaration ⟨403⟩ 401
    nonnegativeVerdict natCodec

def checkedFuture : Artifact.CheckedFuture eraFuture.future :=
  Artifact.CheckedFuture.ofRelation declaration ⟨404⟩ 405 406

def checkedSession : Artifact.CheckedSession protocolResult.session :=
  Artifact.CheckedSession.ofSession declaration ⟨407⟩

def checkedPlan : Artifact.CheckedPlan checkedSession protocolResult.plan :=
  Artifact.CheckedPlan.ofPlan ⟨408⟩

/-- The same output assembled by the primitive artifact combinators. -/
def handArtifact : Artifact.Artifact :=
  Artifact.Artifact.addPlan
    (Artifact.Artifact.addSession
      (Artifact.Artifact.addFuture
        (Artifact.Artifact.addInvariant
          (Artifact.Artifact.addField
            (Artifact.Artifact.ofDeclaration declaration) checkedField)
          checkedInvariant)
        checkedFuture)
      checkedSession)
    checkedPlan

/-- The whole builder projection is definitionally the corresponding hand
composition; no report parser or reconciliation pass intervenes. -/
theorem whole_artifact_is_hand_composition :
    bundle.toArtifact = handArtifact := rfl

/-- The paired encoding is definitionally the canonical encoding of that same
hand-composed artifact. -/
theorem whole_encoding_is_hand_composition :
    bundle.project.encoding = handArtifact.canonicalEncoding := rfl

/-- The nonempty whole artifact makes a structural roundtrip. -/
theorem whole_export_roundtrips :
    bundle.project.encoding.decode = handArtifact := by
  exact bundle.project.decode_encoding.trans whole_artifact_is_hand_composition

theorem every_export_surface_is_nonempty :
    bundle.toArtifact.fields.length = 1
      ∧ bundle.toArtifact.invariants.length = 1
      ∧ bundle.toArtifact.futures.length = 1
      ∧ bundle.toArtifact.sessions.length = 1
      ∧ bundle.toArtifact.plans.length = 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The protocol rows retain the real elaborated session and its plan rather
than equating crossings with meetings. -/
theorem protocol_export_is_nontrivial :
    bundle.toArtifact.sessions.map Artifact.SessionArtifact.crossings = [2]
      ∧ bundle.toArtifact.plans.map (fun plan => plan.actions.length) = [2] :=
  ⟨rfl, rfl⟩

end Examples

/-! ## §5. Decode stops at first-order data -/

/-- Extracting decoded verdicts has a first-order codomain with no invariant
parameter. -/
def decodedVerdicts (wire : Artifact.ArtifactEncoding) :
    List Artifact.VerdictEvidence :=
  wire.decode.invariants.map Artifact.InvariantArtifact.verdict

/-- Decoding preserves host-supplied wire tags as data.  It performs no check
and constructs no `Spec.Verdict`; the semantic predicate does not occur in
either side's type. -/
theorem decoded_verdicts_are_only_wire_data
    (wire : Artifact.ArtifactEncoding) :
    decodedVerdicts wire = wire.invariants.map (fun item => item.verdict) := by
  simp [decodedVerdicts, Artifact.ArtifactEncoding.decode,
    Artifact.InvariantArtifactEncoding.decode, Function.comp_def]

/-- An arbitrary host-authored `.free` tag therefore roundtrips merely as the
same first-order tag.  This is transport, not evidence that any invariant is
I-confluent. -/
def arbitraryFreeWire : Artifact.InvariantArtifactEncoding :=
  ⟨999, 998, 997, .free⟩

theorem arbitrary_free_tag_decodes_only_as_data :
    arbitraryFreeWire.decode.verdict = Artifact.VerdictEvidence.free := rfl

end Uwueave.Preo.Export
