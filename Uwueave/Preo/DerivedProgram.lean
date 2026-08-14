/-
# Uwueave.Preo.DerivedProgram — typed derivations across the semantic stack.

`Preo.Expr` supplies an intrinsically typed expression, exact positional reads,
and proof-producing merge/monotonicity analyses.  This module connects that
syntax to the older semantic surfaces without teaching the elaborator a second
language:

* expression merge preservation is exactly `JoinHom` under the canonical
  `Ty`/`Env` merge structures;
* a `CertifiedMergeSafe` expression becomes a proof-carrying derived program;
* a world decoder that respects register positions turns its syntax-level
  holes into `Holes` locality, and `DerivedDocument.deriveDoc` then gives the
  exact attributed materialization;
* the existing conservative incremental evaluator is re-exposed with its
  correctness and zero-recomputation contracts;
* negative fixtures keep failure closed: ill-typed and raw custom syntax do not
  compile, and monotone-but-nonhomomorphic expressions are not promoted.

The two homomorphisms are intentionally distinct.  Direct expression results
commute with pointwise environment merge only with a `MergeSafe` proof.
Candidate-world documents commute with union for every deterministic evaluator,
because an image distributes over union; that fact does not retroactively make
the evaluator a homomorphism on environments.
-/
import Uwueave.DerivedDocument
import Uwueave.Preo.Incremental
import Uwueave.Specification

namespace Uwueave.Preo.DerivedProgram

open Uwueave.Catalog
open Expr

universe u

/-! ## Canonical merge instances and the semantic bridge -/

/-- The merge structure already proved by recursion in `Expr.Ty`. -/
instance instMergeStateDenote (t : Ty) : MergeState t.denote where
  merge := t.merge
  merge_comm := t.merge_comm
  merge_assoc := t.merge_assoc
  merge_idem := t.merge_idem

/-- Pointwise merge of a heterogeneous expression environment. -/
instance instMergeStateEnv (Γ : Schema) : MergeState (Env Γ) where
  merge := Env.merge
  merge_comm := Env.merge_comm
  merge_assoc := Env.merge_assoc
  merge_idem := Env.merge_idem

/-! ### Executable result-merge cost

The metric below counts primitive typed merge nodes. It is value-sensitive for
options (merging with `none` stops at the option node) and structural for pairs.
`mergeStepBound` is the worst case determined solely by the result type. -/

namespace CombinerCost

def mergeSteps : (type : Ty) → type.denote → type.denote → Nat
  | .bool, _, _ => 1
  | .nat, _, _ => 1
  | .pair left right, (left₁, right₁), (left₂, right₂) =>
      1 + mergeSteps left left₁ left₂ + mergeSteps right right₁ right₂
  | .option _, none, _ => 1
  | .option _, some _, none => 1
  | .option elem, some left, some right => 1 + mergeSteps elem left right

def mergeStepBound : Ty → Nat
  | .bool => 1
  | .nat => 1
  | .pair left right => 1 + mergeStepBound left + mergeStepBound right
  | .option elem => 1 + mergeStepBound elem

theorem mergeSteps_le_bound : ∀ (type : Ty) (left right : type.denote),
    mergeSteps type left right ≤ mergeStepBound type
  | .bool, _, _ => Nat.le_refl 1
  | .nat, _, _ => Nat.le_refl 1
  | .pair left right, (left₁, right₁), (left₂, right₂) => by
      simp only [mergeSteps, mergeStepBound]
      exact Nat.add_le_add
        (Nat.add_le_add_left (mergeSteps_le_bound left left₁ left₂) 1)
        (mergeSteps_le_bound right right₁ right₂)
  | .option _, none, _ => by simp [mergeSteps, mergeStepBound]
  | .option _, some _, none => by simp [mergeSteps, mergeStepBound]
  | .option elem, some left, some right => by
      simp only [mergeSteps, mergeStepBound]
      exact Nat.add_le_add_left (mergeSteps_le_bound elem left right) 1

end CombinerCost

/-- The expression-specific equation and the repository's general `JoinHom`
judgement are exactly the same proposition under the canonical instances. -/
theorem preservesMerge_iff_joinHom (term : Term Γ t) :
    PreservesMerge term ↔ JoinHom term.eval := Iff.rfl

/-- A syntactic positive certificate therefore supplies the general semantic
homomorphism directly. -/
theorem mergeSafe_joinHom {term : Term Γ t} (safe : MergeSafe term) :
    JoinHom term.eval :=
  (preservesMerge_iff_joinHom term).mp safe.sound

/-- A checked term can be asked the semantic question without pretending that
checking its types answered it. -/
theorem checked_preservesMerge_iff_joinHom (checked : Checked Γ) :
    PreservesMerge checked.term ↔ JoinHom checked.term.eval :=
  DerivedProgram.preservesMerge_iff_joinHom checked.term

/-! ## Proof-carrying derived programs -/

/-- A typed expression admitted for direct result shipping.  The type and term
remain dependent, and the positive syntax certificate is retained. -/
structure Program (Γ : Schema) where
  type : Ty
  term : Term Γ type
  safe : MergeSafe term

/-- Repackage the exact result of `Raw.certifyMergeSafe`; no term or proof is
reconstructed. -/
def Program.ofCertified (certified : CertifiedMergeSafe Γ) : Program Γ :=
  ⟨certified.type, certified.term, certified.safe⟩

/-- Run the proof-producing classifier on an already checked expression. -/
def Checked.toDerivedProgram? (checked : Checked Γ) : Option (Program Γ) :=
  match certifyMergeSafe checked.term with
  | none => none
  | some safe => some ⟨checked.type, checked.term, safe⟩

/-- Evaluation of the admitted typed program. -/
def Program.eval (program : Program Γ) (env : Env Γ) : program.type.denote :=
  program.term.eval env

/-- Exact positional occurrences, including child paths and opaque markers. -/
def Program.holes (program : Program Γ) : List Hole := program.term.holes

/-- Erased field positions read by the program. -/
def Program.reads (program : Program Γ) : List Nat := program.term.reads

theorem Program.reads_eq_hole_fields (program : Program Γ) :
    program.reads = program.holes.map Hole.field := rfl

/-- Direct derived results may be merged with the result carrier's merge. -/
theorem Program.joinHom (program : Program Γ) : JoinHom program.eval :=
  mergeSafe_joinHom program.safe

/-- Consequently, a certified expression is incrementally mergeable from its
results, with the result lattice's merge as combiner. -/
theorem Program.incrementallyMergeable (program : Program Γ) :
    IncrementallyMergeable program.eval :=
  joinHom_incrementallyMergeable program.joinHom

/-- The executable, proof-carrying combiner for the supported typed fragment.
It performs the result type's merge exactly once and retains the correctness
equation inherited from the expression's `MergeSafe` certificate. -/
def Program.executableCombiner (program : Program Γ) :
    ExecutableCombiner program.eval where
  combine := program.type.merge
  combineSteps := CombinerCost.mergeSteps program.type
  maxSteps := CombinerCost.mergeStepBound program.type
  correct := program.joinHom
  steps_le := CombinerCost.mergeSteps_le_bound program.type

/-- The executable combiner implements the semantic incremental-merge law. -/
theorem Program.executableCombine_correct (program : Program Γ)
    (left right : Env Γ) :
    program.eval (left ⊔ right) = program.executableCombiner.combine
      (program.eval left) (program.eval right) :=
  program.executableCombiner.correct left right

/-- Checked work bound for every pair of typed results. The metric counts one
result-lattice merge, independently of the source environments' sizes. -/
theorem Program.executableCombine_cost_le (program : Program Γ)
    (left right : program.type.denote) :
    program.executableCombiner.combineSteps left right ≤
      program.executableCombiner.maxSteps :=
  program.executableCombiner.steps_le left right

/-- The advertised maximum is computed solely from the typed result shape. -/
theorem Program.executableCombine_maxSteps (program : Program Γ) :
    program.executableCombiner.maxSteps =
      CombinerCost.mergeStepBound program.type := rfl

/-! ## Outcome-valued specification quotation -/

/-- Quote a typed expression as an outcome-valued specification: at an input
environment, its one admitted outcome is exactly the typed evaluation.  This
supplies `Specification`'s missing first-order language adapter without choosing
a different refinement relation or claiming that singleton outcomes are
coordination-free. -/
def Program.specification (program : Program Γ) :
    Specification.Specification (Env Γ) program.type.denote :=
  fun env outcome => outcome = program.eval env

@[simp] theorem Program.specification_iff (program : Program Γ)
    (env : Env Γ) (outcome : program.type.denote) :
    program.specification env outcome ↔ outcome = program.eval env := Iff.rfl

/-- Every typed execution has its computed outcome. -/
theorem Program.specification_total (program : Program Γ) :
    Specification.Total program.specification :=
  fun env => ⟨program.eval env, rfl⟩

/-! ## Positional world decoding

`Holes.World` stores `Nat` registers.  A typed schema can contain products,
options, and booleans, so no dishonest universal decoder exists.  Instead a
decoder carries exactly the required contract: equality at an in-range old
register position implies typed agreement at that position. -/

/-- A representation adapter from `Holes.World` to one typed schema. -/
structure WorldDecoder (Γ : Schema) where
  decode : Holes.World → Env Γ
  agreeAt : ∀ (x y : Holes.World) (field : Nat), field < Γ.length →
    Holes.read x field = Holes.read y field →
      Env.AgreeAt (decode x) (decode y) field

/-- Typed variables always erase to in-range positions. -/
theorem Var.index_lt_length (field : Var Γ t) : field.index < Γ.length :=
  Expr.Var.index_lt_length field

/-- Every read reported by a typed term is in its schema.  The custom case uses
the range proof required by `CustomNode`. -/
theorem term_reads_in_range (term : Term Γ t) :
    ∀ field ∈ term.reads, field < Γ.length :=
  Expr.Term.reads_in_range term

/-- A typed term factors through precisely the old register positions listed by
its syntactic read analysis.  Representation details outside those positions
cannot affect evaluation. -/
theorem term_evalWorld_eq_of_agreeOnReads (term : Term Γ t)
    (decoder : WorldDecoder Γ) (x y : Holes.World)
    (h : ∀ field ∈ term.reads, Holes.read x field = Holes.read y field) :
    term.eval (decoder.decode x) = term.eval (decoder.decode y) := by
  apply term.eval_ext
  intro field hfield
  exact decoder.agreeAt x y field (term_reads_in_range term field hfield)
    (h field hfield)

theorem Program.evalWorld_eq_of_agreeOnReads (program : Program Γ)
    (decoder : WorldDecoder Γ) (x y : Holes.World)
    (h : ∀ field ∈ program.reads, Holes.read x field = Holes.read y field) :
    program.eval (decoder.decode x) = program.eval (decoder.decode y) :=
  term_evalWorld_eq_of_agreeOnReads program.term decoder x y h

/-- The same locality statement indexed by exact positional holes rather than
their erased read list.  This is the bridge Evidence's old boundary could not
state before a syntax tree existed. -/
theorem Program.evalWorld_eq_of_agreeOnHoles (program : Program Γ)
    (decoder : WorldDecoder Γ) (x y : Holes.World)
    (h : ∀ hole ∈ program.holes,
      Holes.read x hole.field = Holes.read y hole.field) :
    program.eval (decoder.decode x) = program.eval (decoder.decode y) := by
  apply program.evalWorld_eq_of_agreeOnReads decoder x y
  intro field hfield
  obtain ⟨hole, hhole, hfield⟩ :=
    (Term.dependency_iff_positional_hole program.term field).mp hfield
  subst field
  exact h hole hhole

/-! ### A canonical decoder for all-natural schemas -/

/-- A homogeneous natural schema of the requested width. -/
def natSchema : Nat → Schema
  | 0 => []
  | n + 1 => .nat :: natSchema n

@[simp] theorem natSchema_length (n : Nat) : (natSchema n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [natSchema, ih]

/-- Decode `count` consecutive old-world registers starting at `offset`. -/
def natEnvFrom (offset : Nat) : (count : Nat) → Holes.World → Env (natSchema count)
  | 0, _ => .nil
  | count + 1, world =>
      .cons (Holes.read world offset) (natEnvFrom (offset + 1) count world)

theorem natEnvFrom_agreeAt (x y : Holes.World) :
    ∀ (count offset field : Nat), field < count →
      Holes.read x (offset + field) = Holes.read y (offset + field) →
      Env.AgreeAt (natEnvFrom offset count x) (natEnvFrom offset count y) field := by
  intro count
  induction count with
  | zero => intro _ field hlt; exact absurd hlt (Nat.not_lt_zero field)
  | succ count ih =>
      intro offset field hlt hread
      cases field with
      | zero => simpa [natEnvFrom] using hread
      | succ field =>
          apply ih (offset + 1) field (Nat.lt_of_succ_lt_succ hlt)
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hread

/-- The old `List Nat` world is a faithful valuation for an all-natural typed
schema, position for position. -/
def natWorldDecoder (count : Nat) : WorldDecoder (natSchema count) where
  decode := natEnvFrom 0 count
  agreeAt := by
    intro x y field hlt hread
    apply natEnvFrom_agreeAt x y count 0 field
    · simpa using hlt
    · simpa using hread

/-! ## Exact evidence-document materialization -/

/-- Evidence that a caller-authored source function agrees with an external
authenticity predicate on every candidate world actually present.  The
predicate is deliberately supplied by the deployment: this module cannot
derive signatures, causal ownership, or peer identity from a `Nat`. -/
structure SourceAuthenticity (worlds : GSet Holes.World)
    (source : Holes.World → Evidence.Source)
    (Authentic : Holes.World → Evidence.Source → Prop) : Prop where
  authentic : ∀ world, worlds world = true → Authentic world (source world)

/-- Evaluate the typed program in a decoded candidate world. -/
def Program.evalWorld (program : Program Γ) (decoder : WorldDecoder Γ)
    (world : Holes.World) : program.type.denote :=
  program.eval (decoder.decode world)

/-- Materialize the typed derivation as the existing attributed evidence
document.  Candidate values, their sources, obligations, and certificates are
all retained by `DerivedDocument.encodeEvidence`. -/
noncomputable def Program.document (program : Program Γ)
    (decoder : WorldDecoder Γ) (source : Holes.World → Evidence.Source)
    (obligations certificates : GSet Evidence.Source)
    (worlds : GSet Holes.World) :
    DerivedDocument.EvidenceDoc program.type.denote :=
  DerivedDocument.deriveDoc (program.evalWorld decoder) source
    obligations certificates worlds

/-- Exact candidate-node specification: a document contains precisely the
typed values justified by a candidate world, at the source assigned to that
same world. -/
theorem Program.document_candidate_iff (program : Program Γ)
    (decoder : WorldDecoder Γ) (source : Holes.World → Evidence.Source)
    (obligations certificates : GSet Evidence.Source)
    (worlds : GSet Holes.World) (value : program.type.denote)
    (origin : Evidence.Source) :
    program.document decoder source obligations certificates worlds
        (.cand value origin) = true ↔
      ∃ world, worlds world = true ∧
        program.evalWorld decoder world = value ∧ source world = origin :=
  DerivedDocument.deriveDoc_candidate_iff (program.evalWorld decoder)
    source obligations certificates worlds value origin

@[simp] theorem Program.document_owed (program : Program Γ)
    (decoder : WorldDecoder Γ) (source : Holes.World → Evidence.Source)
    (obligations certificates : GSet Evidence.Source)
    (worlds : GSet Holes.World) (origin : Evidence.Source) :
    program.document decoder source obligations certificates worlds (.owed origin) =
      obligations origin := rfl

@[simp] theorem Program.document_sealedBy (program : Program Γ)
    (decoder : WorldDecoder Γ) (source : Holes.World → Evidence.Source)
    (obligations certificates : GSet Evidence.Source)
    (worlds : GSet Holes.World) (origin : Evidence.Source) :
    program.document decoder source obligations certificates worlds (.sealedBy origin) =
      certificates origin := rfl

/-- Candidate-world materialization commutes with union, using the existing
`Holes` → `Evidence` → `DerivedDocument` homomorphism chain. -/
theorem Program.document_joinHom (program : Program Γ)
    (decoder : WorldDecoder Γ) (source : Holes.World → Evidence.Source)
    (obligations certificates : GSet Evidence.Source) :
    JoinHom (program.document decoder source obligations certificates) :=
  DerivedDocument.deriveDoc_hom (program.evalWorld decoder) source
    obligations certificates

/-- Forgetting attribution recovers exactly `Holes.evalSet` of the typed
evaluator; the document layer neither adds nor removes candidate values. -/
theorem Program.document_values_exact (program : Program Γ)
    (decoder : WorldDecoder Γ) (source : Holes.World → Evidence.Source)
    (obligations certificates : GSet Evidence.Source)
    (worlds : GSet Holes.World) :
    Evidence.values (DerivedDocument.decodeEvidence
      (program.document decoder source obligations certificates worlds)) =
      Holes.evalSet (program.evalWorld decoder) worlds := by
  change Evidence.values (Evidence.fromWorlds (program.evalWorld decoder)
    source worlds obligations certificates) = _
  exact Evidence.values_fromWorlds _ _ _ _ _

/-! ## Exact positional attribution materialization -/

/-- Augment the ordinary evidence document with one value/source/position node
for every positional occurrence in the typed expression. -/
noncomputable def Program.attributedDocument (program : Program Γ)
    (decoder : WorldDecoder Γ) (source : Holes.World → Evidence.Source)
    (obligations certificates : GSet Evidence.Source)
    (worlds : GSet Holes.World) :
    DerivedDocument.AttributedDoc program.type.denote Hole :=
  DerivedDocument.deriveAttributedDoc (program.evalWorld decoder) source
    program.holes obligations certificates worlds

/-- Dropping position nodes recovers the exact earlier materialization. -/
@[simp] theorem Program.forget_attributedDocument (program : Program Γ)
    (decoder : WorldDecoder Γ) (source : Holes.World → Evidence.Source)
    (obligations certificates : GSet Evidence.Source)
    (worlds : GSet Holes.World) :
    DerivedDocument.forgetPositions
        (program.attributedDocument decoder source obligations certificates worlds) =
      program.document decoder source obligations certificates worlds := rfl

/-- Exact candidate/source membership in the augmented document. -/
theorem Program.attributed_candidate_iff (program : Program Γ)
    (decoder : WorldDecoder Γ) (source : Holes.World → Evidence.Source)
    (obligations certificates : GSet Evidence.Source)
    (worlds : GSet Holes.World) (value : program.type.denote)
    (origin : Evidence.Source) :
    program.attributedDocument decoder source obligations certificates worlds
        (.evidence (.cand value origin)) = true ↔
      ∃ world, worlds world = true
        ∧ program.evalWorld decoder world = value
        ∧ source world = origin :=
  DerivedDocument.deriveAttributedDoc_candidate_iff
    (program.evalWorld decoder) source program.holes obligations certificates
    worlds value origin

/-- Exact candidate/source/position membership.  In particular, a node cannot
name a field merely because its erased index appears elsewhere: the complete
`Expr.Hole` (child path, field, and field/opaque kind) must occur in the typed
term's positional analysis. -/
theorem Program.attributed_position_iff (program : Program Γ)
    (decoder : WorldDecoder Γ) (source : Holes.World → Evidence.Source)
    (obligations certificates : GSet Evidence.Source)
    (worlds : GSet Holes.World)
    (candidate : Evidence.PositionCandidate program.type.denote Hole) :
    program.attributedDocument decoder source obligations certificates worlds
        (.position candidate) = true ↔
      ∃ world, worlds world = true
        ∧ program.evalWorld decoder world = candidate.value
        ∧ source world = candidate.source
        ∧ candidate.position ∈ program.holes :=
  DerivedDocument.deriveAttributedDoc_position_iff
    (program.evalWorld decoder) source program.holes obligations certificates
    worlds candidate

/-- Positioned materialization remains mergeable under candidate-world union. -/
theorem Program.attributedDocument_joinHom (program : Program Γ)
    (decoder : WorldDecoder Γ) (source : Holes.World → Evidence.Source)
    (obligations certificates : GSet Evidence.Source) :
    JoinHom (program.attributedDocument decoder source obligations certificates) :=
  DerivedDocument.deriveAttributedDoc_hom (program.evalWorld decoder) source
    program.holes obligations certificates

/-- The proof-gated materialization entry point.  Unlike `attributedDocument`,
this function cannot be called for a source assignment until the deployment
proves its chosen authenticity relation for every present world. -/
noncomputable def Program.verifiedAttributedDocument (program : Program Γ)
    (decoder : WorldDecoder Γ) (source : Holes.World → Evidence.Source)
    (Authentic : Holes.World → Evidence.Source → Prop)
    (obligations certificates : GSet Evidence.Source)
    (worlds : GSet Holes.World)
    (_authenticity : SourceAuthenticity worlds source Authentic) :
    DerivedDocument.AttributedDoc program.type.denote Hole :=
  program.attributedDocument decoder source obligations certificates worlds

/-- Exact positioned membership at the verified entry point includes the
external authenticity fact for the very world/source witness. -/
theorem Program.verified_position_iff (program : Program Γ)
    (decoder : WorldDecoder Γ) (source : Holes.World → Evidence.Source)
    (Authentic : Holes.World → Evidence.Source → Prop)
    (obligations certificates : GSet Evidence.Source)
    (worlds : GSet Holes.World)
    (authenticity : SourceAuthenticity worlds source Authentic)
    (candidate : Evidence.PositionCandidate program.type.denote Hole) :
    program.verifiedAttributedDocument decoder source Authentic
        obligations certificates worlds authenticity (.position candidate) = true ↔
      ∃ world, worlds world = true
        ∧ program.evalWorld decoder world = candidate.value
        ∧ source world = candidate.source
        ∧ candidate.position ∈ program.holes
        ∧ Authentic world candidate.source := by
  rw [Program.verifiedAttributedDocument, program.attributed_position_iff]
  constructor
  · rintro ⟨world, hworld, hvalue, hsource, hposition⟩
    refine ⟨world, hworld, hvalue, hsource, hposition, ?_⟩
    rw [← hsource]
    exact authenticity.authentic world hworld
  · rintro ⟨world, hworld, hvalue, hsource, hposition, _⟩
    exact ⟨world, hworld, hvalue, hsource, hposition⟩

/-! ## Existing incremental evaluator, indexed by the admitted program -/

abbrev Program.Cache (program : Program Γ) := Incremental.Cache program.term

def Program.buildCache (program : Program Γ) (env : Env Γ) : program.Cache :=
  Incremental.buildCache program.term env

def Program.update (program : Program Γ) (cache : program.Cache)
    (delta : Incremental.EnvDelta (Γ := Γ) cache.env) :
    Incremental.Result program.term delta.after :=
  Incremental.incremental program.term cache delta

theorem Program.update_correct (program : Program Γ) (cache : program.Cache)
    (delta : Incremental.EnvDelta (Γ := Γ) cache.env) :
    (program.update cache delta).value = program.eval delta.after :=
  Incremental.incremental_correct program.term cache delta

/-- When the existing structural dependency test reports no affected input,
the typed derived program performs zero root recomputations and reuses the
proved cached value. -/
theorem Program.update_off_dependency_zero (program : Program Γ)
    (cache : program.Cache)
    (delta : Incremental.EnvDelta (Γ := Γ) cache.env)
    (h : Incremental.touched delta program.term = false) :
    (program.update cache delta).recomputations = 0 ∧
      (program.update cache delta).value = cache.value :=
  Incremental.off_dependency_zero program.term cache delta h

/-! ## Fixtures and refusal boundaries -/

/-- A safe two-register derivation used to pin all adapter surfaces. -/
def maxFields : Program (natSchema 2) where
  type := .nat
  term := .natMax (.var .here) (.var (.there .here))
  safe := .natMax (.var .here) (.var (.there .here))

theorem maxFields_holes : maxFields.holes =
    [{ path := [0], field := 0, kind := .field },
     { path := [1], field := 1, kind := .field }] := rfl

theorem maxFields_reads : maxFields.reads = [0, 1] := rfl

theorem maxFields_eval_fixture :
    maxFields.evalWorld (natWorldDecoder 2) [3, 8] = (8 : Nat) := by
  change Nat.max 3 8 = 8
  decide

/-- Positive executable/cost fixture: the admitted maximum program combines
the shipped results `3` and `8` to `8` in exactly one checked merge step. -/
theorem maxFields_executable_fixture :
    maxFields.executableCombiner.combine
        (show maxFields.type.denote from (3 : Nat))
        (show maxFields.type.denote from (8 : Nat)) =
          (show maxFields.type.denote from (8 : Nat)) ∧
      maxFields.executableCombiner.combineSteps
        (show maxFields.type.denote from (3 : Nat))
        (show maxFields.type.denote from (8 : Nat)) = 1 ∧
      maxFields.executableCombiner.maxSteps = 1 := by
  decide

/-- Nontrivial structural-cost fixture: a pair result visits the pair node and
its Boolean and natural children, so both the actual and worst-case costs are
three primitive merge nodes. -/
def pairedFieldsProgram : Program [.bool, .nat] where
  type := .pair .bool .nat
  term := pairedFields
  safe := .pair (.var .here) (.var (.there .here))

theorem pairedFields_executable_cost_fixture :
    pairedFieldsProgram.executableCombiner.combineSteps
        (show pairedFieldsProgram.type.denote from ((false, 3) : Bool × Nat))
        (show pairedFieldsProgram.type.denote from ((true, 8) : Bool × Nat)) = 3 ∧
      pairedFieldsProgram.executableCombiner.maxSteps = 3 ∧
      pairedFieldsProgram.executableCombiner.combine
        (show pairedFieldsProgram.type.denote from ((false, 3) : Bool × Nat))
        (show pairedFieldsProgram.type.denote from ((true, 8) : Bool × Nat)) =
          (show pairedFieldsProgram.type.denote from ((true, 8) : Bool × Nat)) := by
  decide

def oneWorld : GSet Holes.World := Delta.addDelta [3, 8]
def noSources : GSet Evidence.Source := fun _ => false

theorem maxFields_document_single_candidate :
    maxFields.document (natWorldDecoder 2) (fun _ => 7) noSources noSources oneWorld
        (.cand (8 : Nat) 7) = true := by
  apply (maxFields.document_candidate_iff (natWorldDecoder 2) (fun _ => 7)
    noSources noSources oneWorld (8 : Nat) 7).2
  exact ⟨[3, 8], by simp [oneWorld, Delta.addDelta], by
    exact maxFields_eval_fixture, rfl⟩

def maxLeftPosition : Hole := { path := [0], field := 0, kind := .field }
def maxRightPosition : Hole := { path := [1], field := 1, kind := .field }
def falseRootPosition : Hole := { path := [], field := 0, kind := .field }

/-- Example deployment authenticity policy: the source id is register zero of
the candidate world. -/
def RegisterZeroAuthentic (world : Holes.World) (source : Evidence.Source) : Prop :=
  source = Holes.read world 0

def registerZeroAuthenticity (worlds : GSet Holes.World) :
    SourceAuthenticity worlds (fun world => Holes.read world 0)
      RegisterZeroAuthentic where
  authentic := fun _ _ => rfl

/-- The caller-authored constant source used by the ordinary attribution
fixtures is not authentic under the example policy and therefore cannot enter
the proof-gated materializer. -/
theorem constantSeven_source_mismatch :
    ¬ SourceAuthenticity oneWorld (fun _ => 7) RegisterZeroAuthentic := by
  intro authenticity
  have bad := authenticity.authentic [3, 8]
    (by simp [oneWorld, Delta.addDelta])
  exact (by decide : (7 : Nat) ≠ 3) bad

theorem maxFields_left_position_attributed :
    maxFields.attributedDocument (natWorldDecoder 2) (fun _ => 7)
        noSources noSources oneWorld
        (.position (⟨(8 : Nat), 7, maxLeftPosition⟩ :
          Evidence.PositionCandidate Nat Hole)) = true := by
  apply (maxFields.attributed_position_iff (natWorldDecoder 2) (fun _ => 7)
    noSources noSources oneWorld _).2
  exact ⟨[3, 8], by simp [oneWorld, Delta.addDelta], maxFields_eval_fixture,
    rfl, by simp [maxFields_holes, maxLeftPosition]⟩

theorem maxFields_right_position_attributed :
    maxFields.attributedDocument (natWorldDecoder 2) (fun _ => 7)
        noSources noSources oneWorld
        (.position (⟨(8 : Nat), 7, maxRightPosition⟩ :
          Evidence.PositionCandidate Nat Hole)) = true := by
  apply (maxFields.attributed_position_iff (natWorldDecoder 2) (fun _ => 7)
    noSources noSources oneWorld _).2
  exact ⟨[3, 8], by simp [oneWorld, Delta.addDelta], maxFields_eval_fixture,
    rfl, by simp [maxFields_holes, maxRightPosition]⟩

theorem maxFields_verified_left_position :
    maxFields.verifiedAttributedDocument (natWorldDecoder 2)
        (fun world => Holes.read world 0) RegisterZeroAuthentic
        noSources noSources oneWorld (registerZeroAuthenticity oneWorld)
        (.position (⟨(8 : Nat), 3, maxLeftPosition⟩ :
          Evidence.PositionCandidate Nat Hole)) = true := by
  apply (maxFields.verified_position_iff (natWorldDecoder 2)
    (fun world => Holes.read world 0) RegisterZeroAuthentic
    noSources noSources oneWorld (registerZeroAuthenticity oneWorld) _).2
  exact ⟨[3, 8], by simp [oneWorld, Delta.addDelta], maxFields_eval_fixture,
    rfl, by simp [maxFields_holes, maxLeftPosition], rfl⟩

/-- Erased field `0` is not enough: the nonexistent root path is absent even
though the real left-child occurrence reads field `0`. -/
theorem maxFields_false_root_position_absent :
    maxFields.attributedDocument (natWorldDecoder 2) (fun _ => 7)
        noSources noSources oneWorld
        (.position (⟨(8 : Nat), 7, falseRootPosition⟩ :
          Evidence.PositionCandidate Nat Hole)) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨_, _, _, _, hposition⟩ :=
    (maxFields.attributed_position_iff (natWorldDecoder 2) (fun _ => 7)
      noSources noSources oneWorld _).1 h
  simp [maxFields_holes, falseRootPosition] at hposition

def maxBase : Env (natSchema 2) :=
  .cons (show Ty.nat.denote from (3 : Nat))
    (.cons (show Ty.nat.denote from (8 : Nat)) .nil)
def maxAfterOutside : Env (natSchema 2) :=
  .cons (show Ty.nat.denote from (3 : Nat))
    (.cons (show Ty.nat.denote from (8 : Nat)) .nil)

/-- A conservative delta that reports no changes pins the executable
off-dependency zero-work contract on the concrete derived program. -/
def maxUntouchedDelta : Incremental.EnvDelta maxBase where
  after := maxAfterOutside
  changed := fun _ => false
  unchanged := by
    intro type field _
    cases field <;> rfl

theorem maxFields_incremental_correct :
    (maxFields.update (maxFields.buildCache maxBase) maxUntouchedDelta).value =
      maxFields.eval maxAfterOutside :=
  maxFields.update_correct (maxFields.buildCache maxBase) maxUntouchedDelta

theorem maxFields_off_dependency_zero :
    (maxFields.update (maxFields.buildCache maxBase) maxUntouchedDelta).recomputations = 0 ∧
      (maxFields.update (maxFields.buildCache maxBase) maxUntouchedDelta).value =
        (maxFields.buildCache maxBase).value := by
  apply maxFields.update_off_dependency_zero
  rfl

/-- Negated membership is typed but not monotone, hence cannot be promoted to a
merge-safe derived program. -/
theorem negated_membership_refused :
    ¬ Monotone negatedMembership ∧ certifyMergeSafe negatedMembership = none :=
  ⟨negatedMembership_not_monotone, rfl⟩

/-- Addition is monotone here but does not preserve merge, so it cannot be
shipped as a bare join-homomorphic result. -/
theorem summed_fields_refused :
    ¬ PreservesMerge summedFields ∧ certifyMergeSafe summedFields = none :=
  ⟨summedFields_not_preservesMerge, summedFields_not_classified_mergeSafe⟩

/-- Ill-typed raw syntax and unsupported raw custom nodes fail before any
derived-program certificate can be constructed. -/
theorem malformed_and_raw_custom_refused :
    Raw.certifyMergeSafe [] malformedNotNat = none ∧
      Raw.certifyMergeSafe [] (.custom "unchecked") = none :=
  ⟨malformed_not_classified, raw_custom_not_classified⟩

/-- Even a local custom node is never auto-classified.  The explicit
proof-carrying `MergeSafe.custom` escape hatch remains available separately. -/
theorem opaque_without_proof_refused :
    certifyMergeSafe hiddenFirstTerm = none ∧
      certifyMonotone hiddenFirstTerm = none :=
  ⟨opaque_not_auto_mergeSafe, opaque_not_auto_monotone⟩

/-- Explicitly admitted custom code exposes only opaque dependency positions;
the adapter does not invent an inspectable internal syntax tree. -/
def hiddenProgram : Program [.nat] where
  type := .nat
  term := hiddenFirstTerm
  safe := hiddenFirst_explicitlySafe

theorem hiddenProgram_holes : hiddenProgram.holes =
    [{ path := [], field := 0, kind := .opaque }] := rfl

theorem hiddenProgram_only_opaque {hole : Hole} (h : hole ∈ hiddenProgram.holes) :
    hole.kind = .opaque := by
  simpa [hiddenProgram_holes] using congrArg Hole.kind (List.mem_singleton.mp h)

/-- A literal has a candidate value but no position attribution. -/
def literalProgram : Program [] where
  type := .nat
  term := .litNat 4
  safe := .litNat 4

theorem literalProgram_no_position_attribution
    (decoder : WorldDecoder []) (source : Holes.World → Evidence.Source)
    (worlds : GSet Holes.World)
    (candidate : Evidence.PositionCandidate literalProgram.type.denote Hole) :
    literalProgram.attributedDocument decoder source noSources noSources worlds
        (.position candidate) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨_, _, _, _, hposition⟩ :=
    (literalProgram.attributed_position_iff decoder source
      noSources noSources worlds candidate).1 h
  exact List.not_mem_nil hposition

end Uwueave.Preo.DerivedProgram
