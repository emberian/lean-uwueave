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
        program.evalWorld decoder world = value ∧ source world = origin := by
  rw [Program.document, DerivedDocument.deriveDoc,
    DerivedDocument.evidenceOf, DerivedDocument.encodeEvidence,
    Evidence.fromWorlds, Holes.mem_evalSet]
  constructor
  · rintro ⟨world, hworld, hp⟩
    exact ⟨world, hworld, congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  · rintro ⟨world, hworld, hvalue, horigin⟩
    exact ⟨world, hworld, by rw [hvalue, horigin]⟩

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

def oneWorld : GSet Holes.World := Delta.addDelta [3, 8]
def noSources : GSet Evidence.Source := fun _ => false

theorem maxFields_document_single_candidate :
    maxFields.document (natWorldDecoder 2) (fun _ => 7) noSources noSources oneWorld
        (.cand (8 : Nat) 7) = true := by
  apply (maxFields.document_candidate_iff (natWorldDecoder 2) (fun _ => 7)
    noSources noSources oneWorld (8 : Nat) 7).2
  exact ⟨[3, 8], by simp [oneWorld, Delta.addDelta], by
    exact maxFields_eval_fixture, rfl⟩

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

end Uwueave.Preo.DerivedProgram
