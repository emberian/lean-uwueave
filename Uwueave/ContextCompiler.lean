/-
# Uwueave.ContextCompiler — executable finite contextual quotients.

`MinimalSummary.CtxEquiv` gives the semantic, carrier-wide quotient for one
query.  This module supplies the finite compiler that boundary deliberately
left open.  The caller provides:

* a finite list of states to classify;
* a finite list of allowed merge contexts;
* a finite homogeneous list of queries.

The compiler evaluates every query now and after every allowed context.  That
answer matrix is a state's `Signature`.  Equal signatures are exactly
multi-query contextual equivalence relative to the supplied context list.
Distinct signatures are deduplicated into `classKeys`, and `representative?`
returns the first enumerated state with a requested key.  The decoder is fully
executable and choice-free.

The scope is intentionally visible in every definition.  A finite state list
is not claimed complete unless a caller proves it.  A finite context list may
be strictly coarser than `MinimalSummary.CtxEquiv`; `restricted_contexts_can_
coarsen` exhibits that fact.  The matrix preserves which context produced an
answer, so it is not `CertificateScope.ResidualEq`, which deliberately keeps
only the image of possible answers.  No global canonical minimal encoding or
bit-optimal serialization is claimed.
-/
import Uwueave.MinimalSummary

namespace Uwueave.ContextCompiler

open Uwueave
open Uwueave.Catalog

universe u v w

/-! ## §1. Finite contextual signatures -/

/-- A finite compiler specification.  Queries are homogeneous (`S -> R`) so
their answers form an ordinary executable matrix. -/
structure Spec (S : Type u) (R : Type v) [MergeState S] where
  states : List S
  contexts : List S
  queries : List (S → R)

/-- The answers to all configured queries at one state. -/
def answerVector {S : Type u} {R : Type v} (queries : List (S → R))
    (state : S) : List R :=
  queries.map (fun query => query state)

/-- A contextual answer matrix.  The first row is the present answer vector;
the remaining rows are answers after each allowed merge context, in order. -/
abbrev Signature (R : Type v) := List (List R)

/-- Compile one state to its complete finite contextual signature. -/
def Spec.signature {S : Type u} {R : Type v} [MergeState S]
    (spec : Spec S R) (state : S) : Signature R :=
  answerVector spec.queries state ::
    spec.contexts.map (fun context => answerVector spec.queries (state ⊔ context))

/-- One-query contextual equivalence relative to an explicit finite context
universe.  This is the finite restriction of `MinimalSummary.CtxEquiv`. -/
def QueryCtxEquivOn {S : Type u} {R : Type v} [MergeState S]
    (contexts : List S) (query : S → R) (x y : S) : Prop :=
  query x = query y ∧
    ∀ context ∈ contexts, query (x ⊔ context) = query (y ⊔ context)

/-- Multi-query contextual equivalence over exactly the compiler's query and
context lists. -/
def Spec.CtxEquivOn {S : Type u} {R : Type v} [MergeState S]
    (spec : Spec S R) (x y : S) : Prop :=
  ∀ query ∈ spec.queries, QueryCtxEquivOn spec.contexts query x y

private theorem map_same_eq_iff {A : Type u} {B : Type v}
    (xs : List A) (f g : A → B) :
    xs.map f = xs.map g ↔ ∀ x ∈ xs, f x = g x := by
  induction xs with
  | nil => simp
  | cons a rest ih => simp [ih]

theorem answerVector_eq_iff {S : Type u} {R : Type v}
    (queries : List (S → R)) (x y : S) :
    answerVector queries x = answerVector queries y ↔
      ∀ query ∈ queries, query x = query y := by
  exact map_same_eq_iff queries (fun query => query x) (fun query => query y)

/-- **Compiler exactness.** Key equality is neither an approximation nor a
hashing claim: it is exactly relative contextual equivalence for every
configured query and allowed context. -/
theorem signature_eq_iff {S : Type u} {R : Type v} [MergeState S]
    (spec : Spec S R) (x y : S) :
    spec.signature x = spec.signature y ↔ spec.CtxEquivOn x y := by
  constructor
  · intro h query hquery
    have hpresent : answerVector spec.queries x = answerVector spec.queries y :=
      List.cons.inj h |>.1
    have hcontexts :
        spec.contexts.map (fun context => answerVector spec.queries (x ⊔ context)) =
          spec.contexts.map (fun context => answerVector spec.queries (y ⊔ context)) :=
      List.cons.inj h |>.2
    refine ⟨(answerVector_eq_iff spec.queries x y).mp hpresent query hquery, ?_⟩
    intro context hcontext
    have hvectors := (map_same_eq_iff spec.contexts
      (fun z => answerVector spec.queries (x ⊔ z))
      (fun z => answerVector spec.queries (y ⊔ z))).mp hcontexts context hcontext
    exact (answerVector_eq_iff spec.queries (x ⊔ context) (y ⊔ context)).mp
      hvectors query hquery
  · intro h
    have hpresent : answerVector spec.queries x = answerVector spec.queries y := by
      apply (answerVector_eq_iff spec.queries x y).mpr
      intro query hquery
      exact (h query hquery).1
    have hcontexts :
        spec.contexts.map (fun context => answerVector spec.queries (x ⊔ context)) =
          spec.contexts.map (fun context => answerVector spec.queries (y ⊔ context)) := by
      apply (map_same_eq_iff spec.contexts
        (fun context => answerVector spec.queries (x ⊔ context))
        (fun context => answerVector spec.queries (y ⊔ context))).mpr
      intro context hcontext
      apply (answerVector_eq_iff spec.queries (x ⊔ context) (y ⊔ context)).mpr
      intro query hquery
      exact (h query hquery).2 context hcontext
    change
      answerVector spec.queries x ::
          spec.contexts.map (fun context => answerVector spec.queries (x ⊔ context)) =
        answerVector spec.queries y ::
          spec.contexts.map (fun context => answerVector spec.queries (y ⊔ context))
    rw [hpresent, hcontexts]

/-- Carrier-wide contextual equivalence implies every finite restriction. -/
theorem queryCtxEquivOn_of_ctxEquiv {S : Type u} {R : Type v} [MergeState S]
    (contexts : List S) {query : S → R} {x y : S}
    (h : CtxEquiv query x y) :
    QueryCtxEquivOn contexts query x y :=
  ⟨h.1, fun context _ => h.2 context⟩

/-- If the supplied context enumeration covers the carrier, the finite
one-query relation is exactly `MinimalSummary.CtxEquiv`. -/
theorem queryCtxEquivOn_iff_ctxEquiv_of_complete
    {S : Type u} {R : Type v} [MergeState S]
    (contexts : List S) (complete : ∀ context : S, context ∈ contexts)
    (query : S → R) (x y : S) :
    QueryCtxEquivOn contexts query x y ↔ CtxEquiv query x y := by
  constructor
  · intro h
    exact ⟨h.1, fun context => h.2 context (complete context)⟩
  · exact queryCtxEquivOn_of_ctxEquiv contexts

/-- With a complete context enumeration, a compiled key is the common
refinement of the carrier-wide contextual quotients for all supplied queries. -/
theorem signature_eq_iff_all_ctxEquiv_of_complete
    {S : Type u} {R : Type v} [MergeState S]
    (spec : Spec S R) (complete : ∀ context : S, context ∈ spec.contexts)
    (x y : S) :
    spec.signature x = spec.signature y ↔
      ∀ query ∈ spec.queries, CtxEquiv query x y := by
  rw [signature_eq_iff]
  constructor
  · intro h query hquery
    exact (queryCtxEquivOn_iff_ctxEquiv_of_complete spec.contexts complete query x y).mp
      (h query hquery)
  · intro h query hquery
    exact (queryCtxEquivOn_iff_ctxEquiv_of_complete spec.contexts complete query x y).mpr
      (h query hquery)

/-! ## §2. Deduplicated classes and a choice-free decoder -/

/-- The finite class table: compile every enumerated state and erase duplicate
signatures.  `List.eraseDups` preserves the first occurrence deterministically. -/
def Spec.classKeys {S : Type u} {R : Type v} [MergeState S]
    [BEq R] [LawfulBEq R] (spec : Spec S R) : List (Signature R) :=
  (spec.states.map spec.signature).eraseDups

theorem mem_classKeys_iff {S : Type u} {R : Type v} [MergeState S]
    [BEq R] [LawfulBEq R] (spec : Spec S R) (key : Signature R) :
    key ∈ spec.classKeys ↔ ∃ state ∈ spec.states, spec.signature state = key := by
  simp [Spec.classKeys]

/-- A representative decoder that scans the caller's enumeration.  There is
no quotient choice and no `Classical.choice`: the first matching state wins. -/
def Spec.representative? {S : Type u} {R : Type v} [MergeState S]
    [BEq R] [LawfulBEq R] (spec : Spec S R) (key : Signature R) : Option S :=
  spec.states.find? (fun state => spec.signature state == key)

/-- Any returned representative came from the supplied state universe and
encodes back to exactly the requested class key. -/
theorem representative_sound {S : Type u} {R : Type v} [MergeState S]
    [BEq R] [LawfulBEq R] (spec : Spec S R) {key : Signature R} {state : S}
    (h : spec.representative? key = some state) :
    state ∈ spec.states ∧ spec.signature state = key := by
  have hfind :
      spec.states.find? (fun candidate => spec.signature candidate == key) = some state := by
    simpa [Spec.representative?] using h
  refine ⟨List.mem_of_find?_eq_some hfind, ?_⟩
  have hmatches : (spec.signature state == key) = true :=
    @List.find?_some S (fun candidate => spec.signature candidate == key)
      state spec.states hfind
  exact beq_iff_eq.mp hmatches

/-- Every compiled class has a concrete, choice-free representative. -/
theorem representative_complete {S : Type u} {R : Type v} [MergeState S]
    [BEq R] [LawfulBEq R] (spec : Spec S R) {key : Signature R}
    (hkey : key ∈ spec.classKeys) :
    ∃ state, spec.representative? key = some state ∧ spec.signature state = key := by
  obtain ⟨witness, hwitness, hsignature⟩ := (mem_classKeys_iff spec key).mp hkey
  have hisSome :
      (spec.states.find? (fun state => spec.signature state == key)).isSome = true :=
    List.find?_isSome.mpr ⟨witness, hwitness, beq_iff_eq.mpr hsignature⟩
  cases hfind : spec.states.find? (fun state => spec.signature state == key) with
  | none => simp [hfind] at hisSome
  | some state =>
      have hsome : spec.representative? key = some state := by
        simpa [Spec.representative?] using hfind
      exact ⟨state, hsome, (representative_sound spec hsome).2⟩

/-- Encode followed by representative decoding is exact up to the compiled
relative contextual equivalence, for every enumerated state. -/
theorem encode_decode_exact {S : Type u} {R : Type v} [MergeState S]
    [BEq R] [LawfulBEq R] (spec : Spec S R) {state : S}
    (hstate : state ∈ spec.states) :
    ∃ representative,
      spec.representative? (spec.signature state) = some representative ∧
      spec.CtxEquivOn representative state := by
  have hkey : spec.signature state ∈ spec.classKeys :=
    (mem_classKeys_iff spec (spec.signature state)).mpr ⟨state, hstate, rfl⟩
  obtain ⟨representative, hdecode, hexact⟩ := representative_complete spec hkey
  exact ⟨representative, hdecode, (signature_eq_iff spec representative state).mp hexact⟩

/-! ## §3. Minimality and decidable sufficiency -/

/-- A caller key is sufficient for this finite query/context family when equal
keys force relative contextual equivalence. -/
def Spec.SufficientFor {S : Type u} {R : Type v} [MergeState S]
    (spec : Spec S R) {K : Type w} (key : S → K) : Prop :=
  ∀ x y, key x = key y → spec.CtxEquivOn x y

/-- **Common-refinement universal property.** Every sufficient caller key
refines the compiled signature partition.  This is minimality in the partition
order, not a claim about serialized bit length. -/
theorem sufficient_refines_signature {S : Type u} {R : Type v} [MergeState S]
    (spec : Spec S R) {K : Type w} (key : S → K)
    (hsufficient : spec.SufficientFor key) {x y : S} (hkey : key x = key y) :
    spec.signature x = spec.signature y :=
  (signature_eq_iff spec x y).mpr (hsufficient x y hkey)

/-- The compiler's own signature is sufficient. -/
theorem signature_sufficient {S : Type u} {R : Type v} [MergeState S]
    (spec : Spec S R) : spec.SufficientFor spec.signature :=
  fun x y h => (signature_eq_iff spec x y).mp h

/-- Equality of finite signatures is executable, and its boolean result is
exactly the compiler's relative contextual-equivalence judgement. -/
def Spec.sameClass {S : Type u} {R : Type v} [MergeState S]
    [BEq R] (spec : Spec S R) (x y : S) : Bool :=
  spec.signature x == spec.signature y

@[simp] theorem sameClass_eq_true_iff {S : Type u} {R : Type v} [MergeState S]
    [BEq R] [LawfulBEq R] (spec : Spec S R) (x y : S) :
    spec.sameClass x y = true ↔ spec.CtxEquivOn x y := by
  rw [Spec.sameClass, beq_iff_eq, signature_eq_iff]

/-! ## §4. Executable fixtures -/

namespace Fixtures

/-- Empty and full G-Sets complete the four-state `Bool` carrier enumeration. -/
def emptyBool : GSet Bool := fun _ => false
def fullBool : GSet Bool := fun _ => true

def boolStates : List (GSet Bool) :=
  [emptyBool, JoinHom.sawA, JoinHom.sawB, fullBool]

/-- The membership observation over the complete four-state carrier. -/
def membership : Spec (GSet Bool) Bool where
  states := boolStates
  contexts := boolStates
  queries := [MinimalSummary.memQuery true]

/-- The finite compiler recovers the semantic membership collapse: four
states produce exactly two contextual classes. -/
theorem membership_has_exactly_two_classes : membership.classKeys.length = 2 := by
  decide

/-- One threshold-distinguishing context is enough to keep `{0}` and `{1}` in
different classes, even though their present threshold answers agree. -/
def thresholdDistinguishing : Spec (GSet (Fin 3)) Bool where
  states := [MinimalSummary.pick 0, MinimalSummary.pick 1]
  contexts := [MinimalSummary.pick 1]
  queries := [MinimalSummary.atLeast 2]

theorem threshold_context_keeps_singletons_distinct :
    thresholdDistinguishing.signature (MinimalSummary.pick 0) ≠
      thresholdDistinguishing.signature (MinimalSummary.pick 1) := by
  decide

/-- A two-query product keeps both named membership observations.  The two
one-element states are not collapsed into their common cardinality class. -/
def twoMembershipQueries : Spec (GSet Bool) Bool where
  states := [JoinHom.sawA, JoinHom.sawB]
  contexts := []
  queries := [MinimalSummary.memQuery false, MinimalSummary.memQuery true]

theorem two_query_product_not_collapsed :
    twoMembershipQueries.classKeys.length = 2 ∧
      twoMembershipQueries.signature JoinHom.sawA ≠
        twoMembershipQueries.signature JoinHom.sawB := by
  decide

/-- With no allowed future contexts, the threshold compiler sees only the
equal present answers of `{0}` and `{1}`. -/
def thresholdRestricted : Spec (GSet (Fin 3)) Bool where
  states := [MinimalSummary.pick 0, MinimalSummary.pick 1]
  contexts := []
  queries := [MinimalSummary.atLeast 2]

/-- **Finite reachable contexts may coarsen the global quotient.** The empty
allowed-context universe identifies `{0}` and `{1}`, while the carrier-wide
`MinimalSummary.CtxEquiv` separates them using context `{1}`. -/
theorem restricted_contexts_can_coarsen :
    thresholdRestricted.signature (MinimalSummary.pick 0) =
        thresholdRestricted.signature (MinimalSummary.pick 1) ∧
      ¬ CtxEquiv (MinimalSummary.atLeast 2)
        (MinimalSummary.pick 0) (MinimalSummary.pick 1) := by
  exact ⟨by decide, MinimalSummary.threshold_finer_than_answer.2⟩

/-- The compiled decoder is concrete: the false membership class selects the
first enumerated state, `emptyBool`. -/
theorem membership_decoder_is_first :
    membership.representative? (membership.signature emptyBool) = some emptyBool := by
  rfl

end Fixtures

end Uwueave.ContextCompiler
