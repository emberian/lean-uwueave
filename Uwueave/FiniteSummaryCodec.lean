/-
# Uwueave.FiniteSummaryCodec — exact finite contextual-class indices and their bit price.

`ContextCompiler` constructs a duplicate-free list of contextual signatures for
an authored finite state/context universe.  This module gives that list its
smallest honest *fixed-width index* interface:

* `CompleteSpec` requires the authored state and context lists to cover their
  carriers.  This is proof data, not a boolean guessed by the codec.
* `ClassKey` is membership in `Spec.classKeys`; `ClassIndex` is exactly
  `Fin classCount`.  `encodeKey` and `decodeKey` are inverse, so the numerical
  bound neither drops nor invents a contextual class.
* `bitCost n` is zero for at most one class and `log2 (n - 1) + 1` otherwise.
  Every class index embeds in `Fin (2 ^ bitCost n)`.
* `fixedWidth_information_lower_bound` states the converse that is actually
  justified: any *injective* code from `Fin n` into `Fin (2 ^ bits)` forces
  `n <= 2 ^ bits`.  There is no claim that arbitrary quotients are finite,
  encodable, or universally compressible.

The fixtures recover the two contextual classes of membership at one bit and
the five classes of the `Fin 3`, threshold-two example at three bits.  A second
threshold fixture deliberately omits every future context: it collapses the
five classes to the two present answers and is proved inadmissible as a
`CompleteSpec`.  Context coverage is therefore load-bearing.
-/
import Uwueave.ContextCompiler

namespace Uwueave.FiniteSummaryCodec

open Uwueave
open Uwueave.Catalog
open Uwueave.ContextCompiler

universe u v w

/-! ## 1. A finite compiler specification whose authored universes are complete -/

/-- A `ContextCompiler.Spec` together with coverage of both finite universes.

State coverage makes every carrier state encodable.  Context coverage upgrades
`Spec.signature_eq_iff` from the authored relative relation to carrier-wide
`MinimalSummary.CtxEquiv` for every authored query. -/
structure CompleteSpec (S : Type u) (R : Type v) [MergeState S] where
  spec : ContextCompiler.Spec S R
  states_complete : forall state : S, state ∈ spec.states
  contexts_complete : forall context : S, context ∈ spec.contexts

variable {S : Type u} {R : Type v} [MergeState S] [BEq R] [LawfulBEq R]

/-! ## 2. Canonical duplicate-free indices -/

/-- `eraseDups` really produces a duplicate-free list.  Kept local because the
core list API exposes membership preservation but no theorem with this exact
name. -/
private theorem eraseDups_nodup {alpha : Type w} [BEq alpha] [LawfulBEq alpha] :
    forall xs : List alpha, xs.eraseDups.Nodup
  | [] => by simp
  | x :: xs => by
      rw [List.eraseDups_cons, List.nodup_cons]
      constructor
      · simp
      · exact eraseDups_nodup (xs.filter fun y => !y == x)
termination_by xs => xs.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- The first index found for a member points back to that member. -/
private theorem get_idxOf_of_mem {alpha : Type w} [BEq alpha] [LawfulBEq alpha]
    {x : alpha} {xs : List alpha} (h : x ∈ xs) :
    xs.get ⟨xs.idxOf x, List.idxOf_lt_length_of_mem h⟩ = x := by
  induction xs with
  | nil => simp at h
  | cons y ys ih =>
      simp only [List.mem_cons] at h
      by_cases hy : y = x
      · subst y
        simp
      · have hx : x ∈ ys := h.resolve_left (Ne.symm hy)
        simp only [List.idxOf_cons, cond_eq_ite, beq_iff_eq, hy, ↓reduceIte]
        exact ih hx

/-- On a duplicate-free list, looking up an indexed element returns that exact
index rather than merely some equal occurrence. -/
private theorem idxOf_get_eq_of_nodup {alpha : Type w} [BEq alpha] [LawfulBEq alpha]
    (xs : List alpha) (hn : xs.Nodup) (i : Fin xs.length) :
    xs.idxOf (xs.get i) = i.val := by
  let x := xs.get i
  have hmem : x ∈ xs := List.get_mem xs i
  have hidx : xs.idxOf x < xs.length := List.idxOf_lt_length_of_mem hmem
  apply (List.getElem?_inj hidx hn).mp
  rw [List.getElem?_eq_getElem hidx, List.getElem?_eq_getElem i.isLt]
  change some (xs.get ⟨xs.idxOf x, hidx⟩) = some (xs.get i)
  rw [get_idxOf_of_mem hmem]

/-- A contextual class key is exactly one signature in the deduplicated class
table. -/
abbrev ClassKey (complete : CompleteSpec S R) :=
  { key : ContextCompiler.Signature R // key ∈ complete.spec.classKeys }

/-- The exact number of compiled contextual classes. -/
def classCount (complete : CompleteSpec S R) : Nat :=
  complete.spec.classKeys.length

/-- A class index is bounded by exactly the number of deduplicated keys. -/
abbrev ClassIndex (complete : CompleteSpec S R) := Fin (classCount complete)

theorem classKeys_nodup (complete : CompleteSpec S R) :
    complete.spec.classKeys.Nodup := by
  unfold ContextCompiler.Spec.classKeys
  exact eraseDups_nodup _

/-- Canonical encoding: the first (and, by `classKeys_nodup`, only) occurrence
of the class key. -/
def encodeKey (complete : CompleteSpec S R) (key : ClassKey complete) :
    ClassIndex complete :=
  ⟨complete.spec.classKeys.idxOf key.val,
    List.idxOf_lt_length_of_mem key.property⟩

/-- Canonical decoding: index directly into the duplicate-free class table. -/
def decodeKey (complete : CompleteSpec S R) (index : ClassIndex complete) :
    ClassKey complete :=
  ⟨complete.spec.classKeys.get index, List.get_mem _ _⟩

theorem decode_encode_key (complete : CompleteSpec S R)
    (key : ClassKey complete) :
    decodeKey complete (encodeKey complete key) = key := by
  apply Subtype.ext
  exact get_idxOf_of_mem key.property

theorem encode_decode_index (complete : CompleteSpec S R)
    (index : ClassIndex complete) :
    encodeKey complete (decodeKey complete index) = index := by
  apply Fin.ext
  exact idxOf_get_eq_of_nodup complete.spec.classKeys
    (classKeys_nodup complete) index

theorem encodeKey_injective (complete : CompleteSpec S R) :
    Function.Injective (encodeKey complete) := by
  intro left right h
  calc
    left = decodeKey complete (encodeKey complete left) :=
      (decode_encode_key complete left).symm
    _ = decodeKey complete (encodeKey complete right) := congrArg _ h
    _ = right := decode_encode_key complete right

/-- The class table has *exactly* `classCount` indices: decoding is a bijection,
not merely an upper-bound injection. -/
theorem class_count_exact (complete : CompleteSpec S R) :
    Function.Injective (decodeKey complete)
      ∧ Function.Surjective (decodeKey complete) := by
  constructor
  · intro left right h
    calc
      left = encodeKey complete (decodeKey complete left) :=
        (encode_decode_index complete left).symm
      _ = encodeKey complete (decodeKey complete right) := congrArg _ h
      _ = right := encode_decode_index complete right
  · intro key
    exact ⟨encodeKey complete key, decode_encode_key complete key⟩

/-- Every carrier state has a class key because the authored state enumeration
is complete. -/
def stateKey (complete : CompleteSpec S R) (state : S) : ClassKey complete :=
  ⟨complete.spec.signature state,
    (ContextCompiler.mem_classKeys_iff complete.spec _).2
      ⟨state, complete.states_complete state, rfl⟩⟩

/-- Encode a carrier state by its exact contextual class. -/
def encodeState (complete : CompleteSpec S R) (state : S) : ClassIndex complete :=
  encodeKey complete (stateKey complete state)

/-- Completeness makes index equality exactly carrier-wide contextual
equivalence for every authored query. -/
theorem encodeState_eq_iff_all_ctxEquiv (complete : CompleteSpec S R)
    (left right : S) :
    encodeState complete left = encodeState complete right ↔
      ∀ query ∈ complete.spec.queries,
        Uwueave.CtxEquiv query left right := by
  constructor
  · intro h
    have hkey : stateKey complete left = stateKey complete right :=
      encodeKey_injective complete (by simpa [encodeState] using h)
    have hsignature : complete.spec.signature left = complete.spec.signature right :=
      congrArg Subtype.val hkey
    exact (ContextCompiler.signature_eq_iff_all_ctxEquiv_of_complete
      complete.spec complete.contexts_complete left right).1 hsignature
  · intro h
    have hsignature : complete.spec.signature left = complete.spec.signature right :=
      (ContextCompiler.signature_eq_iff_all_ctxEquiv_of_complete
        complete.spec complete.contexts_complete left right).2 h
    apply congrArg (encodeKey complete)
    exact Subtype.ext hsignature

/-! ## 3. Fixed-width cost and the honest information lower bound -/

/-- The fixed-width bit cost of `n` codes: zero bits for zero or one code, and
`ceil(log2 n)` thereafter, written using core's floor `Nat.log2`. -/
def bitCost : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => Nat.log2 (n + 1) + 1

/-- The chosen width has enough bit patterns for every class. -/
theorem count_le_two_pow_bitCost (count : Nat) :
    count ≤ 2 ^ bitCost count := by
  cases count with
  | zero => simp [bitCost]
  | succ count =>
      cases count with
      | zero => simp [bitCost]
      | succ count =>
          have h := Nat.lt_log2_self (n := count + 1)
          simp only [bitCost]
          omega

/-- Embed an exact class index into the fixed-width bit-pattern carrier. -/
def encodeFixedWidth (complete : CompleteSpec S R) (index : ClassIndex complete) :
    Fin (2 ^ bitCost (classCount complete)) :=
  Fin.castLE (count_le_two_pow_bitCost (classCount complete)) index

theorem encodeFixedWidth_injective (complete : CompleteSpec S R) :
    Function.Injective (encodeFixedWidth complete) := by
  intro left right h
  apply Fin.ext
  exact congrArg (fun index => index.val) h

/-! Core has no `Fintype`/`Finset` dependency, so the finite pigeonhole fact
used by the lower bound is proved directly from duplicate-free bounded lists. -/

private theorem nodup_lt_length_le (bound : Nat) (values : List Nat)
    (hn : values.Nodup) (hb : ∀ value ∈ values, value < bound) :
    values.length ≤ bound := by
  induction bound generalizing values with
  | zero =>
      cases values with
      | nil => simp
      | cons value rest =>
          have := hb value (by simp)
          omega
  | succ bound ih =>
      by_cases hbound : bound ∈ values
      · have hnodup : (values.erase bound).Nodup := hn.erase bound
        have hbounded : ∀ value ∈ values.erase bound, value < bound := by
          intro value hvalue
          have hvalue' : value ∈ values := List.mem_of_mem_erase hvalue
          have hlt : value < bound + 1 := hb value hvalue'
          have hne : value ≠ bound := (hn.mem_erase_iff).mp hvalue |>.1
          omega
        have hle := ih (values.erase bound) hnodup hbounded
        rw [List.length_erase_of_mem hbound] at hle
        have hpositive : 0 < values.length := by
          cases values with
          | nil => simp at hbound
          | cons => simp
        omega
      · apply Nat.le_trans (ih values hn ?_) (Nat.le_succ bound)
        intro value hvalue
        have hlt : value < bound + 1 := hb value hvalue
        have hne : value ≠ bound := by
          intro h
          subst value
          exact hbound hvalue
        omega

private theorem nodup_finRange (n : Nat) : (List.finRange n).Nodup := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.finRange_succ, List.nodup_cons]
      constructor
      · intro hmem
        simp only [List.mem_map] at hmem
        obtain ⟨index, _, hindex⟩ := hmem
        have hval := congrArg Fin.val hindex
        simp at hval
      · exact List.Pairwise.map Fin.succ
          (fun left right hne heq => by
            apply hne
            apply Fin.ext
            have hval := congrArg Fin.val heq
            simp at hval ⊢
            exact hval) ih

/-- Finite pigeonhole, in the exact direction needed by the information bound. -/
theorem fin_card_le_of_injective {n m : Nat} (code : Fin n → Fin m)
    (hinjective : Function.Injective code) : n ≤ m := by
  let values := (List.finRange n).map (fun index => (code index).val)
  have hnodup : values.Nodup :=
    List.Pairwise.map (fun index => (code index).val)
      (fun left right hne heq => by
        apply hne
        apply hinjective
        apply Fin.ext
        exact heq)
      (nodup_finRange n)
  have hbounded : ∀ value ∈ values, value < m := by
    intro value hvalue
    simp only [values, List.mem_map] at hvalue
    obtain ⟨index, _, rfl⟩ := hvalue
    exact (code index).isLt
  have hle := nodup_lt_length_le m values hnodup hbounded
  simpa [values] using hle

/-- **The honest lower bound.** Any collision-free fixed-width encoding of
`classCount` classes into `bits` bits needs at least `classCount` distinct bit
patterns.  This says nothing about non-injective/lossy codes or unrestricted
semantic quotients. -/
theorem fixedWidth_information_lower_bound (complete : CompleteSpec S R)
    (bits : Nat) (code : ClassIndex complete → Fin (2 ^ bits))
    (hinjective : Function.Injective code) :
    classCount complete ≤ 2 ^ bits :=
  fin_card_le_of_injective code hinjective

/-! ## 4. Exact executable fixtures -/

namespace Fixtures

private theorem boolStates_complete (state : GSet Bool) :
    state ∈ ContextCompiler.Fixtures.boolStates := by
  cases hfalse : state false <;> cases htrue : state true
  · have hstate : state = ContextCompiler.Fixtures.emptyBool := by
      funext value
      cases value <;> assumption
    subst state
    simp [ContextCompiler.Fixtures.boolStates]
  · have hstate : state = JoinHom.sawB := by
      funext value
      cases value <;> assumption
    subst state
    simp [ContextCompiler.Fixtures.boolStates]
  · have hstate : state = JoinHom.sawA := by
      funext value
      cases value <;> assumption
    subst state
    simp [ContextCompiler.Fixtures.boolStates]
  · have hstate : state = ContextCompiler.Fixtures.fullBool := by
      funext value
      cases value <;> assumption
    subst state
    simp [ContextCompiler.Fixtures.boolStates]

/-- The existing complete four-state membership compiler. -/
def membership : CompleteSpec (GSet Bool) Bool where
  spec := ContextCompiler.Fixtures.membership
  states_complete := boolStates_complete
  contexts_complete := boolStates_complete

theorem membership_two_classes : classCount membership = 2 := by decide

theorem membership_one_bit : bitCost (classCount membership) = 1 := by decide

theorem membership_roundtrip (index : ClassIndex membership) :
    encodeKey membership (decodeKey membership index) = index :=
  encode_decode_index membership index

/-- A three-bit spelling of a `Fin 3` grow-only set. -/
def ofBits3 (at0 at1 at2 : Bool) : GSet (Fin 3) := fun index =>
  if index = 0 then at0 else if index = 1 then at1 else at2

/-- All eight states of `GSet (Fin 3)`, in a fixed canonical order. -/
def all3States : List (GSet (Fin 3)) :=
  [ofBits3 false false false,
   ofBits3 false false true,
   ofBits3 false true false,
   ofBits3 false true true,
   ofBits3 true false false,
   ofBits3 true false true,
   ofBits3 true true false,
   ofBits3 true true true]

private theorem ofBits3_self (state : GSet (Fin 3)) :
    state = ofBits3 (state 0) (state 1) (state 2) := by
  apply MinimalSummary.gset3_ext <;> simp [ofBits3]

theorem all3States_complete (state : GSet (Fin 3)) : state ∈ all3States := by
  rw [ofBits3_self state]
  cases state 0 <;> cases state 1 <;> cases state 2 <;> simp [all3States]

/-- The complete finite compiler for `|state| >= 2`. -/
def thresholdTwoSpec : ContextCompiler.Spec (GSet (Fin 3)) Bool where
  states := all3States
  contexts := all3States
  queries := [MinimalSummary.atLeast 2]

def thresholdTwo : CompleteSpec (GSet (Fin 3)) Bool where
  spec := thresholdTwoSpec
  states_complete := all3States_complete
  contexts_complete := all3States_complete

theorem thresholdTwo_five_classes : classCount thresholdTwo = 5 := by decide

theorem thresholdTwo_three_bits : bitCost (classCount thresholdTwo) = 3 := by decide

theorem thresholdTwo_roundtrip (index : ClassIndex thresholdTwo) :
    encodeKey thresholdTwo (decodeKey thresholdTwo index) = index :=
  encode_decode_index thresholdTwo index

/-- Same complete state list, but no future contexts.  It sees only the present
boolean answer and therefore undercounts the real contextual classes. -/
def thresholdNoContexts : ContextCompiler.Spec (GSet (Fin 3)) Bool where
  states := all3States
  contexts := []
  queries := [MinimalSummary.atLeast 2]

theorem thresholdNoContexts_collapses_to_two :
    thresholdNoContexts.classKeys.length = 2 := by decide

/-- Empty authored context coverage is rejected: this spec cannot be promoted
to the complete interface consumed by the canonical codec. -/
theorem thresholdNoContexts_refused :
    ¬ (∀ context : GSet (Fin 3), context ∈ thresholdNoContexts.contexts) := by
  intro hcomplete
  simpa [thresholdNoContexts] using hcomplete MinimalSummary.empty3

/-- The missing coverage is load-bearing: incomplete authorship reports two
classes where the complete compiler reports five. -/
theorem context_coverage_is_load_bearing :
    thresholdNoContexts.classKeys.length = 2
      ∧ classCount thresholdTwo = 5
      ∧ ¬ (∀ context : GSet (Fin 3),
        context ∈ thresholdNoContexts.contexts) :=
  ⟨thresholdNoContexts_collapses_to_two, thresholdTwo_five_classes,
    thresholdNoContexts_refused⟩

end Fixtures

end Uwueave.FiniteSummaryCodec
