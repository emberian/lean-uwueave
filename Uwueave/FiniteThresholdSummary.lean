/-
# Uwueave.FiniteThresholdSummary — the general finite threshold quotient.

For a proof-carrying finite universe, a threshold query on its grow-only set
has one class for every sub-threshold subset and one common top class, provided
the threshold is attainable and nonzero.  At threshold zero, or above the
universe cardinality, the query is constant and has one class.

The class-count formula is therefore

    1                                      if k = 0 or |U| < k
    1 + #{ A ⊆ U | |A| < k }              otherwise.

`binomialPrefix` is that finite binomial prefix, defined without Mathlib from
the repository's exact subset enumerator.  This module proves that a canonical
key list is duplicate-free, exhaustive, and classifies exactly
`MinimalSummary.CtxEquiv`; its length is the displayed formula.  The scope is
an explicit complete duplicate-free finite universe.
-/
import Uwueave.FiniteSummaryCodec
import Uwueave.FiniteProductSearch

namespace Uwueave.FiniteThresholdSummary

open Uwueave
open Uwueave.Catalog

universe u

/-- A finite universe whose enumeration is proof data, not a guessed bound. -/
structure FiniteUniverse (alpha : Type u) where
  values : List alpha
  nodup : values.Nodup
  complete : ∀ value : alpha, value ∈ values

variable {alpha : Type u} [DecidableEq alpha]

namespace FiniteUniverse

/-- The canonical ordered element list of a grow-only set. -/
def elements (U : FiniteUniverse alpha) (state : GSet alpha) : List alpha :=
  U.values.filter state

/-- Exact finite cardinality. -/
def card (U : FiniteUniverse alpha) (state : GSet alpha) : Nat :=
  (U.elements state).length

theorem card_eq_elements_length (U : FiniteUniverse alpha) (state : GSet alpha) :
    U.card state = (U.elements state).length :=
  rfl

theorem mem_elements_iff (U : FiniteUniverse alpha) (state : GSet alpha)
    (value : alpha) :
    value ∈ U.elements state ↔ state value = true := by
  simp [elements, U.complete value]

theorem elements_injective (U : FiniteUniverse alpha) :
    Function.Injective U.elements := by
  intro left right h
  funext value
  apply Bool.eq_iff_iff.mpr
  simpa [mem_elements_iff] using
    congrArg (fun values => value ∈ values) h

/-- Filtering by a stronger Boolean predicate gives a sublist of filtering by
a weaker predicate. -/
theorem filter_sublist_filter {beta : Type u} (values : List beta)
    (p q : beta → Bool)
    (h : ∀ value ∈ values, p value = true → q value = true) :
    values.filter p |>.Sublist (values.filter q) := by
  induction values with
  | nil => exact List.Sublist.slnil
  | cons head tail ih =>
      have htail : ∀ value ∈ tail, p value = true → q value = true :=
        fun value hvalue => h value (List.mem_cons_of_mem head hvalue)
      have hi := ih htail
      cases hp : p head <;> cases hq : q head
      · simpa [hp, hq] using hi
      · simpa [hp, hq] using List.Sublist.cons head hi
      · exact absurd (h head List.mem_cons_self hp) (by simp [hq])
      · simpa [hp, hq] using List.Sublist.cons_cons head hi

theorem elements_sublist_of_subset (U : FiniteUniverse alpha)
    {left right : GSet alpha}
    (h : ∀ value, left value = true → right value = true) :
    (U.elements left).Sublist (U.elements right) :=
  filter_sublist_filter U.values left right
    (fun value _ => h value)

theorem card_le_universe (U : FiniteUniverse alpha) (state : GSet alpha) :
    U.card state ≤ U.values.length := by
  rw [card_eq_elements_length]
  exact List.length_filter_le state U.values

/-- Merging can only increase finite cardinality. -/
theorem card_le_merge (U : FiniteUniverse alpha) (left context : GSet alpha) :
    U.card left ≤ U.card (left ⊔ context) := by
  rw [card_eq_elements_length, card_eq_elements_length]
  exact (elements_sublist_of_subset U (fun value hleft => by
    simp only [gset_mem_merge, hleft, Bool.true_or])).length_le

/-- A list interpreted as a grow-only set. -/
def ofList (values : List alpha) : GSet alpha :=
  fun value => decide (value ∈ values)

/-- A duplicate-free ordered sublist is recovered exactly by filtering its
parent for membership. -/
theorem filter_mem_eq_self {source chosen : List alpha}
    (hsource : source.Nodup) (hchosen : chosen.Sublist source) :
    source.filter (fun value => decide (value ∈ chosen)) = chosen := by
  induction hchosen with
  | slnil => simp
  | @cons left right head hsub ih =>
      have hn := List.nodup_cons.mp hsource
      have hhead : head ∉ left := by
        intro hmem
        exact hn.1 (List.Sublist.mem hmem hsub)
      simpa [hhead] using ih hn.2
  | @cons_cons left right head hsub ih =>
      have hn := List.nodup_cons.mp hsource
      have hpred : right.filter (fun value => decide (value ∈ head :: left)) =
          right.filter (fun value => decide (value ∈ left)) := by
        apply List.filter_congr
        intro value hvalue
        have hne : value ≠ head := by
          intro heq
          subst value
          exact hn.1 hvalue
        simp [hne]
      simp only [List.filter_cons, List.mem_cons_self, decide_true,
        if_true]
      rw [hpred, ih hn.2]

theorem elements_ofList (U : FiniteUniverse alpha) {values : List alpha}
    (hvalues : values.Sublist U.values) :
    U.elements (ofList values) = values := by
  exact filter_mem_eq_self U.nodup hvalues

theorem card_ofList (U : FiniteUniverse alpha) {values : List alpha}
    (hvalues : values.Sublist U.values) :
    U.card (ofList values) = values.length := by
  rw [card_eq_elements_length, elements_ofList U hvalues]

/-- Filtering a list by a Boolean predicate and by its complement partitions
the list's length. -/
theorem filter_lengths_add_complement {beta : Type u} (values : List beta)
    (p : beta → Bool) :
    (values.filter p).length + (values.filter fun value => !p value).length =
      values.length := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      cases hp : p head <;> simp [hp] at ih ⊢ <;> omega

theorem filter_or_length_of_disjoint {beta : Type u} (values : List beta)
    (left right : beta → Bool)
    (hdisjoint : ∀ value ∈ values,
      left value = true → right value = false) :
    (values.filter fun value => left value || right value).length =
      (values.filter left).length + (values.filter right).length := by
  induction values with
  | nil => rfl
  | cons head tail ih =>
      have htail : ∀ value ∈ tail,
          left value = true → right value = false :=
        fun value hvalue => hdisjoint value (List.mem_cons_of_mem head hvalue)
      have hi := ih htail
      have hh := hdisjoint head List.mem_cons_self
      cases hl : left head <;> cases hr : right head <;>
        simp [hl, hr] at hh hi ⊢ <;> omega

/-- Disjoint finite sets add their cardinalities. -/
theorem card_merge_of_disjoint (U : FiniteUniverse alpha)
    (left right : GSet alpha)
    (hdisjoint : ∀ value ∈ U.values,
      left value = true → right value = false) :
    U.card (left ⊔ right) = U.card left + U.card right := by
  simpa only [card, elements, gset_mem_merge] using
    filter_or_length_of_disjoint U.values left right hdisjoint

/-- The threshold observation over the finite universe. -/
def threshold (U : FiniteUniverse alpha) (k : Nat) (state : GSet alpha) : Bool :=
  decide (k ≤ U.card state)

/-- Degenerate thresholds are constant: zero is always true and a threshold
above the universe cardinality is always false. -/
def Degenerate (U : FiniteUniverse alpha) (k : Nat) : Prop :=
  k = 0 ∨ U.values.length < k

instance (U : FiniteUniverse alpha) (k : Nat) : Decidable (U.Degenerate k) :=
  inferInstanceAs (Decidable (k = 0 ∨ U.values.length < k))

theorem threshold_constant_of_degenerate (U : FiniteUniverse alpha) (k : Nat)
    (hdegenerate : U.Degenerate k) (left right : GSet alpha) :
    CtxEquiv (U.threshold k) left right := by
  rcases hdegenerate with rfl | habove
  · exact MinimalSummary.ctxEquiv_threshold_top U.card U.card_le_merge 0
      (Nat.zero_le _) (Nat.zero_le _)
  · refine ⟨?_, fun context => ?_⟩
    · simp only [threshold]
      rw [decide_eq_false (Nat.not_le_of_gt
        (Nat.lt_of_le_of_lt (U.card_le_universe left) habove)),
        decide_eq_false (Nat.not_le_of_gt
          (Nat.lt_of_le_of_lt (U.card_le_universe right) habove))]
    · simp only [threshold]
      rw [decide_eq_false (Nat.not_le_of_gt
        (Nat.lt_of_le_of_lt (U.card_le_universe (left ⊔ context)) habove)),
        decide_eq_false (Nat.not_le_of_gt
          (Nat.lt_of_le_of_lt (U.card_le_universe (right ⊔ context)) habove))]

/-- If `left` is at least as large as a distinct `right`, some element occurs
in `left` but not `right`. -/
theorem exists_left_not_right_of_card_ge (U : FiniteUniverse alpha)
    {left right : GSet alpha} (hcard : U.card right ≤ U.card left)
    (hne : left ≠ right) :
    ∃ value : alpha, left value = true ∧ right value = false := by
  apply Classical.byContradiction
  intro hnone
  have hsubset : ∀ value, left value = true → right value = true := by
    intro value hleft
    by_cases hright : right value = true
    · exact hright
    · have hfalse : right value = false := Bool.eq_false_iff.mpr hright
      exact False.elim (hnone ⟨value, hleft, hfalse⟩)
  have hsub := elements_sublist_of_subset U hsubset
  have hlength : (U.elements left).length = (U.elements right).length := by
    rw [← card_eq_elements_length, ← card_eq_elements_length]
    exact Nat.le_antisymm hsub.length_le hcard
  exact hne (U.elements_injective (hsub.eq_of_length hlength))

/-- A larger-or-equal distinct sub-threshold set can be extended to the
threshold while the other remains below it. -/
theorem separating_context_of_card_ge (U : FiniteUniverse alpha) {k : Nat}
    {left right : GSet alpha}
    (_hpositive : 0 < k) (hattainable : k ≤ U.values.length)
    (_hleft : U.card left < k) (hright : U.card right < k)
    (hcard : U.card right ≤ U.card left) (hne : left ≠ right) :
    ∃ context : GSet alpha,
      U.threshold k (left ⊔ context) = true ∧
      U.threshold k (right ⊔ context) = false := by
  obtain ⟨witness, hwLeft, hwRight⟩ :=
    U.exists_left_not_right_of_card_ge hcard hne
  let joined : GSet alpha := left ⊔ right
  let available := U.values.filter fun value => !joined value
  let needed := k - U.card joined
  let chosen := available.take needed
  let extra : GSet alpha := ofList chosen
  let context : GSet alpha := right ⊔ extra
  have hrightJoined : ∀ value, right value = true → joined value = true := by
    intro value hvalue
    simp [joined, gset_mem_merge, hvalue]
  have hrightSub := elements_sublist_of_subset U hrightJoined
  have hwJoined : joined witness = true := by
    simp [joined, gset_mem_merge, hwLeft]
  have hstrict : U.card right < U.card joined := by
    apply Nat.lt_of_le_of_ne
    · simpa [card_eq_elements_length] using hrightSub.length_le
    · intro heq
      have hlens : (U.elements right).length = (U.elements joined).length := by
        simpa [card_eq_elements_length] using heq
      have helements := hrightSub.eq_of_length hlens
      have hmem := congrArg (fun values => witness ∈ values) helements
      simp [mem_elements_iff, hwRight, hwJoined] at hmem
  have havailableLength : U.card joined + available.length = U.values.length := by
    have hcount := filter_lengths_add_complement U.values joined
    simpa [available, card, elements] using hcount
  have hneeded : needed ≤ available.length := by
    simp only [needed]
    omega
  have hchosenLength : chosen.length = needed := by
    exact List.length_take_of_le hneeded
  have hchosenSub : chosen.Sublist U.values :=
    (List.take_sublist needed available).trans List.filter_sublist
  have hcardExtra : U.card extra = chosen.length := by
    exact U.card_ofList hchosenSub
  have hdisjoint : ∀ value ∈ U.values,
      joined value = true → extra value = false := by
    intro value hvalue hjoined
    by_cases hchosen : value ∈ chosen
    · have havailable : value ∈ available :=
        List.Sublist.mem hchosen (List.take_sublist needed available)
      have hnot : (!joined value) = true := (List.mem_filter.mp havailable).2
      simp [hjoined] at hnot
    · simp [extra, ofList, hchosen]
  have hleftCard : k ≤ U.card (left ⊔ context) := by
    have hsum := U.card_merge_of_disjoint joined extra hdisjoint
    have hassoc : left ⊔ context = joined ⊔ extra := by
      simp [context, joined, merge_assoc]
    rw [hassoc, hsum, hcardExtra, hchosenLength]
    simp only [needed]
    omega
  have hrightDisjoint : ∀ value ∈ U.values,
      right value = true → extra value = false := by
    intro value hmem hvalue
    exact hdisjoint value hmem (hrightJoined value hvalue)
  have hrightCard : U.card (right ⊔ context) < k := by
    have hsum := U.card_merge_of_disjoint right extra hrightDisjoint
    have hidem : right ⊔ context = right ⊔ extra := by
      dsimp [context]
      rw [← merge_assoc, merge_idem]
    rw [hidem, hsum, hcardExtra, hchosenLength]
    simp only [needed]
    omega
  refine ⟨context, ?_, ?_⟩
  · exact decide_eq_true hleftCard
  · exact decide_eq_false (Nat.not_le_of_gt hrightCard)

/-- Below a nondegenerate threshold, distinct states are contextually
distinguishable. -/
theorem not_ctxEquiv_of_below_ne (U : FiniteUniverse alpha) {k : Nat}
    (hpositive : 0 < k) (hattainable : k ≤ U.values.length)
    {left right : GSet alpha} (hleft : U.card left < k)
    (hright : U.card right < k) (hne : left ≠ right) :
    ¬ CtxEquiv (U.threshold k) left right := by
  rcases Nat.le_total (U.card left) (U.card right) with hle | hge
  · obtain ⟨context, hy, hx⟩ := U.separating_context_of_card_ge
      hpositive hattainable hright hleft hle (Ne.symm hne)
    intro hequiv
    exact Bool.noConfusion (hy.symm.trans ((hequiv.2 context).symm.trans hx))
  · obtain ⟨context, hx, hy⟩ := U.separating_context_of_card_ge
      hpositive hattainable hleft hright hge hne
    intro hequiv
    exact Bool.noConfusion (hx.symm.trans ((hequiv.2 context).trans hy))

/-- Canonical semantic key: one key per below-threshold set and `none` for the
common top. Degenerate constant queries also use the single `none` key. -/
def classKey (U : FiniteUniverse alpha) (k : Nat) (state : GSet alpha) :
    Option (List alpha) :=
  if U.Degenerate k then none
  else if k ≤ U.card state then none
  else some (U.elements state)

/-- The key is exactly contextual equivalence. -/
theorem ctxEquiv_iff_classKey_eq (U : FiniteUniverse alpha) (k : Nat)
    (left right : GSet alpha) :
    CtxEquiv (U.threshold k) left right ↔
      U.classKey k left = U.classKey k right := by
  by_cases hdegenerate : U.Degenerate k
  · simp only [classKey, if_pos hdegenerate]
    exact iff_true_intro (U.threshold_constant_of_degenerate k hdegenerate left right)
  · have hpositive : 0 < k := by
      have : k ≠ 0 := fun hk => hdegenerate (Or.inl hk)
      omega
    have hattainable : k ≤ U.values.length := by
      have : ¬ U.values.length < k := fun h => hdegenerate (Or.inr h)
      omega
    simp only [classKey, if_neg hdegenerate]
    by_cases hleft : k ≤ U.card left <;>
      by_cases hright : k ≤ U.card right
    · simp only [if_pos hleft, if_pos hright]
      exact iff_true_intro
        (MinimalSummary.ctxEquiv_threshold_top U.card U.card_le_merge k hleft hright)
    · rw [if_pos hleft, if_neg hright]
      constructor
      intro hequiv
      have hpresent := hequiv.1
      simp [threshold, decide_eq_true hleft,
        decide_eq_false (Nat.not_le_of_gt (Nat.lt_of_not_ge hright))] at hpresent
      intro hfalse
      exact False.elim (Option.some_ne_none _ hfalse.symm)
    · rw [if_neg hleft, if_pos hright]
      constructor
      intro hequiv
      have hpresent := hequiv.1
      simp [threshold, decide_eq_true hright,
        decide_eq_false (Nat.not_le_of_gt (Nat.lt_of_not_ge hleft))] at hpresent
      intro hfalse
      exact False.elim (Option.some_ne_none _ hfalse)
    · simp only [if_neg hleft, if_neg hright, Option.some.injEq]
      constructor
      · intro hequiv
        apply Classical.byContradiction
        intro hne
        exact U.not_ctxEquiv_of_below_ne hpositive hattainable
          (Nat.lt_of_not_ge hleft) (Nat.lt_of_not_ge hright)
          (fun heq => hne (congrArg U.elements heq)) hequiv
      · intro helements
        have heq := U.elements_injective helements
        subst right
        exact ctxEquiv_refl _ _

/-- The finite binomial prefix `sum_{i < k} choose(|U|, i)`, represented by
the exact subset enumeration available in Lean core. -/
def binomialPrefix (U : FiniteUniverse alpha) (k : Nat) : Nat :=
  (FiniteProductSearch.subsets U.values |>.filter
    (fun choice => decide (choice.length < k))).length

/-- The cardinality formula. -/
def thresholdClassCount (U : FiniteUniverse alpha) (k : Nat) : Nat :=
  if U.Degenerate k then 1 else U.binomialPrefix k + 1

/-- Canonical representatives of every key. -/
def classKeys (U : FiniteUniverse alpha) (k : Nat) :
    List (Option (List alpha)) :=
  if U.Degenerate k then [none]
  else none ::
    ((FiniteProductSearch.subsets U.values).filter
      (fun choice => decide (choice.length < k))).map some

theorem classKeys_length_formula (U : FiniteUniverse alpha) (k : Nat) :
    (U.classKeys k).length = U.thresholdClassCount k := by
  by_cases h : U.Degenerate k <;>
    simp [classKeys, thresholdClassCount, binomialPrefix, h]

/-- The same formula with the finite binomial prefix exposed: one class for a
constant query, otherwise one top class plus every subset of size below the
threshold. -/
theorem classKeys_length_explicit (U : FiniteUniverse alpha) (k : Nat) :
    (U.classKeys k).length =
      if U.Degenerate k then 1
      else
        ((FiniteProductSearch.subsets U.values).filter
          (fun choice => decide (choice.length < k))).length + 1 := by
  simpa [thresholdClassCount, binomialPrefix] using U.classKeys_length_formula k

theorem subsets_nodup_of_nodup {source : List alpha} (hsource : source.Nodup) :
    (FiniteProductSearch.subsets source).Nodup := by
  induction source with
  | nil => simp [FiniteProductSearch.subsets]
  | cons head tail ih =>
      have hn := List.nodup_cons.mp hsource
      have htail := ih hn.2
      rw [FiniteProductSearch.subsets, List.nodup_append]
      refine ⟨htail, ?_, ?_⟩
      · exact List.Pairwise.map (fun choice => head :: choice)
          (fun left right hne heq => hne (List.cons.inj heq).2) htail
      · intro left hleft right hright heq
        obtain ⟨choice, hchoice, rfl⟩ := List.mem_map.mp hright
        have hheadLeft : head ∈ left := by
          rw [heq]
          exact List.mem_cons_self
        have hsub : left.Sublist tail :=
          FiniteProductSearch.mem_subsets_iff_sublist.mp hleft
        exact hn.1 (List.Sublist.mem hheadLeft hsub)

theorem classKeys_nodup (U : FiniteUniverse alpha) (k : Nat) :
    (U.classKeys k).Nodup := by
  by_cases hdegenerate : U.Degenerate k
  · simp [classKeys, hdegenerate]
  · have hsubsets := subsets_nodup_of_nodup U.nodup
    have hfiltered :
        ((FiniteProductSearch.subsets U.values).filter
          (fun choice => decide (choice.length < k))).Nodup :=
      List.Pairwise.filter _ hsubsets
    have hmapped :
        (((FiniteProductSearch.subsets U.values).filter
          (fun choice => decide (choice.length < k))).map some).Nodup :=
      List.Pairwise.map some
        (fun left right hne heq => hne (Option.some.inj heq)) hfiltered
    simp [classKeys, hdegenerate, hmapped]

/-- Every semantic class key occurs in the canonical key list. -/
theorem classKey_mem (U : FiniteUniverse alpha) (k : Nat) (state : GSet alpha) :
    U.classKey k state ∈ U.classKeys k := by
  by_cases hdegenerate : U.Degenerate k
  · simp [classKey, classKeys, hdegenerate]
  · by_cases htop : k ≤ U.card state
    · simp [classKey, classKeys, hdegenerate, htop]
    · have hsub : (U.elements state).Sublist U.values := List.filter_sublist
      have hsubset : U.elements state ∈
          FiniteProductSearch.subsets U.values :=
        FiniteProductSearch.mem_subsets_iff_sublist.mpr hsub
      have hbelow : (U.elements state).length < k := by
        rw [← card_eq_elements_length]
        exact Nat.lt_of_not_ge htop
      rw [classKey, if_neg hdegenerate, if_neg htop,
        classKeys, if_neg hdegenerate]
      exact List.mem_cons_of_mem none (List.mem_map.mpr
        ⟨U.elements state,
          List.mem_filter.mpr ⟨hsubset, decide_eq_true hbelow⟩, rfl⟩)

/-- No key is invented: each key has a grow-only-set representative. -/
theorem mem_classKeys_iff (U : FiniteUniverse alpha) (k : Nat)
    (key : Option (List alpha)) :
    key ∈ U.classKeys k ↔ ∃ state : GSet alpha, U.classKey k state = key := by
  constructor
  · intro hkey
    by_cases hdegenerate : U.Degenerate k
    · simp [classKeys, hdegenerate] at hkey
      subst key
      exact ⟨fun _ => false, by simp [classKey, hdegenerate]⟩
    · simp only [classKeys, hdegenerate, if_false, List.mem_cons,
        List.mem_map] at hkey
      rcases hkey with rfl | ⟨choice, hchoice, rfl⟩
      · have hpositive : 0 < k := by
          have : k ≠ 0 := fun hk => hdegenerate (Or.inl hk)
          omega
        let full : GSet alpha := fun _ => true
        have htop : k ≤ U.card full := by
          have hcard : U.card full = U.values.length := by
            simp [card, elements, full]
          rw [hcard]
          have : ¬ U.values.length < k := fun h => hdegenerate (Or.inr h)
          omega
        exact ⟨full, by simp [classKey, hdegenerate, htop]⟩
      · have hmem := List.mem_filter.mp hchoice
        have hsub := FiniteProductSearch.mem_subsets_iff_sublist.mp hmem.1
        have helements := U.elements_ofList hsub
        have hcard := U.card_ofList hsub
        have hbelow : ¬ k ≤ U.card (ofList choice) := by
          rw [hcard]
          exact Nat.not_le_of_gt (of_decide_eq_true hmem.2)
        exact ⟨ofList choice, by
          simp [classKey, hdegenerate, hbelow, helements]⟩
  · rintro ⟨state, rfl⟩
    exact U.classKey_mem k state

/-- The duplicate-free exhaustive key list is an exact finite presentation of
the contextual quotient, and its cardinality is the formula above. -/
theorem threshold_quotient_class_count_formula (U : FiniteUniverse alpha)
    (k : Nat) :
    (U.classKeys k).Nodup ∧
      (∀ left right : GSet alpha,
        CtxEquiv (U.threshold k) left right ↔
          U.classKey k left = U.classKey k right) ∧
      (∀ key, key ∈ U.classKeys k ↔
        ∃ state : GSet alpha, U.classKey k state = key) ∧
      (U.classKeys k).length = U.thresholdClassCount k :=
  ⟨U.classKeys_nodup k, U.ctxEquiv_iff_classKey_eq k,
    U.mem_classKeys_iff k, U.classKeys_length_formula k⟩

end FiniteUniverse

/-! Exact corollaries for the previously exhibited two- and five-class poles. -/

private theorem finRange_nodup (n : Nat) : (List.finRange n).Nodup := by
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
            simp at hval
            exact hval) ih

def finUniverse (n : Nat) : FiniteUniverse (Fin n) where
  values := List.finRange n
  nodup := finRange_nodup n
  complete := List.mem_finRange

theorem two_class_corollary : (finUniverse 2).thresholdClassCount 1 = 2 := by
  rfl

theorem five_class_corollary : (finUniverse 3).thresholdClassCount 2 = 5 := by
  rfl

theorem existing_counts_are_corollaries :
    (finUniverse 2).thresholdClassCount 1 =
        FiniteSummaryCodec.classCount FiniteSummaryCodec.Fixtures.membership ∧
      (finUniverse 3).thresholdClassCount 2 =
        FiniteSummaryCodec.classCount FiniteSummaryCodec.Fixtures.thresholdTwo := by
  exact ⟨two_class_corollary.trans
      FiniteSummaryCodec.Fixtures.membership_two_classes.symm,
    five_class_corollary.trans
      FiniteSummaryCodec.Fixtures.thresholdTwo_five_classes.symm⟩

end Uwueave.FiniteThresholdSummary
