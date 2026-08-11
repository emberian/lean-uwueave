/-
# Uwueave.ExecRefine — proofs about the kernel's decision layer.

`Uwueave/Exec.lean` factors the replay as decode → `absReplay` → encode, so the
byte layer needs no theorem — it is a composition. This file proves the facts
that are *not* free:

  1. **General acyclicity** (`absReplay_acyclic`, `absReplay_terminates`,
     `absReplay_chain_nodup`): if the structural first-parent base is grounded
     (some rank strictly descends along it — the shape content-addressing gives
     for free, `Uwueave.Acyclicity`), then after replaying *any* op array the
     effective-parent relation has no cycle: every override chain terminates at
     root without revisiting a node. This generalizes `Move.miniInterp_acyclic`
     from the 2-op miniature to the real kernel, for all inputs.

  2. **Fuel adequacy** (`chainHits_decides`): on a terminating view over `n`
     live indices, fuel `n + 1` is enough for `chainHits` to *decide* chain
     membership — exhaustion never masquerades as "misses". This is the lemma
     that makes `applyOp`'s cycle check meaningful, and it is what the
     preservation argument consumes: an op is applied only when the
     destination's chain provably misses the child.

  3. **Codec, word level** (`getWord_pushWord`, `getWord_encodeView`,
     `toI_ofI`, `decode_encode_id`): a pushed word reads back exactly, earlier
     words are undisturbed, and the i64 two's-complement round trip is the
     identity on the range the kernel produces.

No `sorry`, no `native_decide`, no `#guard`; axioms of every keystone are
within `{propext, Classical.choice, Quot.sound}`.
-/
import Uwueave.Exec

namespace Uwueave.Exec

/-! ## §1. The effective-parent relation, as Props

`chainHits` is a fueled Bool computation; these are the Props it computes.
Everything is stated against `effParent`, the exact function the kernel steps
through. -/

/-- One effective-parent step, as a partial function: `some p` iff `i`'s
effective parent is node `p`, `none` iff `i` is (effectively) at root. -/
def parentOf (fp ov : Array Int) (i : Nat) : Option Nat :=
  if effParent fp ov i < 0 then none else some (effParent fp ov i).toNat

/-- The effective-ancestor chain from `start` passes through `needle`
(in ≥ 0 steps) — the Prop `chainHits fp ov start needle` computes. The
`needle` is the family's parameter, `start` the varying index, so this reads
`Hits fp ov needle start`. -/
inductive Hits (fp ov : Array Int) (needle : Nat) : Nat → Prop where
  | refl : Hits fp ov needle needle
  | step {i p : Nat} :
      parentOf fp ov i = some p → Hits fp ov needle p → Hits fp ov needle i

/-- Proper reachability (≥ 1 step) along effective parents. -/
inductive Reaches (fp ov : Array Int) : Nat → Nat → Prop where
  | parent {i p : Nat} : parentOf fp ov i = some p → Reaches fp ov i p
  | trans {i p j : Nat} :
      parentOf fp ov i = some p → Reaches fp ov p j → Reaches fp ov i j

/-- The chain from `i` reaches root. -/
inductive Terminates (fp ov : Array Int) : Nat → Prop where
  | root {i : Nat} : parentOf fp ov i = none → Terminates fp ov i
  | step {i p : Nat} :
      parentOf fp ov i = some p → Terminates fp ov p → Terminates fp ov i

/-- Depth-bounded termination: the chain from `i` reaches root in ≤ `k` steps. -/
inductive TermIn (fp ov : Array Int) : Nat → Nat → Prop where
  | root {k i : Nat} : parentOf fp ov i = none → TermIn fp ov k i
  | step {k i p : Nat} :
      parentOf fp ov i = some p → TermIn fp ov k p → TermIn fp ov (k + 1) i

/-- The full chain from `i`, as a list — `i` first, the root-end node last. -/
inductive ChainTo (fp ov : Array Int) : Nat → List Nat → Prop where
  | root {i : Nat} : parentOf fp ov i = none → ChainTo fp ov i [i]
  | step {i p : Nat} {l : List Nat} :
      parentOf fp ov i = some p → ChainTo fp ov p l → ChainTo fp ov i (i :: l)

/-- Characterization: no parent ↔ the effective parent is negative. -/
theorem parentOf_eq_none_iff {fp ov : Array Int} {i : Nat} :
    parentOf fp ov i = none ↔ effParent fp ov i < 0 := by
  unfold parentOf
  split <;> simp_all

/-- Characterization: a parent ↔ the effective parent is the (nonneg) index. -/
theorem parentOf_eq_some_iff {fp ov : Array Int} {i p : Nat} :
    parentOf fp ov i = some p ↔
      0 ≤ effParent fp ov i ∧ (effParent fp ov i).toNat = p := by
  unfold parentOf
  split
  · rename_i hlt
    constructor
    · intro hh; cases hh
    · intro ⟨h0, _⟩; omega
  · rename_i hlt
    constructor
    · intro hh; injection hh with he; exact ⟨by omega, he⟩
    · intro ⟨_, he⟩; rw [he]

/-! ## §2. Basic structure -/

/-- Append one step at the root end of a reachability path. -/
theorem Reaches.snoc {fp ov : Array Int} {a b c : Nat}
    (h : Reaches fp ov a b) (hbc : parentOf fp ov b = some c) :
    Reaches fp ov a c := by
  induction h with
  | parent hp => exact .trans hp (.parent hbc)
  | trans hp _ ih => exact .trans hp (ih hbc)

/-- A terminating node is on no cycle. -/
theorem Terminates.not_reaches_self {fp ov : Array Int} {v : Nat}
    (h : Terminates fp ov v) : ¬ Reaches fp ov v v := by
  induction h with
  | root hr =>
    intro hcyc
    cases hcyc with
    | parent hp => rw [hr] at hp; cases hp
    | trans hp _ => rw [hr] at hp; cases hp
  | step hp _ ih =>
    intro hcyc
    cases hcyc with
    | parent hp' =>
      rw [hp] at hp'
      injection hp' with he
      subst he
      exact ih (.parent hp)
    | trans hp' hr =>
      rw [hp] at hp'
      injection hp' with he
      subst he
      exact ih (hr.snoc hp)

/-- A hit is either the start itself or proper reachability. -/
theorem Hits.eq_or_reaches {fp ov : Array Int} {needle start : Nat}
    (h : Hits fp ov needle start) :
    start = needle ∨ Reaches fp ov start needle := by
  induction h with
  | refl => exact .inl rfl
  | step hp _ ih =>
    cases ih with
    | inl he => exact .inr (he ▸ .parent hp)
    | inr hr => exact .inr (.trans hp hr)

/-- Depth bounds weaken. -/
theorem TermIn.mono {fp ov : Array Int} {k k' i : Nat}
    (h : TermIn fp ov k i) (hk : k ≤ k') : TermIn fp ov k' i := by
  induction h generalizing k' with
  | root hr => exact .root hr
  | step hp _ ih =>
    have hk' : k' = (k' - 1) + 1 := by omega
    rw [hk']
    exact .step hp (ih (by omega))

/-- Termination yields an explicit chain. -/
theorem Terminates.chainTo {fp ov : Array Int} {i : Nat}
    (h : Terminates fp ov i) : ∃ l, ChainTo fp ov i l := by
  induction h with
  | root hr => exact ⟨_, .root hr⟩
  | step hp _ ih =>
    obtain ⟨l, hl⟩ := ih
    exact ⟨_, .step hp hl⟩

/-- Chains are nonempty. -/
theorem ChainTo.ne_nil {fp ov : Array Int} {i : Nat} {l : List Nat}
    (h : ChainTo fp ov i l) : l ≠ [] := by
  cases h <;> simp

/-- Everything on the chain from `s` is hit by the chain from `s`. -/
theorem ChainTo.hits_of_mem {fp ov : Array Int} {s : Nat} {l : List Nat}
    (h : ChainTo fp ov s l) : ∀ j ∈ l, Hits fp ov j s := by
  induction h with
  | root _ =>
    intro j hj
    rw [List.mem_singleton] at hj
    exact hj ▸ .refl
  | step hp _ ih =>
    intro j hj
    rcases List.mem_cons.mp hj with he | hm
    · exact he ▸ .refl
    · exact .step hp (ih j hm)

/-- On an acyclic view, the chain visits no node twice. -/
theorem ChainTo.nodup {fp ov : Array Int} {s : Nat} {l : List Nat}
    (hacyc : ∀ v, ¬ Reaches fp ov v v) (h : ChainTo fp ov s l) : l.Nodup := by
  induction h with
  | root _ => simp
  | @step i p l' hp hc ih =>
    rw [List.nodup_cons]
    refine ⟨fun hmem => ?_, ih⟩
    rcases (hc.hits_of_mem i hmem).eq_or_reaches with he | hr
    · rw [he] at hp
      exact hacyc i (.parent hp)
    · exact hacyc i (.trans hp hr)

/-- The chain splits as live nodes followed by the root-end node. -/
theorem ChainTo.split_last {fp ov : Array Int} {i : Nat} {l : List Nat}
    (h : ChainTo fp ov i l) :
    ∃ l₁ x, l = l₁ ++ [x] ∧ ∀ j ∈ l₁, parentOf fp ov j ≠ none := by
  induction h with
  | root _ => exact ⟨[], _, rfl, by simp⟩
  | step hp _ ih =>
    obtain ⟨l₁, x, hl, hlive⟩ := ih
    refine ⟨_ :: l₁, x, by rw [hl]; rfl, ?_⟩
    intro j hj
    rcases List.mem_cons.mp hj with he | hm
    · subst he; rw [hp]; simp
    · exact hlive j hm

/-- A chain of `k` nodes bounds the termination depth by `k - 1`. -/
theorem ChainTo.termIn {fp ov : Array Int} {i : Nat} {l : List Nat}
    (h : ChainTo fp ov i l) : TermIn fp ov (l.length - 1) i := by
  induction h with
  | root hr => exact .root hr
  | @step i p l' hp hc ih =>
    have hpos : 0 < l'.length := List.length_pos_iff.mpr hc.ne_nil
    have hstep : TermIn fp ov (l'.length - 1 + 1) i := .step hp ih
    rw [Nat.sub_add_cancel hpos] at hstep
    simpa using hstep

/-! ## §3. Liveness bound and pigeonhole -/

private theorem getD_oob {a : Array Int} {i : Nat} {d : Int}
    (h : a.size ≤ i) : a.getD i d = d := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]
  rfl

/-- Out-of-range indices are effectively at root: with an `n`-sized base and
view, every live index (one with an effective parent) is `< n`. -/
theorem lt_of_parentOf_ne_none {fp ov : Array Int} {n : Nat}
    (hfp : fp.size = n) (hov : ov.size = n) {i : Nat}
    (h : parentOf fp ov i ≠ none) : i < n := by
  rcases Nat.lt_or_ge i n with hlt | hge
  · exact hlt
  · exfalso
    apply h
    have h1 : ov.getD i (-2) = -2 := getD_oob (by omega)
    have h2 : fp.getD i (-1) = -1 := getD_oob (by omega)
    simp [parentOf, effParent, h1, h2]

/-- Pigeonhole: a duplicate-free list of naturals `< n` has at most `n`
elements. -/
theorem length_le_of_nodup_of_lt {n : Nat} :
    ∀ {l : List Nat}, l.Nodup → (∀ x ∈ l, x < n) → l.length ≤ n := by
  induction n with
  | zero =>
    intro l _ hb
    match l with
    | [] => simp
    | x :: _ => exact absurd (hb x (List.mem_cons_self)) (Nat.not_lt_zero x)
  | succ n ih =>
    intro l hd hb
    by_cases hn : n ∈ l
    · have hlen : (l.erase n).length = l.length - 1 :=
        List.length_erase_of_mem hn
      have hle : (l.erase n).length ≤ n := by
        refine ih (hd.erase n) fun x hx => ?_
        rw [hd.erase_eq_filter n] at hx
        have hmem := List.mem_filter.mp hx
        have hxl := hb x hmem.1
        have hxn : x ≠ n := by simpa using hmem.2
        omega
      have hpos : 0 < l.length := List.length_pos_iff.mpr (by rintro rfl; simp at hn)
      omega
    · refine Nat.le_succ_of_le (ih hd fun x hx => ?_)
      have := hb x hx
      have hxn : x ≠ n := fun he => hn (he ▸ hx)
      omega

/-- **Depth bound**: on a terminating view whose live indices sit below `n`,
every chain reaches root within `n` steps — the chain's live prefix visits
distinct indices `< n`, so it cannot be longer than `n`. -/
theorem termIn_of_terminates {fp ov : Array Int} {n : Nat}
    (hfp : fp.size = n) (hov : ov.size = n)
    (hall : ∀ i, Terminates fp ov i) : ∀ i, TermIn fp ov n i := by
  have hacyc : ∀ v, ¬ Reaches fp ov v v := fun v => (hall v).not_reaches_self
  intro i
  obtain ⟨l, hchain⟩ := (hall i).chainTo
  obtain ⟨l₁, x, hsplit, hlive⟩ := hchain.split_last
  have hnd : l.Nodup := hchain.nodup hacyc
  have hnd₁ : l₁.Nodup := by
    rw [hsplit] at hnd
    exact (List.sublist_append_left l₁ [x]).nodup hnd
  have hbound : ∀ j ∈ l₁, j < n := fun j hj =>
    lt_of_parentOf_ne_none hfp hov (hlive j hj)
  have hlen : l₁.length ≤ n := length_le_of_nodup_of_lt hnd₁ hbound
  refine hchain.termIn.mono ?_
  rw [hsplit]
  simp only [List.length_append, List.length_cons, List.length_nil]
  omega

/-! ## §4. Fuel adequacy: `chainHits` decides `Hits` -/

/-- **Fuel adequacy, exactly aligned with the recursion**: if the chain from
`start` reaches root within `k` steps, then fuel `k + 1` is enough for
`chainHits` to compute the truth of `Hits` — in particular exhaustion cannot
produce a wrong `false`. -/
theorem chainHits_iff_of_termIn {fp ov : Array Int} {k start : Nat}
    (h : TermIn fp ov k start) (needle : Nat) :
    (chainHits fp ov start needle (k + 1) = true ↔ Hits fp ov needle start) := by
  induction h with
  | @root k i hr =>
    rw [chainHits]
    by_cases hsn : i = needle
    · subst hsn
      simp [Hits.refl]
    · rw [if_neg (by simpa using hsn), if_pos (parentOf_eq_none_iff.mp hr)]
      constructor
      · intro hfalse; cases hfalse
      · intro hh
        cases hh with
        | refl => exact absurd rfl hsn
        | step hp _ => rw [hr] at hp; cases hp
  | @step k i p hp ht ih =>
    rw [chainHits]
    by_cases hsn : i = needle
    · subst hsn
      simp [Hits.refl]
    · obtain ⟨hpos, htn⟩ := parentOf_eq_some_iff.mp hp
      rw [if_neg (by simpa using hsn), if_neg (by omega), htn, ih]
      constructor
      · exact fun hh => .step hp hh
      · intro hh
        cases hh with
        | refl => exact absurd rfl hsn
        | @step _ p' hp' hh' =>
          rw [hp] at hp'
          injection hp' with he
          rw [he]
          exact hh'

/-- **The fuel the kernel actually passes suffices.** On a terminating view of
size `n` (base and view), `chainHits` at fuel `n + 1` — the literal fuel in
`applyOp` — decides chain membership. -/
theorem chainHits_decides {fp ov : Array Int} {n : Nat}
    (hfp : fp.size = n) (hov : ov.size = n)
    (hall : ∀ i, Terminates fp ov i) (start needle : Nat) :
    (chainHits fp ov start needle (n + 1) = true ↔ Hits fp ov needle start) :=
  chainHits_iff_of_termIn (termIn_of_terminates hfp hov hall start) needle

/-! ## §5. Preservation: `applyOp` keeps the view terminating -/

private theorem getD_set!_ne {a : Array Int} {c i : Nat} {v d : Int}
    (h : i ≠ c) : (a.set! c v).getD i d = a.getD i d := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
      Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds,
      if_neg (fun hh => h hh.symm)]

private theorem getD_set!_self {a : Array Int} {c : Nat} {v d : Int}
    (h : c < a.size) : (a.set! c v).getD c d = v := by
  rw [Array.set!_eq_setIfInBounds, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds, if_pos rfl, if_pos h]
  rfl

theorem effParent_set!_ne {fp ov : Array Int} {c : Nat} {v : Int} {i : Nat}
    (h : i ≠ c) : effParent fp (ov.set! c v) i = effParent fp ov i := by
  unfold effParent
  rw [getD_set!_ne h]

theorem effParent_set!_self {fp ov : Array Int} {c : Nat} {v : Int}
    (hc : c < ov.size) (hv : v ≠ -2) :
    effParent fp (ov.set! c v) c = v := by
  unfold effParent
  rw [getD_set!_self hc]
  simp [hv]

theorem parentOf_set!_ne {fp ov : Array Int} {c : Nat} {v : Int} {i : Nat}
    (h : i ≠ c) : parentOf fp (ov.set! c v) i = parentOf fp ov i := by
  unfold parentOf
  rw [effParent_set!_ne h]

theorem parentOf_set!_self {fp ov : Array Int} {c : Nat} {v : Int}
    (hc : c < ov.size) (hv : v ≠ -2) :
    parentOf fp (ov.set! c v) c = (if v < 0 then none else some v.toNat) := by
  unfold parentOf
  rw [effParent_set!_self hc hv]

/-- **Chains that miss the overwritten child are untouched.** -/
theorem Terminates.set!_of_not_hits {fp ov : Array Int} {c : Nat} {v : Int}
    {j : Nat} (ht : Terminates fp ov j) (hmiss : ¬ Hits fp ov c j) :
    Terminates fp (ov.set! c v) j := by
  revert hmiss
  induction ht with
  | @root i hr =>
    intro hmiss
    have hne : i ≠ c := fun e => hmiss (by rw [e]; exact .refl)
    exact .root ((parentOf_set!_ne hne).trans hr)
  | @step i p hp _ ih =>
    intro hmiss
    have hne : i ≠ c := fun e => hmiss (by rw [e]; exact .refl)
    exact .step ((parentOf_set!_ne hne).trans hp)
      (ih fun hh => hmiss (.step hp hh))

/-- Once the overwritten child itself terminates, everything does: chains
follow their old steps until they hit the child, then borrow its termination. -/
theorem terminates_set!_all {fp ov : Array Int} {c : Nat} {v : Int}
    (hall : ∀ i, Terminates fp ov i)
    (hc : Terminates fp (ov.set! c v) c) :
    ∀ i, Terminates fp (ov.set! c v) i := by
  intro i
  induction hall i with
  | @root i' hr =>
    by_cases hic : i' = c
    · rw [hic]; exact hc
    · exact .root ((parentOf_set!_ne hic).trans hr)
  | @step i' p hp _ ih =>
    by_cases hic : i' = c
    · rw [hic]; exact hc
    · exact .step ((parentOf_set!_ne hic).trans hp) ih

/-- Overriding to root (`-1`) can only truncate chains. -/
theorem terminates_set!_root {fp ov : Array Int} {c : Nat}
    (hc : c < ov.size) (hall : ∀ i, Terminates fp ov i) :
    ∀ i, Terminates fp (ov.set! c (-1)) i := by
  refine terminates_set!_all hall (.root ?_)
  rw [parentOf_set!_self hc (by omega), if_pos (by omega)]

/-- Re-pointing `c` under `dst` preserves termination, provided the (old)
chain from `dst` misses `c` — exactly what the kernel's cycle check
establishes before it applies an op. -/
theorem terminates_set!_dest {fp ov : Array Int} {c : Nat} {dst : Int}
    (hc : c < ov.size) (hdst : 0 ≤ dst)
    (hall : ∀ i, Terminates fp ov i)
    (hmiss : ¬ Hits fp ov c dst.toNat) :
    ∀ i, Terminates fp (ov.set! c dst) i := by
  refine terminates_set!_all hall (.step (p := dst.toNat) ?_ ?_)
  · rw [parentOf_set!_self hc (by omega), if_neg (by omega)]
  · exact (hall dst.toNat).set!_of_not_hits hmiss

theorem size_applyOp (fp : Array Int) (n : Nat) (ov : Array Int) (op : Op) :
    (applyOp fp n ov op).size = ov.size := by
  simp only [applyOp]
  repeat' split
  all_goals simp [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

/-- **The preservation theorem**: one `applyOp` step keeps every chain
terminating. The interesting branch converts the kernel's `chainHits … = false`
verdict — meaningful by fuel adequacy — into the miss hypothesis the
re-pointing lemma needs. -/
theorem terminates_applyOp {fp : Array Int} {n : Nat} {ov : Array Int}
    (hfp : fp.size = n) (hov : ov.size = n)
    (hall : ∀ i, Terminates fp ov i) (op : Op) :
    ∀ i, Terminates fp (applyOp fp n ov op) i := by
  intro i
  simp only [applyOp]
  split
  · exact hall i
  · split
    · rename_i hchild _
      exact terminates_set!_root (by omega) hall i
    · split
      · exact hall i
      · split
        · exact hall i
        · split
          · exact hall i
          · rename_i hchild hne1 hnneg hd hmiss
            have hdst : 0 ≤ op.dest := by omega
            refine terminates_set!_dest (by omega) hdst hall ?_ i
            intro hh
            exact hmiss ((chainHits_decides hfp hov hall _ _).mpr hh)

/-! ## §5b. The fold, the grounded base, and the main theorems -/

/-- **Groundedness of the structural base** — the hypothesis the weave's
content-addressing supplies (`Uwueave.Acyclicity`, "where a real system gets
`rank`"): some rank strictly descends along every present first-parent edge.
Stated over `getD` so it constrains exactly the in-range entries (out of
range, `getD` is `-1` and the hypothesis is vacuous). -/
def GroundedBase (r : Nat → Nat) (fp : Array Int) : Prop :=
  ∀ i : Nat, 0 ≤ fp.getD i (-1) → r (fp.getD i (-1)).toNat < r i

/-- Before any op is applied (all overrides `-2`), the effective parent *is*
the structural parent. -/
theorem effParent_replicate {fp : Array Int} {n i : Nat} :
    effParent fp (Array.replicate n (-2)) i = fp.getD i (-1) := by
  unfold effParent
  have h : (Array.replicate n (-2) : Array Int).getD i (-2) = -2 := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  rw [h]
  simp

/-- A grounded base terminates before any op is applied: rank descent is a
termination measure. -/
theorem terminates_replicate {fp : Array Int} {n : Nat} {r : Nat → Nat}
    (hg : GroundedBase r fp) :
    ∀ i, Terminates fp (Array.replicate n (-2)) i := by
  have key : ∀ k i, r i < k → Terminates fp (Array.replicate n (-2)) i := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
      intro i hik
      by_cases hp : fp.getD i (-1) < 0
      · refine .root ?_
        rw [parentOf_eq_none_iff, effParent_replicate]
        exact hp
      · have h0 : 0 ≤ fp.getD i (-1) := by omega
        refine .step (p := (fp.getD i (-1)).toNat) ?_
          (ih _ (by have := hg i h0; omega))
        rw [parentOf_eq_some_iff, effParent_replicate]
        exact ⟨h0, rfl⟩
  exact fun i => key (r i + 1) i (Nat.lt_succ_self _)

private theorem terminates_foldl {fp : Array Int} {n : Nat} (hfp : fp.size = n) :
    ∀ (l : List Op) (ov : Array Int), ov.size = n → (∀ i, Terminates fp ov i) →
      ∀ i, Terminates fp (l.foldl (applyOp fp n) ov) i := by
  intro l
  induction l with
  | nil => exact fun ov _ hall => hall
  | cons op t ih =>
    intro ov hov hall
    exact ih _ ((size_applyOp ..).trans hov) (terminates_applyOp hfp hov hall op)

private theorem size_foldl_applyOp {fp : Array Int} {n : Nat} :
    ∀ (l : List Op) (ov : Array Int), (l.foldl (applyOp fp n) ov).size = ov.size := by
  intro l
  induction l with
  | nil => exact fun _ => rfl
  | cons op t ih =>
    intro ov
    rw [List.foldl_cons, ih, size_applyOp]

/-- The decision layer never changes the view's length (no hypotheses — this
holds on an ungrounded base too). -/
theorem size_absReplay (fp : Array Int) (ops : Array Op) :
    (absReplay fp ops).size = fp.size := by
  simp only [absReplay]
  rw [← Array.foldl_toList, size_foldl_applyOp, Array.size_replicate]

/-- **Every chain of the replayed view reaches root** (grounded base ⇒
terminating view, for any op array — order, duplication and content of the
ops are unconstrained). -/
theorem absReplay_terminates (fp : Array Int) (ops : Array Op)
    (r : Nat → Nat) (hg : GroundedBase r fp) :
    ∀ i, Terminates fp (absReplay fp ops) i := by
  simp only [absReplay]
  rw [← Array.foldl_toList]
  exact terminates_foldl rfl _ _ (Array.size_replicate ..)
    (terminates_replicate hg)

/-- **The general acyclicity theorem** — `Move.miniInterp_acyclic`, but for
the real kernel and all inputs: on a grounded base, the effective-parent
relation after replaying *any* op array has no cycle. -/
theorem absReplay_acyclic (fp : Array Int) (ops : Array Op)
    (r : Nat → Nat) (hg : GroundedBase r fp) :
    ∀ i, ¬ Reaches fp (absReplay fp ops) i i :=
  fun i => (absReplay_terminates fp ops r hg i).not_reaches_self

/-- Packaged as the operational sentence: after replay, every override chain
terminates at root without revisiting a node. -/
theorem absReplay_chain_nodup (fp : Array Int) (ops : Array Op)
    (r : Nat → Nat) (hg : GroundedBase r fp) :
    ∀ i, ∃ l, ChainTo fp (absReplay fp ops) i l ∧ l.Nodup := by
  intro i
  obtain ⟨l, hl⟩ := (absReplay_terminates fp ops r hg i).chainTo
  exact ⟨l, hl,
    hl.nodup fun v => (absReplay_terminates fp ops r hg v).not_reaches_self⟩

/-! ## §6. Codec: the word level round-trips

`pushWord`/`getWord` are inverse at every word boundary, `encodeView` is
word-faithful, and `toI`/`ofI` round-trip on the i64 range. Together: reading
word `i` of the encoded view recovers entry `i` exactly
(`decode_encode_id`). What is *not* proved here is the input-side mirror
(`decodeBase`/`decodeOps` against a bytes-level encoder — the kernel does not
contain such an encoder; the Rust side owns request encoding). -/

private def pwBytes (u : UInt64) : List UInt8 :=
  (List.range 8).map (fun k => UInt8.ofNat ((u >>> (UInt64.ofNat (8 * k))).toNat % 256))

private theorem pushWord_eq (b : ByteArray) (u : UInt64) :
    pushWord b u = (pwBytes u).foldl ByteArray.push b := by
  unfold pushWord pwBytes
  rw [List.foldl_map]

private theorem byteAt_push_lt {b : ByteArray} {x : UInt8} {i : Nat}
    (h : i < b.size) : byteAt (b.push x) i = byteAt b i := by
  unfold byteAt
  rw [dif_pos (by rw [ByteArray.size_push]; omega), dif_pos h]
  exact Array.getElem_push_lt (xs := b.data) (x := x) h

private theorem byteAt_push_eq {b : ByteArray} {x : UInt8} :
    byteAt (b.push x) b.size = x := by
  unfold byteAt
  rw [dif_pos (by rw [ByteArray.size_push]; omega)]
  exact Array.getElem_push_eq (xs := b.data) (x := x)

private theorem byteAt_foldl_push_lt (l : List UInt8) :
    ∀ (b : ByteArray) (i : Nat), i < b.size →
      byteAt (l.foldl ByteArray.push b) i = byteAt b i := by
  induction l with
  | nil => exact fun _ _ _ => rfl
  | cons x t ih =>
    intro b i h
    rw [List.foldl_cons, ih _ _ (by rw [ByteArray.size_push]; omega),
        byteAt_push_lt h]

private theorem size_foldl_push (l : List UInt8) :
    ∀ b : ByteArray, (l.foldl ByteArray.push b).size = b.size + l.length := by
  induction l with
  | nil => simp
  | cons x t ih =>
    intro b
    rw [List.foldl_cons, ih, ByteArray.size_push]
    simp +arith

private theorem byteAt_foldl_push (l : List UInt8) :
    ∀ (b : ByteArray) (k : Nat) (hk : k < l.length),
      byteAt (l.foldl ByteArray.push b) (b.size + k) = l[k] := by
  induction l with
  | nil => intro _ _ hk; simp at hk
  | cons x t ih =>
    intro b k hk
    match k with
    | 0 =>
      rw [List.foldl_cons]
      rw [byteAt_foldl_push_lt t _ _ (by rw [ByteArray.size_push]; omega)]
      simpa using byteAt_push_eq
    | k + 1 =>
      rw [List.foldl_cons]
      have := ih (b.push x) k (by simpa using hk)
      rw [ByteArray.size_push] at this
      rw [show b.size + (k + 1) = b.size + 1 + k by omega, this]
      simp

theorem size_pushWord (b : ByteArray) (u : UInt64) :
    (pushWord b u).size = b.size + 8 := by
  rw [pushWord_eq, size_foldl_push]
  rfl

private theorem orAddPow (i : Nat) {a : Nat} (b : Nat) (ha : a < 2 ^ i) :
    a ||| b * 2 ^ i = a + b * 2 ^ i := by
  rw [Nat.or_comm, Nat.mul_comm b, ← Nat.two_pow_add_eq_or_of_lt ha, Nat.add_comm, Nat.mul_comm]

private theorem assemble (U : Nat) (hU : U < 2 ^ 64) :
    ((((((((0 : Nat) ||| U % 256)
      ||| U / 2 ^ 8 % 256 * 2 ^ 8)
      ||| U / 2 ^ 16 % 256 * 2 ^ 16)
      ||| U / 2 ^ 24 % 256 * 2 ^ 24)
      ||| U / 2 ^ 32 % 256 * 2 ^ 32)
      ||| U / 2 ^ 40 % 256 * 2 ^ 40)
      ||| U / 2 ^ 48 % 256 * 2 ^ 48)
      ||| U / 2 ^ 56 % 256 * 2 ^ 56 = U := by
  rw [Nat.zero_or,
      orAddPow 8 _ (by omega),
      orAddPow 16 _ (by omega),
      orAddPow 24 _ (by omega),
      orAddPow 32 _ (by omega),
      orAddPow 40 _ (by omega),
      orAddPow 48 _ (by omega),
      orAddPow 56 _ (by omega)]
  omega

private theorem byteAt_pushWord (b : ByteArray) (u : UInt64) (k : Nat) (hk : k < 8) :
    byteAt (pushWord b u) (b.size + k) =
      UInt8.ofNat ((u >>> (UInt64.ofNat (8 * k))).toNat % 256) := by
  rw [pushWord_eq, byteAt_foldl_push _ _ _ (by simp [pwBytes]; omega)]
  simp [pwBytes]

private theorem assembleN (U : Nat) (hU : U < 18446744073709551616) :
    ((((((((0 : Nat) ||| U % 256)
      ||| U / 256 % 256 * 256)
      ||| U / 65536 % 256 * 65536)
      ||| U / 16777216 % 256 * 16777216)
      ||| U / 4294967296 % 256 * 4294967296)
      ||| U / 1099511627776 % 256 * 1099511627776)
      ||| U / 281474976710656 % 256 * 281474976710656)
      ||| U / 72057594037927936 % 256 * 72057594037927936 = U :=
  assemble U hU

/-- A word pushed at the end of a word-aligned buffer reads back exactly. -/
theorem getWord_pushWord (b : ByteArray) (u : UInt64) {w : Nat}
    (h : b.size = 8 * w) : getWord (pushWord b u) w = u := by
  unfold getWord
  simp only [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.foldl]
  rw [show w * 8 = b.size by omega,
      byteAt_pushWord b u 0 (by omega), byteAt_pushWord b u 1 (by omega),
      byteAt_pushWord b u 2 (by omega), byteAt_pushWord b u 3 (by omega),
      byteAt_pushWord b u 4 (by omega), byteAt_pushWord b u 5 (by omega),
      byteAt_pushWord b u 6 (by omega), byteAt_pushWord b u 7 (by omega)]
  refine UInt64.toNat_inj.mp ?_
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_ofNat',
    UInt8.toNat_ofNat', UInt64.toNat_shiftRight, UInt64.toNat_ofNat,
    Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.reduceMul, Nat.reduceMod, Nat.reducePow]
  refine Eq.trans ?_ (assembleN u.toNat (UInt64.toNat_lt u))
  congr 1
  · congr 1
    · congr 1
      · congr 1
        · congr 1
          · congr 1
            · congr 1
              · congr 1 <;> omega
              · omega
            · omega
          · omega
        · omega
      · omega
    · omega
  · omega

/-- Pushing a word does not disturb any complete word already in the buffer. -/
theorem getWord_pushWord_lt (b : ByteArray) (u : UInt64) {i : Nat}
    (h : 8 * (i + 1) ≤ b.size) : getWord (pushWord b u) i = getWord b i := by
  unfold getWord
  simp only [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.foldl]
  rw [pushWord_eq,
      byteAt_foldl_push_lt _ _ _ (by omega), byteAt_foldl_push_lt _ _ _ (by omega),
      byteAt_foldl_push_lt _ _ _ (by omega), byteAt_foldl_push_lt _ _ _ (by omega),
      byteAt_foldl_push_lt _ _ _ (by omega), byteAt_foldl_push_lt _ _ _ (by omega),
      byteAt_foldl_push_lt _ _ _ (by omega), byteAt_foldl_push_lt _ _ _ (by omega)]

private theorem size_foldl_pushWord (l : List Int) :
    ∀ b : ByteArray,
      (l.foldl (fun acc v => pushWord acc (ofI v)) b).size = b.size + 8 * l.length := by
  induction l with
  | nil => intro b; simp
  | cons x t ih =>
    intro b
    rw [List.foldl_cons, ih, size_pushWord, List.length_cons]
    omega

/-- The encoded view is exactly one word per entry. -/
theorem size_encodeView (ov : Array Int) : (encodeView ov).size = 8 * ov.size := by
  unfold encodeView
  rw [← Array.foldl_toList, size_foldl_pushWord]
  simp

private theorem getWord_foldl_pushWord_lt (l : List Int) :
    ∀ (b : ByteArray) (i : Nat), 8 * (i + 1) ≤ b.size →
      getWord (l.foldl (fun acc v => pushWord acc (ofI v)) b) i = getWord b i := by
  induction l with
  | nil => intro b i _; rfl
  | cons x t ih =>
    intro b i h
    rw [List.foldl_cons, ih _ _ (by rw [size_pushWord]; omega),
        getWord_pushWord_lt _ _ h]

private theorem getWord_foldl_pushWord (l : List Int) :
    ∀ (b : ByteArray) (w : Nat), b.size = 8 * w →
      ∀ (j : Nat) (hj : j < l.length),
        getWord (l.foldl (fun acc v => pushWord acc (ofI v)) b) (w + j) = ofI l[j] := by
  induction l with
  | nil => intro b w _ j hj; simp at hj
  | cons x t ih =>
    intro b w hb j hj
    rw [List.foldl_cons]
    match j with
    | 0 =>
      rw [Nat.add_zero,
          getWord_foldl_pushWord_lt t _ _ (by rw [size_pushWord, hb]; omega),
          getWord_pushWord _ _ hb]
      rfl
    | j + 1 =>
      have := ih (pushWord b (ofI x)) (w + 1)
        (by rw [size_pushWord, hb]; omega) j (by simpa using hj)
      rw [show w + (j + 1) = w + 1 + j by omega, this]
      rfl

/-- Word `i` of the encoded view is entry `i`, encoded. -/
theorem getWord_encodeView (ov : Array Int) {i : Nat} (h : i < ov.size) :
    getWord (encodeView ov) i = ofI ov[i] := by
  unfold encodeView
  rw [← Array.foldl_toList]
  have := getWord_foldl_pushWord ov.toList ByteArray.empty 0 (by simp) i
    (by simpa using h)
  simpa using this

/-- The two's-complement round trip is the identity on the i64 range. -/
theorem toI_ofI {z : Int} (h1 : -(2 ^ 63) ≤ z) (h2 : z < 2 ^ 63) :
    toI (ofI z) = z := by
  unfold toI ofI
  rw [UInt64.toNat_ofNat']
  split <;> omega

/-- **Codec round trip at the word level**: decoding word `i` of the encoded
view recovers entry `i`, for every in-range value (the kernel only produces
`-2`, `-1`, and indices `< n`, all comfortably in i64 range). -/
theorem decode_encode_id (ov : Array Int) {i : Nat} (h : i < ov.size)
    (h1 : -(2 ^ 63) ≤ ov[i]) (h2 : ov[i] < 2 ^ 63) :
    toI (getWord (encodeView ov) i) = ov[i] := by
  rw [getWord_encodeView ov h, toI_ofI h1 h2]

end Uwueave.Exec
