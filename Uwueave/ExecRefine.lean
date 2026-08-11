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

  4. **The trace block** (format v2): `overrides_foldl_applyOpFull` — the
     traced fold's view component is the plain `applyOp` fold, so every view
     theorem transfers to the shipping kernel; `size_statuses_absReplayFull` —
     one status word per request op; `applyOp_skip_of_opStatus_ne_zero` — a
     nonzero status is a real no-op on the view; `opStatus_mem_range` — a
     status word is one of the three documented values.

  5. **SEC for the shipping kernel** (§6, `kernel_derived_view_sec` and the
     `absReplay_perm` / `absReplay_append_mem` / `absReplay_ext_mem` family):
     the replay is a function of the op *set* — order-blind and
     redelivery-blind — so `Move.derived_view_sec`'s clauses are theorems
     about `absReplay`, not informal inheritance.

  6. **Input codec** (§8, `decodeBase_encodeRequest` /
     `decodeOps_encodeRequest` / `replay_encodeRequest`): the canonical
     request encoder round-trips through the decoders exactly, closing the
     input side of the wire contract at the Lean level.

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

/-- Projecting the traced fold onto its override block is the plain `applyOp`
fold over the same ops in the same order — the statuses ride along without
influencing the view. This is the lemma that lets every view theorem below be
proved against the plain fold and hold for the shipping `absReplayFull`. -/
theorem overrides_foldl_applyOpFull {fp : Array Int} {n : Nat} :
    ∀ (l : List (Op × Nat)) (acc : ReplayFull),
      (l.foldl (applyOpFull fp n) acc).overrides
        = (l.map Prod.fst).foldl (applyOp fp n) acc.overrides := by
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons p t ih =>
    intro acc
    rw [List.foldl_cons, List.map_cons, List.foldl_cons, ih]
    rfl

private theorem size_statuses_foldl {fp : Array Int} {n : Nat} :
    ∀ (l : List (Op × Nat)) (acc : ReplayFull),
      (l.foldl (applyOpFull fp n) acc).statuses.size = acc.statuses.size := by
  intro l
  induction l with
  | nil => intro acc; rfl
  | cons p t ih =>
    intro acc
    rw [List.foldl_cons, ih]
    simp [applyOpFull, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

/-- **The status block is exactly one word per request op** (no hypotheses —
this holds on an ungrounded base too): the size fact `replay`'s v2 output
layout relies on. -/
theorem size_statuses_absReplayFull (fp : Array Int) (ops : Array Op) :
    (absReplayFull fp ops).statuses.size = ops.size := by
  simp only [absReplayFull]
  rw [size_statuses_foldl]
  exact Array.size_replicate ..

/-- **A reported skip is a real no-op.** Whenever `opStatus` reports anything
but `0` (applied), `applyOp` returns the view unchanged: the status block
faithfully partitions the replay into ops that acted and ops that did not.
(The other direction is by construction: both functions branch on the same
conditions in the same order.) -/
theorem applyOp_skip_of_opStatus_ne_zero {fp : Array Int} {n : Nat}
    {ov : Array Int} {op : Op} (h : opStatus fp n ov op ≠ 0) :
    applyOp fp n ov op = ov := by
  simp only [opStatus] at h
  simp only [applyOp]
  repeat' split at h <;> simp_all
  all_goals intros
  all_goals omega

/-- A status word is one of the three documented values. -/
theorem opStatus_mem_range (fp : Array Int) (n : Nat) (ov : Array Int) (op : Op) :
    opStatus fp n ov op = 0 ∨ opStatus fp n ov op = 1 ∨ opStatus fp n ov op = 2 := by
  simp only [opStatus]
  repeat' split
  all_goals simp

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
  simp only [absReplay, absReplayFull]
  rw [overrides_foldl_applyOpFull, size_foldl_applyOp]
  exact Array.size_replicate ..

/-- **Every chain of the replayed view reaches root** (grounded base ⇒
terminating view, for any op array — order, duplication and content of the
ops are unconstrained). -/
theorem absReplay_terminates (fp : Array Int) (ops : Array Op)
    (r : Nat → Nat) (hg : GroundedBase r fp) :
    ∀ i, Terminates fp (absReplay fp ops) i := by
  simp only [absReplay, absReplayFull]
  rw [overrides_foldl_applyOpFull]
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

/-! ## §6. SEC for the shipping kernel: the replay is a function of the op SET

`Move.derived_view_sec` is generic: any log CRDT, any interpreter. Until this
section, the *shipping* kernel inherited it only informally ("the log is a
G-Set, so..."). Here the inheritance becomes theorems about `absReplay`
itself: the replay is blind to delivery order (`absReplay_perm`,
`absReplay_append_comm`), blind to redelivery (`absReplay_snoc_mem`,
`absReplay_append_mem`), and in fact a function of the op *set*
(`absReplay_ext_mem`) — with the three clauses of `derived_view_sec`
packaged, for this kernel, as `kernel_derived_view_sec`.

The two engines: (1) `opLe` is a total, transitive, *antisymmetric* order
(ops tying on all four keys are equal), so any two sorted permutations of a
log are equal lists (`Perm.eq_of_pairwise`); (2) replaying an op twice in a
row is replaying it once (`applyOp_applyOp` — no hypotheses: the second
application meets a view on which its own verdict cannot change), so the
duplicate runs a stable sort produces collapse in the fold. -/

private theorem opLt_eq_true_iff {a b : Op} :
    opLt a b = true ↔
      a.lamport.toNat < b.lamport.toNat
      ∨ (a.lamport.toNat = b.lamport.toNat ∧ a.replica.toNat < b.replica.toNat)
      ∨ (a.lamport.toNat = b.lamport.toNat ∧ a.replica.toNat = b.replica.toNat
          ∧ a.child < b.child)
      ∨ (a.lamport.toNat = b.lamport.toNat ∧ a.replica.toNat = b.replica.toNat
          ∧ a.child = b.child ∧ a.dest < b.dest) := by
  simp only [opLt, UInt64.lt_iff_toNat_lt]
  repeat' split
  all_goals simp_all
  all_goals omega

private theorem opLt_eq_false_iff {a b : Op} :
    opLt a b = false ↔
      ¬(a.lamport.toNat < b.lamport.toNat
        ∨ (a.lamport.toNat = b.lamport.toNat ∧ a.replica.toNat < b.replica.toNat)
        ∨ (a.lamport.toNat = b.lamport.toNat ∧ a.replica.toNat = b.replica.toNat
            ∧ a.child < b.child)
        ∨ (a.lamport.toNat = b.lamport.toNat ∧ a.replica.toNat = b.replica.toNat
            ∧ a.child = b.child ∧ a.dest < b.dest)) := by
  rw [← opLt_eq_true_iff]
  cases h : opLt a b <;> simp

theorem opLe_refl (a : Op) : opLe a a = true := by
  simp only [opLe, Bool.not_eq_true']
  rw [opLt_eq_false_iff]
  omega

theorem opLe_trans (a b c : Op) : opLe a b → opLe b c → opLe a c := by
  simp only [opLe, Bool.not_eq_true']
  rw [opLt_eq_false_iff, opLt_eq_false_iff, opLt_eq_false_iff]
  intro h₁ h₂
  omega

theorem opLe_total (a b : Op) : opLe a b || opLe b a := by
  simp only [opLe, Bool.not_eq_true', Bool.or_eq_true]
  rw [opLt_eq_false_iff, opLt_eq_false_iff]
  omega

/-- `opLe` is antisymmetric: two ops that tie on all four keys are the same
op — the fact that makes the sorted presentation of a log *unique*, and ties
in the stable sort harmless. -/
theorem opLe_antisymm {a b : Op} (h₁ : opLe a b) (h₂ : opLe b a) : a = b := by
  simp only [opLe, Bool.not_eq_true'] at h₁ h₂
  rw [opLt_eq_false_iff] at h₁ h₂
  obtain ⟨hl, hr, hc, hd⟩ :
      a.lamport.toNat = b.lamport.toNat ∧ a.replica.toNat = b.replica.toNat
        ∧ a.child = b.child ∧ a.dest = b.dest := by omega
  cases a; cases b
  simp_all [← UInt64.toNat_inj]

/-- The traced sort projects to the plain stable sort of the ops (core's
stability lemma `List.mergeSort_zipIdx`), so `absReplay` is literally
fold-over-`mergeSort`. -/
theorem absReplay_eq_foldl_mergeSort (fp : Array Int) (ops : Array Op) :
    absReplay fp ops
      = (ops.toList.mergeSort opLe).foldl (applyOp fp fp.size)
          (Array.replicate fp.size (-2)) := by
  simp only [absReplay, absReplayFull]
  rw [overrides_foldl_applyOpFull]
  have h : List.map Prod.fst (ops.toList.zipIdx.mergeSort (List.zipIdxLE opLe))
      = ops.toList.mergeSort opLe := List.mergeSort_zipIdx
  rw [h]

private theorem mergeSort_eq_of_perm {a b : List Op} (h : a.Perm b) :
    a.mergeSort opLe = b.mergeSort opLe :=
  List.Perm.eq_of_pairwise
    (fun _ _ _ _ hxy hyx => opLe_antisymm hxy hyx)
    (List.pairwise_mergeSort opLe_trans opLe_total a)
    (List.pairwise_mergeSort opLe_trans opLe_total b)
    ((List.mergeSort_perm a opLe).trans (h.trans (List.mergeSort_perm b opLe).symm))

/-- **The replay is blind to delivery order**: logs that are permutations of
each other replay identically. -/
theorem absReplay_perm (fp : Array Int) {a b : Array Op}
    (h : a.toList.Perm b.toList) : absReplay fp a = absReplay fp b := by
  rw [absReplay_eq_foldl_mergeSort, absReplay_eq_foldl_mergeSort,
      mergeSort_eq_of_perm h]

/-- Deltas commute — `derived_view_sec`'s clause (1), for this kernel. -/
theorem absReplay_append_comm (fp : Array Int) (a b : Array Op) :
    absReplay fp (a ++ b) = absReplay fp (b ++ a) :=
  absReplay_perm fp (by simp [List.perm_append_comm])

/-- **Replaying an op twice in a row is replaying it once** — no hypotheses.
A skip leaves the view unchanged, so the repeat meets the same view and skips
again; an applied op wrote its child's slot, and whether the repeat applies
(same write, collapsing) or skips, the view is the one write's. -/
theorem applyOp_applyOp (fp : Array Int) (n : Nat) (ov : Array Int) (op : Op) :
    applyOp fp n (applyOp fp n ov op) op = applyOp fp n ov op := by
  by_cases h1 : op.child ≥ n
  · simp only [applyOp, if_pos h1]
  · by_cases h2 : (op.dest == -1) = true
    · simp only [applyOp, if_neg h1, if_pos h2, Array.set!_eq_setIfInBounds,
        Array.setIfInBounds_setIfInBounds]
    · by_cases h3 : op.dest < 0
      · simp only [applyOp, if_neg h1, if_neg h2, if_pos h3]
      · by_cases h4 : op.dest.toNat ≥ n
        · simp only [applyOp, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
        · by_cases h5 : chainHits fp ov op.dest.toNat op.child (n + 1) = true
          · have hin : applyOp fp n ov op = ov := by
              simp only [applyOp, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
                if_pos h5]
            rw [hin]
            exact hin
          · have hin : applyOp fp n ov op = ov.set! op.child op.dest := by
              simp only [applyOp, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
                if_neg h5]
            rw [hin]
            simp only [applyOp, if_neg h1, if_neg h2, if_neg h3, if_neg h4,
              Array.set!_eq_setIfInBounds, Array.setIfInBounds_setIfInBounds,
              ite_self]

/-- The list-level replay every array theorem factors through. -/
private def replayL (fp : Array Int) (l : List Op) : Array Int :=
  (l.mergeSort opLe).foldl (applyOp fp fp.size) (Array.replicate fp.size (-2))

private theorem absReplay_eq_replayL (fp : Array Int) (ops : Array Op) :
    absReplay fp ops = replayL fp ops.toList :=
  absReplay_eq_foldl_mergeSort fp ops

private theorem replayL_perm {fp : Array Int} {a b : List Op} (h : a.Perm b) :
    replayL fp a = replayL fp b := by
  unfold replayL
  rw [mergeSort_eq_of_perm h]

/-- Appending one already-present op: the stable sort inserts the duplicate
next to its twin, where the fold collapses it. -/
private theorem replayL_snoc_mem {fp : Array Int} {l : List Op} {x : Op}
    (hx : x ∈ l) : replayL fp (l ++ [x]) = replayL fp l := by
  obtain ⟨l₁, l₂, hsplit⟩ := List.append_of_mem (List.mem_mergeSort.mpr hx)
  have hsorted := List.pairwise_mergeSort opLe_trans opLe_total l
  rw [hsplit] at hsorted
  have hsorted' : (l₁ ++ x :: x :: l₂).Pairwise (opLe · ·) := by
    rw [List.pairwise_append] at hsorted ⊢
    obtain ⟨hp₁, hp₂, hcross⟩ := hsorted
    rw [List.pairwise_cons] at hp₂
    obtain ⟨hxl₂, hpl₂⟩ := hp₂
    refine ⟨hp₁, ?_, ?_⟩
    · rw [List.pairwise_cons]
      refine ⟨?_, List.Pairwise.cons hxl₂ hpl₂⟩
      intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact opLe_refl _
      · exact hxl₂ b hb
    · intro a ha b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · exact hcross a ha _ List.mem_cons_self
      · exact hcross a ha b hb
  have hperm : (l ++ [x]).Perm (l₁ ++ x :: x :: l₂) := by
    have h₀ : l.Perm (l₁ ++ x :: l₂) := hsplit ▸ (List.mergeSort_perm l opLe).symm
    exact List.perm_append_comm.trans ((h₀.cons x).trans List.perm_middle.symm)
  have hsortEq : (l ++ [x]).mergeSort opLe = l₁ ++ x :: x :: l₂ :=
    List.Perm.eq_of_pairwise
      (fun _ _ _ _ hxy hyx => opLe_antisymm hxy hyx)
      (List.pairwise_mergeSort opLe_trans opLe_total _)
      hsorted'
      ((List.mergeSort_perm _ opLe).trans hperm)
  unfold replayL
  rw [hsortEq, hsplit]
  simp only [List.foldl_append, List.foldl_cons, applyOp_applyOp]

/-- Absorption, delta-shaped: appending any batch of already-present ops
changes nothing. -/
private theorem replayL_append_mem {fp : Array Int} {l d : List Op}
    (hd : ∀ op ∈ d, op ∈ l) : replayL fp (l ++ d) = replayL fp l := by
  induction d generalizing l with
  | nil => simp
  | cons x d' ih =>
    have hx : x ∈ l := hd x List.mem_cons_self
    calc replayL fp (l ++ x :: d')
        _ = replayL fp ((l ++ [x]) ++ d') := by rw [List.append_assoc]; rfl
        _ = replayL fp (l ++ [x]) := ih fun op hop =>
              List.mem_append_left _ (hd op (List.mem_cons_of_mem x hop))
        _ = replayL fp l := replayL_snoc_mem hx

/-- **Redelivery is invisible, op-level**: pushing an op the log already
contains does not change the replay. -/
theorem absReplay_snoc_mem (fp : Array Int) {ops : Array Op} {x : Op}
    (hx : x ∈ ops.toList) : absReplay fp (ops.push x) = absReplay fp ops := by
  rw [absReplay_eq_replayL, absReplay_eq_replayL, Array.toList_push]
  exact replayL_snoc_mem hx

/-- **Redelivery is invisible, delta-level**: appending a batch of
already-seen ops does not change the replay. -/
theorem absReplay_append_mem (fp : Array Int) {ops Δ : Array Op}
    (h : ∀ op ∈ Δ.toList, op ∈ ops.toList) :
    absReplay fp (ops ++ Δ) = absReplay fp ops := by
  rw [absReplay_eq_replayL, absReplay_eq_replayL, Array.toList_append]
  exact replayL_append_mem h

/-- **The replay is a function of the op SET.** Two logs with the same
members — any order, any duplication — replay identically. This is the
missing Prop-level link between the kernel and the grow-only-log abstraction:
`absReplay ∘ toSet⁻¹` is well-defined. -/
theorem absReplay_ext_mem (fp : Array Int) {a b : Array Op}
    (h : ∀ op, op ∈ a.toList ↔ op ∈ b.toList) :
    absReplay fp a = absReplay fp b := by
  have hab : absReplay fp (a ++ b) = absReplay fp a :=
    absReplay_append_mem fp fun op hop => (h op).mpr hop
  have hba : absReplay fp (b ++ a) = absReplay fp b :=
    absReplay_append_mem fp fun op hop => (h op).mp hop
  rw [← hab, absReplay_append_comm, hba]

/-- **`derived_view_sec`, discharged for the shipping kernel.** `Move.lean`'s
generic guarantee, instantiated on `absReplay` with log union = append:
(1) deltas arriving in either order give the same view, (2) a redelivered
delta changes nothing, (3) the view is acyclic regardless — on a grounded
base. SEC for the real kernel is no longer informal inheritance from the log
argument; it is these three clauses. (What `derived_view_sec` writes as
`⊔` on an abstract `MergeState` appears here as `++` — `absReplay_ext_mem`
is exactly the statement that `++` only matters through the set it
builds.) -/
theorem kernel_derived_view_sec (fp : Array Int) (r : Nat → Nat)
    (hg : GroundedBase r fp) (base Δ₁ Δ₂ : Array Op) :
    absReplay fp ((base ++ Δ₁) ++ Δ₂) = absReplay fp ((base ++ Δ₂) ++ Δ₁)
    ∧ absReplay fp ((base ++ Δ₁) ++ Δ₁) = absReplay fp (base ++ Δ₁)
    ∧ ∀ i, ¬ Reaches fp (absReplay fp ((base ++ Δ₁) ++ Δ₂)) i i := by
  refine ⟨?_, ?_, absReplay_acyclic _ _ r hg⟩
  · refine absReplay_perm fp ?_
    simp only [Array.toList_append, List.append_assoc]
    exact List.Perm.append_left _ List.perm_append_comm
  · exact absReplay_append_mem fp fun op hop => by
      rw [Array.toList_append]
      exact List.mem_append_right _ hop

/-! ## §7. Codec: the word level round-trips

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

/-! ## §8. Input codec: the request round-trips

The output side round-tripped in §7; here the *input* side stops being a
one-way street. `encodeRequest` (in `Exec.lean`) is the canonical encoder for
the request layout; these theorems prove `decodeBase`/`decodeOps` invert it
exactly, under the range conditions every real request satisfies (sizes and
children in u64 range, parents and destinations in i64 range). With
`replay_encodeRequest`, the byte-level kernel applied to a canonical request
is *literally* the decision layer plus the proved output codec — no unproved
decode step remains between them. The one thing left outside any proof is
that the Rust marshaller emits `encodeRequest`'s exact bytes: a finite,
testable claim (exercised end-to-end by the property suite), not a semantic
gap. -/

private theorem size_foldl_pushWords (l : List UInt64) :
    ∀ b : ByteArray, (l.foldl pushWord b).size = b.size + 8 * l.length := by
  induction l with
  | nil => simp
  | cons x t ih =>
    intro b
    rw [List.foldl_cons, ih, size_pushWord, List.length_cons]
    omega

private theorem getWord_foldl_pushWords_lt (l : List UInt64) :
    ∀ (b : ByteArray) (i : Nat), 8 * (i + 1) ≤ b.size →
      getWord (l.foldl pushWord b) i = getWord b i := by
  induction l with
  | nil => intro b i _; rfl
  | cons x t ih =>
    intro b i h
    rw [List.foldl_cons, ih _ _ (by rw [size_pushWord]; omega),
        getWord_pushWord_lt _ _ h]

private theorem getWord_foldl_pushWords (l : List UInt64) :
    ∀ (b : ByteArray) (w : Nat), b.size = 8 * w →
      ∀ (j : Nat), (hj : j < l.length) →
        getWord (l.foldl pushWord b) (w + j) = l[j] := by
  induction l with
  | nil => intro b w _ j hj; simp at hj
  | cons x t ih =>
    intro b w hb j hj
    rw [List.foldl_cons]
    match j with
    | 0 =>
      rw [Nat.add_zero,
          getWord_foldl_pushWords_lt t _ _ (by rw [size_pushWord, hb]; omega),
          getWord_pushWord _ _ hb]
      rfl
    | j + 1 =>
      have := ih (pushWord b x) (w + 1)
        (by rw [size_pushWord, hb]; omega) j (by simpa using hj)
      rw [show w + (j + 1) = w + 1 + j by omega, this]
      rfl

/-- Word `j` of the canonical request is word `j` of `requestWords`. -/
private theorem getWord_encodeRequest (fp : Array Int) (ops : Array Op)
    {j : Nat} (hj : j < (requestWords fp ops).length) :
    getWord (encodeRequest fp ops) j = (requestWords fp ops)[j] := by
  have h := getWord_foldl_pushWords (requestWords fp ops) ByteArray.empty 0
    (by simp) j hj
  simpa using h

private theorem length_flatMap_quad (f : Op → List UInt64)
    (h4 : ∀ op, (f op).length = 4) :
    ∀ l : List Op, (l.flatMap f).length = 4 * l.length := by
  intro l
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.flatMap_cons, List.length_append, h4, ih, List.length_cons]
    omega

private theorem requestWords_length (fp : Array Int) (ops : Array Op) :
    (requestWords fp ops).length = 2 + fp.size + 4 * ops.size := by
  have h := length_flatMap_quad
    (fun op => [op.lamport, op.replica, UInt64.ofNat op.child, ofI op.dest])
    (fun _ => rfl) ops.toList
  simp only [requestWords, List.length_cons, List.length_append,
    List.length_map, Array.length_toList, h]
  omega

private theorem getElem?_flatMap_quad (f : Op → List UInt64)
    (h4 : ∀ op, (f op).length = 4) :
    ∀ (l : List Op) (q k : Nat) (hq : q < l.length), k < 4 →
      (l.flatMap f)[4 * q + k]? = (f (l[q]'hq))[k]? := by
  intro l
  induction l with
  | nil => intro q k hq _; simp at hq
  | cons a t ih =>
    intro q k hq hk
    match q with
    | 0 =>
      simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add,
        List.getElem_cons_zero]
      rw [List.getElem?_append_left (by rw [h4]; exact hk)]
    | q + 1 =>
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [List.getElem?_append_right (by rw [h4]; omega)]
      rw [show 4 * (q + 1) + k - (f a).length = 4 * q + k by rw [h4]; omega]
      exact ih q k (by simpa using hq) hk

private theorem getElem_of_getElem? {l : List UInt64} {i : Nat} {v : UInt64}
    (h : i < l.length) (hv : l[i]? = some v) : l[i] = v := by
  rw [List.getElem?_eq_getElem h] at hv
  exact Option.some.inj hv

/-- **The base decodes back exactly** from the canonical request. -/
theorem decodeBase_encodeRequest (fp : Array Int) (ops : Array Op)
    (hn : fp.size < 2 ^ 64)
    (hfp : ∀ (i : Nat) (h : i < fp.size), -(2 ^ 63) ≤ fp[i] ∧ fp[i] < 2 ^ 63) :
    decodeBase (encodeRequest fp ops) = fp := by
  have hw0 : getWord (encodeRequest fp ops) 0 = UInt64.ofNat fp.size := by
    rw [getWord_encodeRequest fp ops (by rw [requestWords_length]; omega)]
    rfl
  have hn' : (getWord (encodeRequest fp ops) 0).toNat = fp.size := by
    rw [hw0, UInt64.toNat_ofNat']
    omega
  simp only [decodeBase, hn']
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Array.getElem_map, Array.getElem_range]
    have hidx : 2 + i < (requestWords fp ops).length := by
      rw [requestWords_length]
      simp at h1
      omega
    rw [getWord_encodeRequest fp ops hidx]
    have h1' : i < fp.size := by simpa using h1
    have hval : (requestWords fp ops)[2 + i]'hidx = ofI fp[i] := by
      apply getElem_of_getElem? hidx
      simp only [requestWords]
      rw [show (2 : Nat) + i = i + 1 + 1 by omega,
          List.getElem?_cons_succ, List.getElem?_cons_succ,
          List.getElem?_append_left (by simpa using h1'),
          List.getElem?_map, Array.getElem?_toList,
          Array.getElem?_eq_getElem h1']
      rfl
    rw [hval, toI_ofI (hfp i h1').1 (hfp i h1').2]

/-- **The ops decode back exactly** from the canonical request. -/
theorem decodeOps_encodeRequest (fp : Array Int) (ops : Array Op)
    (hn : fp.size < 2 ^ 64) (hm : ops.size < 2 ^ 64)
    (hchild : ∀ (j : Nat) (h : j < ops.size), ops[j].child < 2 ^ 64)
    (hdest : ∀ (j : Nat) (h : j < ops.size),
      -(2 ^ 63) ≤ ops[j].dest ∧ ops[j].dest < 2 ^ 63) :
    decodeOps (encodeRequest fp ops) = ops := by
  have hw0 : (getWord (encodeRequest fp ops) 0).toNat = fp.size := by
    rw [getWord_encodeRequest fp ops (by rw [requestWords_length]; omega)]
    show (UInt64.ofNat fp.size).toNat = fp.size
    rw [UInt64.toNat_ofNat']
    omega
  have hw1 : (getWord (encodeRequest fp ops) 1).toNat = ops.size := by
    rw [getWord_encodeRequest fp ops (by rw [requestWords_length]; omega)]
    show (UInt64.ofNat ops.size).toNat = ops.size
    rw [UInt64.toNat_ofNat']
    omega
  -- One quad word, extracted: word 2 + n + (4j + k) is field k of op j.
  have hquad : ∀ (j k : Nat) (hj : j < ops.size) (hk : k < 4),
      getWord (encodeRequest fp ops) (2 + fp.size + (4 * j + k))
        = ([ops[j].lamport, ops[j].replica, UInt64.ofNat ops[j].child,
            ofI ops[j].dest][k]'(by simpa using hk)) := by
    intro j k hj hk
    have hidx : 2 + fp.size + (4 * j + k) < (requestWords fp ops).length := by
      rw [requestWords_length]
      omega
    rw [getWord_encodeRequest fp ops hidx]
    apply getElem_of_getElem? hidx
    simp only [requestWords]
    have hj' : j < ops.toList.length := by simpa using hj
    rw [show 2 + fp.size + (4 * j + k) = fp.size + (4 * j + k) + 1 + 1 by omega,
        List.getElem?_cons_succ, List.getElem?_cons_succ,
        List.getElem?_append_right (by simp),
        show fp.size + (4 * j + k) - (List.map ofI fp.toList).length
          = 4 * j + k by simp,
        getElem?_flatMap_quad _ (fun _ => rfl) ops.toList j k hj' hk]
    simp only [Array.getElem_toList]
    rw [List.getElem?_eq_getElem (by simpa using hk)]
  simp only [decodeOps, hw0, hw1]
  apply Array.ext
  · simp
  · intro j h1 h2
    simp only [Array.getElem_map, Array.getElem_range]
    have hj : j < ops.size := by simpa using h1
    have q0 := hquad j 0 hj (by omega)
    have q1 := hquad j 1 hj (by omega)
    have q2 := hquad j 2 hj (by omega)
    have q3 := hquad j 3 hj (by omega)
    rw [show (2 : Nat) + fp.size + j * 4 = 2 + fp.size + (4 * j + 0) by omega]
    rw [show 2 + fp.size + (4 * j + 0) + 1 = 2 + fp.size + (4 * j + 1) by omega,
        show 2 + fp.size + (4 * j + 0) + 2 = 2 + fp.size + (4 * j + 2) by omega,
        show 2 + fp.size + (4 * j + 0) + 3 = 2 + fp.size + (4 * j + 3) by omega]
    rw [q0, q1, q2, q3]
    show Op.mk ops[j].lamport ops[j].replica (UInt64.ofNat ops[j].child).toNat
        (toI (ofI ops[j].dest)) = ops[j]
    have hc : (UInt64.ofNat ops[j].child).toNat = ops[j].child := by
      rw [UInt64.toNat_ofNat']
      have := hchild j hj
      omega
    rw [hc, toI_ofI (hdest j hj).1 (hdest j hj).2]

/-- **Whole-request round trip**: the byte-level kernel applied to the
canonical encoding of `(base, ops)` is exactly the decision layer followed by
the proved output codec. Nothing unverified stands between
`uwueave_replay_kernel`'s bytes and `absReplayFull`'s mathematics for
canonical requests. -/
theorem replay_encodeRequest (fp : Array Int) (ops : Array Op)
    (hn : fp.size < 2 ^ 64) (hm : ops.size < 2 ^ 64)
    (hfp : ∀ (i : Nat) (h : i < fp.size), -(2 ^ 63) ≤ fp[i] ∧ fp[i] < 2 ^ 63)
    (hchild : ∀ (j : Nat) (h : j < ops.size), ops[j].child < 2 ^ 64)
    (hdest : ∀ (j : Nat) (h : j < ops.size),
      -(2 ^ 63) ≤ ops[j].dest ∧ ops[j].dest < 2 ^ 63) :
    replay (encodeRequest fp ops)
      = encodeView ((absReplayFull fp ops).overrides
          ++ (absReplayFull fp ops).statuses) := by
  simp only [replay]
  rw [decodeBase_encodeRequest fp ops hn hfp,
      decodeOps_encodeRequest fp ops hn hm hchild hdest]

end Uwueave.Exec
