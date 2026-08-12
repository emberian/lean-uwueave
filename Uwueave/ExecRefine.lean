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

  4. **The trace block** (the ungated layer's, format v2 through v3): `overrides_foldl_applyOpFull` — the
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
     `decodeOps_encodeRequest` / `decodeGrants_encodeRequest` /
     `decodeRevs_encodeRequest` / `replay_encodeRequest`): the canonical v3
     request encoder round-trips through all four decoders exactly, closing
     the input side of the wire contract at the Lean level — magic word
     included, so `replay`'s refusal branch is discharged, not assumed away.

  7. **The gate** (§9, format v3): `gatedReplay_eq_absReplay_admitted` —
     **gating is pre-filtering**, the gated kernel is `absReplay` on the
     admitted sub-log, which is why `gatedReplay_acyclic` /
     `gatedReplay_terminates` / `gatedReplay_chain_nodup` / `size_gatedReplay`
     are one line each; `activeFrom_antitone` → `permittedOp_antitone` →
     **`kernel_gated_antitone`** (with `kernel_gated_merge_only_revokes`),
     the executable twin of `Gated.gated_antitone`: growing the revocation
     words never enlarges the replayed feed; `size_statuses_gatedReplayFull`,
     `gated_status_mem_range` and **`gated_status_eq_three_iff`** — one word
     per request op, from a four-code vocabulary, with `3` marking *exactly*
     the ops the gate removed; `gated_unauthorised_is_forever`; and
     ⚠ `applied_set_not_antitone`, the refutation that keeps the antitone
     claim from being over-read (revoking can *add* an applied move, because
     the cycle rule is not monotone in the log).

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

/-! The order's three laws, via a lexicographic key.

`opLt` is lexicographic `<` on five keys, so the direct route — characterize
it as a five-fold disjunction and hand that to `omega` — is a case split the
solver stops finishing at this arity (measured: ~90s for transitivity alone,
past the default heartbeat budget). Reducing the order to `lexLt` on the key
LIST turns each law into a two-line induction whose per-step obligation is a
single `Int` comparison. `opLt_eq_lexLt` pins the reduction to the shipping
comparator; nothing below reasons about `opLt` again. -/

private def opKey (a : Op) : List Int :=
  [(a.lamport.toNat : Int), (a.replica.toNat : Int), (a.child : Int), a.dest,
   (a.cite : Int)]

private def lexLt : List Int → List Int → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => if x < y then true else if y < x then false else lexLt xs ys

private theorem lexLt_irrefl : ∀ l : List Int, lexLt l l = false
  | [] => rfl
  | x :: xs => by
    simp only [lexLt, if_neg (Int.lt_irrefl x)]
    exact lexLt_irrefl xs

private theorem lexLt_asymm : ∀ {l₁ l₂ : List Int},
    lexLt l₁ l₂ = true → lexLt l₂ l₁ = false := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ h; cases l₂ with
    | nil => exact absurd h (by simp [lexLt])
    | cons y ys => rfl
  | cons x xs ih =>
    intro l₂ h
    cases l₂ with
    | nil => simp [lexLt] at h
    | cons y ys =>
      simp only [lexLt] at h ⊢
      by_cases h1 : x < y
      · rw [if_neg (by omega), if_pos (by omega)]
      · rw [if_neg h1] at h
        by_cases h2 : y < x
        · rw [if_pos h2] at h; exact absurd h (by simp)
        · rw [if_neg h2] at h
          rw [if_neg h2, if_neg h1]
          exact ih h

private theorem lexLt_antisymm : ∀ {l₁ l₂ : List Int},
    lexLt l₁ l₂ = false → lexLt l₂ l₁ = false → l₁ = l₂ := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ h₁ h₂
    cases l₂ with
    | nil => rfl
    | cons y ys => exact absurd h₁ (by simp [lexLt])
  | cons x xs ih =>
    intro l₂ h₁ h₂
    cases l₂ with
    | nil => exact absurd h₂ (by simp [lexLt])
    | cons y ys =>
      simp only [lexLt] at h₁ h₂
      by_cases h1 : x < y
      · exact absurd h₁ (by rw [if_pos h1]; simp)
      · by_cases h2 : y < x
        · exact absurd h₂ (by rw [if_pos h2]; simp)
        · rw [if_neg h1, if_neg h2] at h₁
          rw [if_neg h2, if_neg h1] at h₂
          have hxy : x = y := by omega
          rw [hxy, ih h₁ h₂]

private theorem lexLt_negtrans : ∀ {l₁ l₂ l₃ : List Int},
    lexLt l₁ l₃ = true → lexLt l₁ l₂ = true ∨ lexLt l₂ l₃ = true := by
  intro l₁
  induction l₁ with
  | nil =>
    intro l₂ l₃ h
    cases l₂ with
    | nil => exact Or.inr h
    | cons y ys => exact Or.inl rfl
  | cons x xs ih =>
    intro l₂ l₃ h
    cases l₃ with
    | nil => simp [lexLt] at h
    | cons z zs =>
      cases l₂ with
      | nil => exact Or.inr rfl
      | cons y ys =>
        simp only [lexLt] at h ⊢
        by_cases h1 : x < z
        · by_cases h2 : x < y
          · exact Or.inl (by rw [if_pos h2])
          · refine Or.inr ?_
            rw [if_pos (by omega)]
        · rw [if_neg h1] at h
          by_cases h3 : z < x
          · rw [if_pos h3] at h; exact absurd h (by simp)
          · rw [if_neg h3] at h
            have hxz : x = z := by omega
            subst hxz
            by_cases h2 : x < y
            · exact Or.inl (by rw [if_pos h2])
            · by_cases h4 : y < x
              · exact Or.inr (by rw [if_pos h4])
              · have hxy : x = y := by omega
                subst hxy
                rcases ih h with hl | hr
                · exact Or.inl (by rw [if_neg h2, if_neg h2]; exact hl)
                · exact Or.inr (by rw [if_neg h2, if_neg h2]; exact hr)

private theorem opLt_eq_lexLt (a b : Op) : opLt a b = lexLt (opKey a) (opKey b) := by
  simp only [opLt, opKey, lexLt, UInt64.lt_iff_toNat_lt, Int.ofNat_lt]
  have hlast : decide (a.cite < b.cite) =
      (if a.cite < b.cite then true
       else if b.cite < a.cite then false else false) := by
    by_cases h : a.cite < b.cite <;> simp [h]
  rw [hlast]

private theorem opKey_inj {a b : Op} (h : opKey a = opKey b) : a = b := by
  simp only [opKey, List.cons.injEq, and_true] at h
  obtain ⟨hl, hr, hc, hd, hg⟩ := h
  cases a; cases b
  simp_all [← UInt64.toNat_inj]
  omega

theorem opLe_refl (a : Op) : opLe a a = true := by
  simp only [opLe, opLt_eq_lexLt, lexLt_irrefl, Bool.not_false]

theorem opLe_trans (a b c : Op) : opLe a b → opLe b c → opLe a c := by
  simp only [opLe, opLt_eq_lexLt, Bool.not_eq_true']
  intro h₁ h₂
  by_cases h : lexLt (opKey c) (opKey a) = true
  · rcases lexLt_negtrans (l₂ := opKey b) h with hl | hr
    · exact absurd hl (by simp [h₂])
    · exact absurd hr (by simp [h₁])
  · simpa using h

theorem opLe_total (a b : Op) : opLe a b || opLe b a := by
  simp only [opLe, opLt_eq_lexLt, Bool.or_eq_true, Bool.not_eq_true']
  by_cases h : lexLt (opKey b) (opKey a) = true
  · exact Or.inr (lexLt_asymm h)
  · exact Or.inl (by simpa using h)

theorem opLe_antisymm {a b : Op} (h₁ : opLe a b) (h₂ : opLe b a) : a = b := by
  simp only [opLe, opLt_eq_lexLt, Bool.not_eq_true'] at h₁ h₂
  exact opKey_inj (lexLt_antisymm h₂ h₁)

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

/-! These three lemmas are the codec proof once, for an arbitrary source
carrier and word projection. `encodeView`, canonical requests, and the ERA
kernel retain their domain-specific theorem names as wrappers below and in
`EraKernel`; none of them needs to re-run the same induction. -/

namespace WordCodec

theorem foldlPushWord_size {α : Type _} (encode : α → UInt64) (values : List α) :
    ∀ b : ByteArray,
      (values.foldl (fun acc value => pushWord acc (encode value)) b).size =
        b.size + 8 * values.length := by
  induction values with
  | nil => intro b; simp
  | cons value rest ih =>
    intro b
    rw [List.foldl_cons, ih, size_pushWord, List.length_cons]
    omega

theorem foldlPushWord_get_lt {α : Type _} (encode : α → UInt64)
    (values : List α) :
    ∀ (b : ByteArray) (i : Nat), 8 * (i + 1) ≤ b.size →
      getWord (values.foldl (fun acc value => pushWord acc (encode value)) b) i =
        getWord b i := by
  induction values with
  | nil => intro b i _; rfl
  | cons value rest ih =>
    intro b i h
    rw [List.foldl_cons, ih _ _ (by rw [size_pushWord]; omega),
        getWord_pushWord_lt _ _ h]

theorem foldlPushWord_get {α : Type _} (encode : α → UInt64) (values : List α) :
    ∀ (b : ByteArray) (w : Nat), b.size = 8 * w →
      ∀ (j : Nat) (hj : j < values.length),
        getWord
          (values.foldl (fun acc value => pushWord acc (encode value)) b)
          (w + j) = encode values[j] := by
  induction values with
  | nil => intro b w _ j hj; simp at hj
  | cons value rest ih =>
    intro b w hb j hj
    rw [List.foldl_cons]
    match j with
    | 0 =>
      rw [Nat.add_zero,
          foldlPushWord_get_lt encode rest _ _ (by rw [size_pushWord, hb]; omega),
          getWord_pushWord _ _ hb]
      rfl
    | j + 1 =>
      have hget := ih (pushWord b (encode value)) (w + 1)
        (by rw [size_pushWord, hb]; omega) j (by simpa using hj)
      rw [show w + (j + 1) = w + 1 + j by omega, hget]
      rfl

end WordCodec

private theorem size_foldl_pushWord (l : List Int) :
    ∀ b : ByteArray,
      (l.foldl (fun acc v => pushWord acc (ofI v)) b).size = b.size + 8 * l.length :=
  WordCodec.foldlPushWord_size ofI l

/-- The encoded view is exactly one word per entry. -/
theorem size_encodeView (ov : Array Int) : (encodeView ov).size = 8 * ov.size := by
  unfold encodeView
  rw [← Array.foldl_toList, size_foldl_pushWord]
  simp

private theorem getWord_foldl_pushWord_lt (l : List Int) :
    ∀ (b : ByteArray) (i : Nat), 8 * (i + 1) ≤ b.size →
      getWord (l.foldl (fun acc v => pushWord acc (ofI v)) b) i = getWord b i :=
  WordCodec.foldlPushWord_get_lt ofI l

private theorem getWord_foldl_pushWord (l : List Int) :
    ∀ (b : ByteArray) (w : Nat), b.size = 8 * w →
      ∀ (j : Nat) (hj : j < l.length),
        getWord (l.foldl (fun acc v => pushWord acc (ofI v)) b) (w + j) = ofI l[j] :=
  WordCodec.foldlPushWord_get ofI l

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


/-! ## §9. The gate (format v3): the filter, and what survives it -/

private theorem map_fst_filter_zipIdx {α : Type _} (p : α → Bool) :
    ∀ (l : List α) (i : Nat),
      ((l.zipIdx i).filter (fun x => p x.1)).map Prod.fst = l.filter p := by
  intro l
  induction l with
  | nil => intro i; rfl
  | cons a t ih =>
    intro i
    rw [List.zipIdx_cons, List.filter_cons, List.filter_cons]
    by_cases h : p a
    · simp only [h, if_pos, List.map_cons]
      rw [ih (i + 1)]
    · simp only [h, Bool.false_eq_true, if_false]
      exact ih (i + 1)

private theorem pairwise_fst_of_zipIdxLE {L : List (Op × Nat)}
    (h : L.Pairwise (fun a b => List.zipIdxLE opLe a b = true)) :
    (L.map Prod.fst).Pairwise (fun a b => opLe a b = true) := by
  rw [List.pairwise_map]
  refine h.imp ?_
  intro a b hab
  simp only [List.zipIdxLE] at hab
  split at hab
  · rename_i hle
    exact hle
  · exact absurd hab (by simp)

/-- Sorting index-tagged ops and dropping the tags is sorting the ops: the
tag only breaks ties, and `opLe` has none (`opLe_antisymm`). Core's
`List.mergeSort_zipIdx` says this for a *contiguous* tagging; the gate hands
the sort a FILTERED tagging, whose indices are the surviving request slots,
so the general statement is the one the gated kernel needs. -/
private theorem map_fst_mergeSort_zipIdxLE (L : List (Op × Nat)) :
    (L.mergeSort (List.zipIdxLE opLe)).map Prod.fst
      = (L.map Prod.fst).mergeSort opLe := by
  refine List.Perm.eq_of_pairwise
    (fun _ _ _ _ hxy hyx => opLe_antisymm hxy hyx)
    (pairwise_fst_of_zipIdxLE
      (List.pairwise_mergeSort (List.zipIdxLE_trans opLe_trans)
        (List.zipIdxLE_total opLe_total) L))
    (List.pairwise_mergeSort opLe_trans opLe_total _)
    ?_
  exact ((List.mergeSort_perm L (List.zipIdxLE opLe)).map Prod.fst).trans
    (List.mergeSort_perm (L.map Prod.fst) opLe).symm

/-- **Gating is pre-filtering.** The gated kernel's view is *literally* the
ungated kernel run on the admitted sub-log — the filter removes ops and does
nothing else. Every `absReplay` theorem therefore transfers to the shipping
gated kernel with no new argument, which is why the acyclicity results below
are one line each. -/
theorem gatedReplay_eq_absReplay_admitted (gs : Array Grant) (rs : Array Nat)
    (fp : Array Int) (ops : Array Op) :
    gatedReplay gs rs fp ops = absReplay fp (admittedOps gs rs ops).toArray := by
  simp only [gatedReplay, gatedReplayFull]
  rw [overrides_foldl_applyOpFull, absReplay_eq_foldl_mergeSort,
      map_fst_mergeSort_zipIdxLE, map_fst_filter_zipIdx]
  simp only [admittedOps]

/-- **Acyclicity survives the gate** — and survives it for free: the gated
view is `absReplay` on a sub-log, so this *is* `absReplay_terminates`. -/
theorem gatedReplay_terminates (gs : Array Grant) (rs : Array Nat)
    (fp : Array Int) (ops : Array Op) (r : Nat → Nat) (hg : GroundedBase r fp) :
    ∀ i, Terminates fp (gatedReplay gs rs fp ops) i := by
  rw [gatedReplay_eq_absReplay_admitted]
  exact absReplay_terminates _ _ r hg

/-- `absReplay_acyclic` for the gated kernel: on a grounded base, the gated
replay of *any* op array under *any* grant/revocation substrate has no
cycle. -/
theorem gatedReplay_acyclic (gs : Array Grant) (rs : Array Nat)
    (fp : Array Int) (ops : Array Op) (r : Nat → Nat) (hg : GroundedBase r fp) :
    ∀ i, ¬ Reaches fp (gatedReplay gs rs fp ops) i i :=
  fun i => (gatedReplay_terminates gs rs fp ops r hg i).not_reaches_self

/-- Every override chain of the gated view terminates at root without
revisiting a node. -/
theorem gatedReplay_chain_nodup (gs : Array Grant) (rs : Array Nat)
    (fp : Array Int) (ops : Array Op) (r : Nat → Nat) (hg : GroundedBase r fp) :
    ∀ i, ∃ l, ChainTo fp (gatedReplay gs rs fp ops) i l ∧ l.Nodup := by
  rw [gatedReplay_eq_absReplay_admitted]
  exact absReplay_chain_nodup _ _ r hg

/-- The gated view has one word per node, gate or no gate. -/
theorem size_gatedReplay (gs : Array Grant) (rs : Array Nat)
    (fp : Array Int) (ops : Array Op) :
    (gatedReplay gs rs fp ops).size = fp.size := by
  rw [gatedReplay_eq_absReplay_admitted]
  exact size_absReplay _ _

/-! ### The antitone direction: revocations only ever remove -/

/-- `Authority.authority_view_antitone`, in the kernel's carrier: growing the
revocation array never activates a grant. Well-founded induction on the id,
mirroring `activeFrom`'s own recursion. -/
theorem activeFrom_antitone {gs : Array Grant} {rs rs' : Array Nat}
    (hgrow : ∀ i, isRevoked rs i = true → isRevoked rs' i = true) :
    ∀ i, activeFrom gs rs' i = true → activeFrom gs rs i = true := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro h
    cases hf : findGrant gs i with
    | none =>
      rw [activeFrom, hf] at h
      exact absurd h (by simp)
    | some g =>
      have hunfold : ∀ r : Array Nat, activeFrom gs r i =
          (if isRevoked r i then false
            else if g.parent == 0 then true
            else if _h : g.parent < i then activeFrom gs r g.parent else false) := by
        intro r; rw [activeFrom, hf]
      rw [hunfold] at h ⊢
      by_cases hrev : isRevoked rs' i = true
      · rw [if_pos hrev] at h; exact absurd h (by simp)
      · have hrev' : isRevoked rs i = false := by
          cases hr : isRevoked rs i with
          | false => rfl
          | true => exact absurd (hgrow i hr) (by simp [hrev])
        rw [if_neg hrev] at h
        rw [if_neg (by simp [hrev'])]
        by_cases hroot : (g.parent == 0) = true
        · rw [if_pos hroot]
        · rw [if_neg hroot] at h ⊢
          by_cases hlt : g.parent < i
          · rw [dif_pos hlt] at h ⊢
            exact ih g.parent hlt h
          · rw [dif_neg hlt] at h; exact absurd h (by simp)

/-- The gate is antitone in the revocation substrate, op by op. -/
theorem permittedOp_antitone {gs : Array Grant} {rs rs' : Array Nat}
    (hgrow : ∀ i, isRevoked rs i = true → isRevoked rs' i = true) (op : Op)
    (h : permittedOp gs rs' op = true) : permittedOp gs rs op = true := by
  cases hf : findGrant gs op.cite with
  | none => simp only [permittedOp, hf] at h; exact absurd h (by simp)
  | some g =>
    simp only [permittedOp, hf, Bool.and_eq_true] at h ⊢
    exact ⟨activeFrom_antitone hgrow _ h.1, h.2⟩

/-- **`kernel_gated_antitone` — the executable twin of
`Gated.gated_antitone`, and the point of the whole exercise.** Growing the
revocation words never ENLARGES the sub-log the kernel replays: every op
admitted under the larger revocation set was already admitted under the
smaller. Late revocations only ever remove moves from effect; they cannot
authorise one, resurrect one, or smuggle one into the fold. -/
theorem kernel_gated_antitone {gs : Array Grant} {rs rs' : Array Nat}
    (hgrow : ∀ i, isRevoked rs i = true → isRevoked rs' i = true)
    (ops : Array Op) {op : Op} (h : op ∈ admittedOps gs rs' ops) :
    op ∈ admittedOps gs rs ops := by
  simp only [admittedOps, List.mem_filter] at h ⊢
  exact ⟨h.1, permittedOp_antitone hgrow op h.2⟩

/-- Appending revocations only grows the revoked set — the wire's merge. -/
theorem isRevoked_append {rs Δ : Array Nat} {i : Nat}
    (h : isRevoked rs i = true) : isRevoked (rs ++ Δ) i = true := by
  simp only [isRevoked, Array.any_eq_true'] at h ⊢
  obtain ⟨x, hx, hxi⟩ := h
  exact ⟨x, by simp [hx], hxi⟩

/-- `kernel_gated_antitone` at an actual sync: merging in a peer's
revocations only ever shrinks the replayed sub-log —
`Gated.gated_merge_only_revokes` in the kernel. -/
theorem kernel_gated_merge_only_revokes (gs : Array Grant) (rs Δ : Array Nat)
    (ops : Array Op) {op : Op} (h : op ∈ admittedOps gs (rs ++ Δ) ops) :
    op ∈ admittedOps gs rs ops :=
  kernel_gated_antitone (fun _ hi => isRevoked_append hi) ops h

/-! ### The status trace is total -/

theorem size_statuses_gatedReplayFull (gs : Array Grant) (rs : Array Nat)
    (fp : Array Int) (ops : Array Op) :
    (gatedReplayFull gs rs fp ops).statuses.size = ops.size := by
  simp only [gatedReplayFull]
  rw [size_statuses_foldl]
  simp [initStatuses]

/-- Every entry of the final status block is either the value the gate wrote
before the fold, or an `opStatus` verdict the fold wrote — the one induction
both the range theorem and the `3`-marks-unauthorised theorem consume. -/
private theorem statuses_foldl_cases {fp : Array Int} {n : Nat} :
    ∀ (l : List (Op × Nat)) (acc : ReplayFull) (j : Nat),
      (l.foldl (applyOpFull fp n) acc).statuses.getD j 0 = acc.statuses.getD j 0
      ∨ ∃ (ov : Array Int) (op : Op),
          (l.foldl (applyOpFull fp n) acc).statuses.getD j 0 = opStatus fp n ov op := by
  intro l
  induction l with
  | nil => intro acc j; exact Or.inl rfl
  | cons p t ih =>
    intro acc j
    rw [List.foldl_cons]
    rcases ih (applyOpFull fp n acc p) j with hkeep | hwrote
    · rw [hkeep]
      by_cases hj : j = p.2
      · by_cases hin : p.2 < acc.statuses.size
        · exact Or.inr ⟨acc.overrides, p.1, by
            show (acc.statuses.set! p.2 (opStatus fp n acc.overrides p.1)).getD j 0 = _
            rw [hj, getD_set!_self hin]⟩
        · refine Or.inl ?_
          show (acc.statuses.set! p.2 (opStatus fp n acc.overrides p.1)).getD j 0 = _
          rw [hj, getD_oob (by
                rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]; omega),
              getD_oob (by omega)]
      · exact Or.inl (by
          show (acc.statuses.set! p.2 (opStatus fp n acc.overrides p.1)).getD j 0 = _
          rw [getD_set!_ne hj])
    · exact Or.inr hwrote

/-- **The status vocabulary is closed**: every word of the v3 status block is
one of the four documented codes. -/
theorem gated_status_mem_range (gs : Array Grant) (rs : Array Nat)
    (fp : Array Int) (ops : Array Op) (j : Nat) :
    (gatedReplayFull gs rs fp ops).statuses.getD j 0 = 0
    ∨ (gatedReplayFull gs rs fp ops).statuses.getD j 0 = 1
    ∨ (gatedReplayFull gs rs fp ops).statuses.getD j 0 = 2
    ∨ (gatedReplayFull gs rs fp ops).statuses.getD j 0 = 3 := by
  simp only [gatedReplayFull]
  rcases statuses_foldl_cases (fp := fp) (n := fp.size) _
      ⟨Array.replicate fp.size (-2), initStatuses gs rs ops⟩ j with hkeep | ⟨ov, op, hw⟩
  · rw [hkeep]
    show (initStatuses gs rs ops).getD j 0 = 0 ∨ _
    by_cases hj : j < ops.size
    · have : (initStatuses gs rs ops).getD j 0
          = if permittedOp gs rs ops[j] then 2 else 3 := by
        simp only [initStatuses]
        rw [Array.getD_eq_getD_getElem?, Array.getElem?_map,
            Array.getElem?_eq_getElem hj]
        rfl
      rw [this]
      split
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))
    · rw [getD_oob (by simp [initStatuses]; omega)]
      exact Or.inl rfl
  · rw [hw]
    rcases opStatus_mem_range fp fp.size ov op with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

private theorem getElem?_of_mem_zipIdx {α : Type _} {l : List α} {p : α × Nat}
    (h : p ∈ l.zipIdx) : l[p.2]? = some p.1 := by
  rw [List.mem_iff_getElem?] at h
  obtain ⟨k, hk⟩ := h
  rw [List.getElem?_zipIdx] at hk
  cases hl : l[k]? with
  | none => rw [hl] at hk; exact absurd hk (by simp)
  | some a =>
    rw [hl] at hk
    have hp : p = (a, k) := by
      have hk' := Option.some.inj hk
      simpa using hk'.symm
    rw [hp]
    simpa using hl

private theorem statuses_foldl_untouched {fp : Array Int} {n : Nat} :
    ∀ (l : List (Op × Nat)) (acc : ReplayFull) (j : Nat), (∀ p ∈ l, p.2 ≠ j) →
      (l.foldl (applyOpFull fp n) acc).statuses.getD j 0
        = acc.statuses.getD j 0 := by
  intro l
  induction l with
  | nil => intro acc j _; rfl
  | cons p t ih =>
    intro acc j hne
    rw [List.foldl_cons, ih _ _ (fun q hq => hne q (List.mem_cons_of_mem p hq))]
    show (acc.statuses.set! p.2 (opStatus fp n acc.overrides p.1)).getD j 0 = _
    exact getD_set!_ne (fun he => hne p List.mem_cons_self (he ▸ rfl))

private theorem statuses_foldl_ne_three {fp : Array Int} {n : Nat}
    (l : List (Op × Nat)) (acc : ReplayFull) (j : Nat)
    (h : acc.statuses.getD j 0 ≠ 3) :
    (l.foldl (applyOpFull fp n) acc).statuses.getD j 0 ≠ 3 := by
  rcases statuses_foldl_cases l acc j with hkeep | ⟨ov, op, hw⟩
  · rw [hkeep]; exact h
  · rw [hw]
    rcases opStatus_mem_range fp n ov op with hs | hs | hs <;> rw [hs] <;> decide

/-- **Status `3` marks exactly the ops the gate removed.** Not "at least"
(the fold never writes a `3`: its verdicts are `opStatus`'s three codes) and
not "at most" (an unauthorised op is not in the fold's list at all, so its
slot keeps the `3` the gate wrote). With `size_statuses_gatedReplayFull` this
is trace completeness: one word per request op, and the word says which of
the four things happened to it. -/
theorem gated_status_eq_three_iff (gs : Array Grant) (rs : Array Nat)
    (fp : Array Int) (ops : Array Op) {j : Nat} (hj : j < ops.size) :
    (gatedReplayFull gs rs fp ops).statuses.getD j 0 = 3
      ↔ permittedOp gs rs ops[j] = false := by
  have hinit : (initStatuses gs rs ops).getD j 0
      = if permittedOp gs rs ops[j] then 2 else 3 := by
    simp only [initStatuses]
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_map,
        Array.getElem?_eq_getElem hj]
    rfl
  constructor
  · intro h
    by_cases hp : permittedOp gs rs ops[j] = true
    · exfalso
      refine statuses_foldl_ne_three _ _ j ?_ h
      rw [hinit, if_pos hp]
      decide
    · simpa using hp
  · intro hp
    simp only [gatedReplayFull]
    rw [statuses_foldl_untouched _ _ j ?_, hinit, if_neg (by simp [hp])]
    intro q hq hqj
    rw [List.mem_mergeSort, List.mem_filter] at hq
    have hmem : ops.toList[q.2]? = some q.1 := getElem?_of_mem_zipIdx hq.1
    rw [hqj, Array.getElem?_toList, Array.getElem?_eq_getElem hj] at hmem
    have : q.1 = ops[j] := (Option.some.inj hmem).symm
    rw [this] at hq
    exact absurd hq.2 (by simp [hp])

/-- `gated_out_is_forever` in the kernel: an op the gate refused under `rs`
is refused under every larger revocation array — its status word stays `3`,
so a UI never sees a de-authorised move come back. -/
theorem gated_unauthorised_is_forever {gs : Array Grant} {rs rs' : Array Nat}
    (hgrow : ∀ i, isRevoked rs i = true → isRevoked rs' i = true)
    (fp : Array Int) (ops : Array Op) {j : Nat} (hj : j < ops.size)
    (h : (gatedReplayFull gs rs fp ops).statuses.getD j 0 = 3) :
    (gatedReplayFull gs rs' fp ops).statuses.getD j 0 = 3 := by
  rw [gated_status_eq_three_iff gs rs fp ops hj] at h
  rw [gated_status_eq_three_iff gs rs' fp ops hj]
  cases hp : permittedOp gs rs' ops[j] with
  | false => rfl
  | true => exact absurd (permittedOp_antitone hgrow _ hp) (by simp [h])



/-- Sorting a pair, unfolded once — the mergeSort layer discharged so the
concrete fold below is structural and `decide` can finish it (`Move.lean` §3
does the same for the miniature). -/
private theorem mergeSort_pair {α : Type _} {le : α → α → Bool} {a b : α} :
    [a, b].mergeSort le = if le a b then [a, b] else [b, a] := by
  rw [List.mergeSort]
  simp [List.merge]

/-! ### ⚠ The boundary: the ADMITTED set is antitone, the APPLIED set is not

`kernel_gated_antitone` says revocations only ever remove ops from the feed.
It is tempting to read that as "revoking never makes a move happen" — and
that reading is FALSE, because the cycle rule is not monotone in the log: an
op the fold skipped only because an earlier op was in the way applies once
that op is gated out. The fixture below is the two-node witness; the theorem
is stated in the same breath as the antitone one so nobody quotes the
flattering half. Two root nodes, two root-issued grants of scope 2, and two
moves that would close a cycle. -/

/-- Two nodes, both structural roots — grounded, so the acyclicity theorems
apply. -/
def unblockBase : Array Int := #[-1, -1]
/-- Two root-issued grants, each of scope 2 (covering nodes 0 and 1). -/
def unblockGrants : Array Grant := #[⟨1, 0, 2⟩, ⟨2, 0, 2⟩]
/-- The earlier move (lamport 1): node 1 under node 0, citing grant 1. -/
def unblockOpA : Op := { lamport := 1, replica := 0, child := 1, dest := 0, cite := 1 }
/-- The later move (lamport 2): node 0 under node 1, citing grant 2 — a
cycle, so the fold skips it while `unblockOpA` stands. -/
def unblockOpB : Op := { lamport := 2, replica := 0, child := 0, dest := 1, cite := 2 }
/-- The request's op array. -/
def unblockOps : Array Op := #[unblockOpA, unblockOpB]

/-- With nothing revoked, the gate admits both moves. -/
theorem unblock_admitted : admittedOps unblockGrants #[] unblockOps = [unblockOpA, unblockOpB] := by
  have hA : permittedOp unblockGrants #[] unblockOpA = true := by
    show (activeFrom unblockGrants #[] 1 && decide (1 < 2)) = true
    rw [show activeFrom unblockGrants #[] 1 = true from by
      rw [activeFrom, show findGrant unblockGrants 1 = some ⟨1, 0, 2⟩ from rfl]
      simp [isRevoked]]
    decide
  have hB : permittedOp unblockGrants #[] unblockOpB = true := by
    show (activeFrom unblockGrants #[] 2 && decide (0 < 2)) = true
    rw [show activeFrom unblockGrants #[] 2 = true from by
      rw [activeFrom, show findGrant unblockGrants 2 = some ⟨2, 0, 2⟩ from rfl]
      simp [isRevoked]]
    decide
  show List.filter (permittedOp unblockGrants #[]) [unblockOpA, unblockOpB] = _
  rw [List.filter_cons, List.filter_cons, hA, hB]
  simp

/-- Revoking grant 1 removes the earlier move from the feed — the antitone
direction, on this fixture. -/
theorem unblock_admitted_revoked : admittedOps unblockGrants #[1] unblockOps = [unblockOpB] := by
  have hA : permittedOp unblockGrants #[1] unblockOpA = false := by
    show (activeFrom unblockGrants #[1] 1 && decide (1 < 2)) = false
    rw [show activeFrom unblockGrants #[1] 1 = false from by
      rw [activeFrom, show findGrant unblockGrants 1 = some ⟨1, 0, 2⟩ from rfl]
      simp [isRevoked]]
    decide
  have hB : permittedOp unblockGrants #[1] unblockOpB = true := by
    show (activeFrom unblockGrants #[1] 2 && decide (0 < 2)) = true
    rw [show activeFrom unblockGrants #[1] 2 = true from by
      rw [activeFrom, show findGrant unblockGrants 2 = some ⟨2, 0, 2⟩ from rfl]
      simp [isRevoked]]
    decide
  show List.filter (permittedOp unblockGrants #[1]) [unblockOpA, unblockOpB] = _
  rw [List.filter_cons, List.filter_cons, hA, hB]
  simp

/-- ⚠ **Revoking a grant can ADD an applied move.** The revocation set grows
(`#[] ⊆ #[1]`), the admitted feed shrinks (`unblock_admitted_revoked`) — and
the resulting VIEW gains an override it did not have: node 0 was un-moved and
is now under node 1, because the op that had been blocking `unblockOpB` by
the cycle rule is gone. So `kernel_gated_antitone`'s antitonicity is exactly
about the FEED, and any claim of the form "more revocations ⇒ fewer applied
ops" is refuted here. What survives is the security-relevant statement: no op
is applied whose authority the substrate does not carry
(`Gated.kernel_gate_agrees_gatedOps`), and de-authorisation is forever
(`gated_unauthorised_is_forever`). -/
theorem applied_set_not_antitone :
    (∀ i, isRevoked (#[] : Array Nat) i = true → isRevoked #[1] i = true)
    ∧ gatedReplay unblockGrants #[] unblockBase unblockOps = #[-2, 0]
    ∧ gatedReplay unblockGrants #[1] unblockBase unblockOps = #[1, -2] := by
  refine ⟨fun i hi => absurd hi (by simp [isRevoked]), ?_, ?_⟩
  · rw [gatedReplay_eq_absReplay_admitted, unblock_admitted,
        absReplay_eq_foldl_mergeSort]
    show (List.mergeSort [unblockOpA, unblockOpB] opLe).foldl (applyOp unblockBase 2)
        (Array.replicate 2 (-2)) = _
    rw [mergeSort_pair, show opLe unblockOpA unblockOpB = true from by decide]
    decide
  · rw [gatedReplay_eq_absReplay_admitted, unblock_admitted_revoked,
        absReplay_eq_foldl_mergeSort]
    show (List.mergeSort [unblockOpB] opLe).foldl (applyOp unblockBase 2)
        (Array.replicate 2 (-2)) = _
    rw [List.mergeSort_singleton]
    decide


/-! ## §8. Input codec: the request round-trips (format v3)

The output side round-tripped in §7; here the *input* side stops being a
one-way street. `encodeRequest` (in `Exec.lean`) is the canonical encoder for
the v3 request layout — magic, four counts, then the base, op, grant and
revocation blocks — and these theorems prove the four decoders invert it
exactly, under the range conditions every real request satisfies (counts and
ids in u64 range, parents and destinations in i64 range). With
`replay_encodeRequest`, the byte-level kernel applied to a canonical request
is *literally* the gated decision layer plus the proved output codec — no
unproved decode step remains between them, and the magic guard is discharged
rather than assumed. The one thing left outside any proof is that the Rust
marshaller emits `encodeRequest`'s exact bytes: a finite, testable claim
(checked at runtime against `requestCanonicalKernel`), not a semantic gap. -/

private theorem size_foldl_pushWords (l : List UInt64) :
    ∀ b : ByteArray, (l.foldl pushWord b).size = b.size + 8 * l.length := by
  simpa only using WordCodec.foldlPushWord_size (fun word : UInt64 => word) l

private theorem getWord_foldl_pushWords_lt (l : List UInt64) :
    ∀ (b : ByteArray) (i : Nat), 8 * (i + 1) ≤ b.size →
      getWord (l.foldl pushWord b) i = getWord b i := by
  simpa only using WordCodec.foldlPushWord_get_lt (fun word : UInt64 => word) l

private theorem getWord_foldl_pushWords (l : List UInt64) :
    ∀ (b : ByteArray) (w : Nat), b.size = 8 * w →
      ∀ (j : Nat), (hj : j < l.length) →
        getWord (l.foldl pushWord b) (w + j) = l[j] := by
  simpa only using WordCodec.foldlPushWord_get (fun word : UInt64 => word) l

/-- Word `j` of the canonical request is word `j` of `requestWords`. -/
private theorem getWord_encodeRequest (fp : Array Int) (ops : Array Op)
    (gs : Array Grant) (rs : Array Nat)
    {j : Nat} (hj : j < (requestWords fp ops gs rs).length) :
    getWord (encodeRequest fp ops gs rs) j = (requestWords fp ops gs rs)[j] := by
  have h := getWord_foldl_pushWords (requestWords fp ops gs rs) ByteArray.empty 0
    (by simp) j hj
  simpa using h

/-! ### Block lengths and block-local indexing -/

namespace FixedWidth

theorem flatMap_length {α β : Type _} (width : Nat) (f : α → List β)
    (hk : ∀ x, (f x).length = width) :
    ∀ l : List α, (l.flatMap f).length = width * l.length := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.flatMap_cons, List.length_append, hk, ih, List.length_cons]
    rw [Nat.mul_succ]
    omega

theorem flatMap_getElem?_eq {α β : Type _} (width : Nat) (f : α → List β)
    (hk : ∀ x, (f x).length = width) :
    ∀ (l : List α) (q i : Nat) (hq : q < l.length), i < width →
      (l.flatMap f)[width * q + i]? = (f (l[q]'hq))[i]? := by
  intro l
  induction l with
  | nil => intro q i hq _; simp at hq
  | cons a t ih =>
    intro q i hq hi
    match q with
    | 0 =>
      simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add,
        List.getElem_cons_zero]
      rw [List.getElem?_append_left (by rw [hk]; exact hi)]
    | q + 1 =>
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [List.getElem?_append_right (by rw [hk, Nat.mul_succ]; omega)]
      rw [show width * (q + 1) + i - (f a).length = width * q + i by
        rw [hk, Nat.mul_succ]
        omega]
      exact ih q i (by simpa using hq) hi

end FixedWidth

private theorem length_flatMap_quint {α : Type _} (f : α → List UInt64)
    (hk : ∀ x, (f x).length = 5) :
    ∀ l : List α, (l.flatMap f).length = 5 * l.length :=
  FixedWidth.flatMap_length 5 f hk

private theorem getElem?_flatMap_quint {α : Type _} (f : α → List UInt64)
    (hk : ∀ x, (f x).length = 5) :
    ∀ (l : List α) (q i : Nat) (hq : q < l.length), i < 5 →
      (l.flatMap f)[5 * q + i]? = (f (l[q]'hq))[i]? :=
  FixedWidth.flatMap_getElem?_eq 5 f hk

private theorem length_flatMap_triple {α : Type _} (f : α → List UInt64)
    (hk : ∀ x, (f x).length = 3) :
    ∀ l : List α, (l.flatMap f).length = 3 * l.length :=
  FixedWidth.flatMap_length 3 f hk

private theorem getElem?_flatMap_triple {α : Type _} (f : α → List UInt64)
    (hk : ∀ x, (f x).length = 3) :
    ∀ (l : List α) (q i : Nat) (hq : q < l.length), i < 3 →
      (l.flatMap f)[3 * q + i]? = (f (l[q]'hq))[i]? :=
  FixedWidth.flatMap_getElem?_eq 3 f hk

theorem length_baseWords (fp : Array Int) : (baseWords fp).length = fp.size := by
  simp [baseWords]

theorem length_opWords (ops : Array Op) : (opWords ops).length = 5 * ops.size := by
  rw [opWords, length_flatMap_quint
    (fun op => [op.lamport, op.replica, UInt64.ofNat op.child, ofI op.dest,
      UInt64.ofNat op.cite]) (fun _ => rfl) ops.toList]
  simp

theorem length_grantWords (gs : Array Grant) :
    (grantWords gs).length = 3 * gs.size := by
  rw [grantWords, length_flatMap_triple
    (fun g => [UInt64.ofNat g.id, UInt64.ofNat g.parent, UInt64.ofNat g.scope])
    (fun _ => rfl) gs.toList]
  simp

theorem length_revWords (rs : Array Nat) : (revWords rs).length = rs.size := by
  simp [revWords]

private theorem requestWords_length (fp : Array Int) (ops : Array Op)
    (gs : Array Grant) (rs : Array Nat) :
    (requestWords fp ops gs rs).length
      = 5 + fp.size + 5 * ops.size + 3 * gs.size + rs.size := by
  simp only [requestWords, List.length_cons, List.length_append,
    length_baseWords, length_opWords, length_grantWords, length_revWords]
  omega

/-- Past the five header words, the request is its four blocks. -/
private theorem getElem?_request_body (fp : Array Int) (ops : Array Op)
    (gs : Array Grant) (rs : Array Nat) (i : Nat) :
    (requestWords fp ops gs rs)[5 + i]?
      = (baseWords fp ++ opWords ops ++ grantWords gs ++ revWords rs)[i]? := by
  simp only [requestWords]
  rw [show 5 + i = i + 1 + 1 + 1 + 1 + 1 by omega,
      List.getElem?_cons_succ, List.getElem?_cons_succ, List.getElem?_cons_succ,
      List.getElem?_cons_succ, List.getElem?_cons_succ]

private theorem body_base (A B C D : List UInt64) {i : Nat} (h : i < A.length) :
    (A ++ B ++ C ++ D)[i]? = A[i]? := by
  rw [List.getElem?_append_left (by simp only [List.length_append]; omega),
      List.getElem?_append_left (by simp only [List.length_append]; omega),
      List.getElem?_append_left h]

private theorem body_ops (A B C D : List UInt64) {i : Nat} (h : i < B.length) :
    (A ++ B ++ C ++ D)[A.length + i]? = B[i]? := by
  rw [List.getElem?_append_left (by simp only [List.length_append]; omega),
      List.getElem?_append_left (by simp only [List.length_append]; omega),
      List.getElem?_append_right (by omega),
      show A.length + i - A.length = i by omega]

private theorem body_grants (A B C D : List UInt64) {i : Nat} (h : i < C.length) :
    (A ++ B ++ C ++ D)[A.length + B.length + i]? = C[i]? := by
  rw [List.getElem?_append_left (by simp only [List.length_append]; omega),
      List.getElem?_append_right (by simp only [List.length_append]; omega),
      show A.length + B.length + i - (A ++ B).length = i by simp only [List.length_append]; omega]

private theorem body_revs (A B C D : List UInt64) {i : Nat} (_h : i < D.length) :
    (A ++ B ++ C ++ D)[A.length + B.length + C.length + i]? = D[i]? := by
  rw [List.getElem?_append_right (by simp only [List.length_append]; omega),
      show A.length + B.length + C.length + i - (A ++ B ++ C).length = i by
        simp only [List.length_append]; omega]

private theorem getElem_of_getElem? {l : List UInt64} {i : Nat} {v : UInt64}
    (h : i < l.length) (hv : l[i]? = some v) : l[i] = v := by
  rw [List.getElem?_eq_getElem h] at hv
  exact Option.some.inj hv

/-! ### The header words -/

private theorem word_magic (fp : Array Int) (ops : Array Op)
    (gs : Array Grant) (rs : Array Nat) :
    getWord (encodeRequest fp ops gs rs) 0 = magicV3 := by
  rw [getWord_encodeRequest fp ops gs rs (by rw [requestWords_length]; omega)]
  rfl

private theorem word_count (fp : Array Int) (ops : Array Op)
    (gs : Array Grant) (rs : Array Nat) :
    (getWord (encodeRequest fp ops gs rs) 1 = UInt64.ofNat fp.size)
    ∧ (getWord (encodeRequest fp ops gs rs) 2 = UInt64.ofNat ops.size)
    ∧ (getWord (encodeRequest fp ops gs rs) 3 = UInt64.ofNat gs.size)
    ∧ (getWord (encodeRequest fp ops gs rs) 4 = UInt64.ofNat rs.size) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [getWord_encodeRequest fp ops gs rs (by rw [requestWords_length]; omega)]
      rfl

/-! ### The four decoders invert the encoder -/

/-- **The base decodes back exactly** from the canonical request. -/
theorem decodeBase_encodeRequest (fp : Array Int) (ops : Array Op)
    (gs : Array Grant) (rs : Array Nat) (hn : fp.size < 2 ^ 64)
    (hfp : ∀ (i : Nat) (h : i < fp.size), -(2 ^ 63) ≤ fp[i] ∧ fp[i] < 2 ^ 63) :
    decodeBase (encodeRequest fp ops gs rs) = fp := by
  have hn' : (getWord (encodeRequest fp ops gs rs) 1).toNat = fp.size := by
    rw [(word_count fp ops gs rs).1, UInt64.toNat_ofNat']
    omega
  simp only [decodeBase, hn']
  apply Array.ext
  · simp
  · intro i h1 h2
    simp only [Array.getElem_map, Array.getElem_range]
    have h1' : i < fp.size := by simpa using h1
    have hidx : 5 + i < (requestWords fp ops gs rs).length := by
      rw [requestWords_length]; omega
    rw [getWord_encodeRequest fp ops gs rs hidx]
    have hval : (requestWords fp ops gs rs)[5 + i]'hidx = ofI fp[i] := by
      apply getElem_of_getElem? hidx
      rw [getElem?_request_body,
          body_base _ _ _ _ (by rw [length_baseWords]; exact h1')]
      simp only [baseWords, List.getElem?_map, Array.getElem?_toList,
        Array.getElem?_eq_getElem h1']
      rfl
    rw [hval, toI_ofI (hfp i h1').1 (hfp i h1').2]

/-- **The ops decode back exactly** from the canonical request. -/
theorem decodeOps_encodeRequest (fp : Array Int) (ops : Array Op)
    (gs : Array Grant) (rs : Array Nat)
    (hn : fp.size < 2 ^ 64) (hm : ops.size < 2 ^ 64)
    (hchild : ∀ (j : Nat) (h : j < ops.size), ops[j].child < 2 ^ 64)
    (hcite : ∀ (j : Nat) (h : j < ops.size), ops[j].cite < 2 ^ 64)
    (hdest : ∀ (j : Nat) (h : j < ops.size),
      -(2 ^ 63) ≤ ops[j].dest ∧ ops[j].dest < 2 ^ 63) :
    decodeOps (encodeRequest fp ops gs rs) = ops := by
  have hw1 : (getWord (encodeRequest fp ops gs rs) 1).toNat = fp.size := by
    rw [(word_count fp ops gs rs).1, UInt64.toNat_ofNat']; omega
  have hw2 : (getWord (encodeRequest fp ops gs rs) 2).toNat = ops.size := by
    rw [(word_count fp ops gs rs).2.1, UInt64.toNat_ofNat']; omega
  have hquint : ∀ (j k : Nat) (hj : j < ops.size) (hk : k < 5),
      getWord (encodeRequest fp ops gs rs) (5 + fp.size + (5 * j + k))
        = ([ops[j].lamport, ops[j].replica, UInt64.ofNat ops[j].child,
            ofI ops[j].dest, UInt64.ofNat ops[j].cite][k]'(by simpa using hk)) := by
    intro j k hj hk
    have hidx : 5 + fp.size + (5 * j + k) < (requestWords fp ops gs rs).length := by
      rw [requestWords_length]; omega
    rw [getWord_encodeRequest fp ops gs rs hidx]
    apply getElem_of_getElem? hidx
    have hj' : j < ops.toList.length := by simpa using hj
    rw [show 5 + fp.size + (5 * j + k) = 5 + (fp.size + (5 * j + k)) by omega,
        getElem?_request_body]
    rw [show fp.size = (baseWords fp).length by rw [length_baseWords],
        body_ops _ _ _ _ (by rw [length_opWords]; omega)]
    rw [show opWords ops = ops.toList.flatMap
          (fun op => [op.lamport, op.replica, UInt64.ofNat op.child, ofI op.dest,
            UInt64.ofNat op.cite]) from rfl,
        getElem?_flatMap_quint _ (fun _ => rfl) ops.toList j k hj' hk]
    simp only [Array.getElem_toList]
    rw [List.getElem?_eq_getElem (by simpa using hk)]
  simp only [decodeOps, hw1, hw2]
  apply Array.ext
  · simp
  · intro j h1 h2
    simp only [Array.getElem_map, Array.getElem_range]
    have hj : j < ops.size := by simpa using h1
    have q0 := hquint j 0 hj (by omega)
    have q1 := hquint j 1 hj (by omega)
    have q2 := hquint j 2 hj (by omega)
    have q3 := hquint j 3 hj (by omega)
    have q4 := hquint j 4 hj (by omega)
    rw [show (5 : Nat) + fp.size + j * 5 = 5 + fp.size + (5 * j + 0) by omega]
    rw [show 5 + fp.size + (5 * j + 0) + 1 = 5 + fp.size + (5 * j + 1) by omega,
        show 5 + fp.size + (5 * j + 0) + 2 = 5 + fp.size + (5 * j + 2) by omega,
        show 5 + fp.size + (5 * j + 0) + 3 = 5 + fp.size + (5 * j + 3) by omega,
        show 5 + fp.size + (5 * j + 0) + 4 = 5 + fp.size + (5 * j + 4) by omega]
    rw [q0, q1, q2, q3, q4]
    show Op.mk ops[j].lamport ops[j].replica (UInt64.ofNat ops[j].child).toNat
        (toI (ofI ops[j].dest)) (UInt64.ofNat ops[j].cite).toNat = ops[j]
    have hc : (UInt64.ofNat ops[j].child).toNat = ops[j].child := by
      rw [UInt64.toNat_ofNat']
      have := hchild j hj
      omega
    have hg : (UInt64.ofNat ops[j].cite).toNat = ops[j].cite := by
      rw [UInt64.toNat_ofNat']
      have := hcite j hj
      omega
    rw [hc, hg, toI_ofI (hdest j hj).1 (hdest j hj).2]

/-- **The grants decode back exactly** from the canonical request. -/
theorem decodeGrants_encodeRequest (fp : Array Int) (ops : Array Op)
    (gs : Array Grant) (rs : Array Nat)
    (hn : fp.size < 2 ^ 64) (hm : ops.size < 2 ^ 64) (hng : gs.size < 2 ^ 64)
    (hgr : ∀ (k : Nat) (h : k < gs.size),
      gs[k].id < 2 ^ 64 ∧ gs[k].parent < 2 ^ 64 ∧ gs[k].scope < 2 ^ 64) :
    decodeGrants (encodeRequest fp ops gs rs) = gs := by
  have hw1 : (getWord (encodeRequest fp ops gs rs) 1).toNat = fp.size := by
    rw [(word_count fp ops gs rs).1, UInt64.toNat_ofNat']; omega
  have hw2 : (getWord (encodeRequest fp ops gs rs) 2).toNat = ops.size := by
    rw [(word_count fp ops gs rs).2.1, UInt64.toNat_ofNat']; omega
  have hw3 : (getWord (encodeRequest fp ops gs rs) 3).toNat = gs.size := by
    rw [(word_count fp ops gs rs).2.2.1, UInt64.toNat_ofNat']; omega
  have htriple : ∀ (k t : Nat) (hk : k < gs.size) (ht : t < 3),
      getWord (encodeRequest fp ops gs rs)
          (5 + fp.size + ops.size * 5 + (3 * k + t))
        = ([UInt64.ofNat gs[k].id, UInt64.ofNat gs[k].parent,
            UInt64.ofNat gs[k].scope][t]'(by simpa using ht)) := by
    intro k t hk ht
    have hidx : 5 + fp.size + ops.size * 5 + (3 * k + t)
        < (requestWords fp ops gs rs).length := by
      rw [requestWords_length]; omega
    rw [getWord_encodeRequest fp ops gs rs hidx]
    apply getElem_of_getElem? hidx
    have hk' : k < gs.toList.length := by simpa using hk
    rw [show 5 + fp.size + ops.size * 5 + (3 * k + t)
          = 5 + (fp.size + 5 * ops.size + (3 * k + t)) by omega,
        getElem?_request_body]
    rw [show fp.size = (baseWords fp).length by rw [length_baseWords],
        show 5 * ops.size = (opWords ops).length by rw [length_opWords],
        show (baseWords fp).length + (opWords ops).length + (3 * k + t)
          = (baseWords fp).length + ((opWords ops).length + (3 * k + t)) by omega]
    rw [show (baseWords fp).length + ((opWords ops).length + (3 * k + t))
          = (baseWords fp).length + (opWords ops).length + (3 * k + t) by omega,
        body_grants _ _ _ _ (by rw [length_grantWords]; omega)]
    rw [show grantWords gs = gs.toList.flatMap
          (fun g => [UInt64.ofNat g.id, UInt64.ofNat g.parent,
            UInt64.ofNat g.scope]) from rfl,
        getElem?_flatMap_triple _ (fun _ => rfl) gs.toList k t hk' ht]
    simp only [Array.getElem_toList]
    rw [List.getElem?_eq_getElem (by simpa using ht)]
  simp only [decodeGrants, hw1, hw2, hw3]
  apply Array.ext
  · simp
  · intro k h1 h2
    simp only [Array.getElem_map, Array.getElem_range]
    have hk : k < gs.size := by simpa using h1
    have t0 := htriple k 0 hk (by omega)
    have t1 := htriple k 1 hk (by omega)
    have t2 := htriple k 2 hk (by omega)
    rw [show (5 : Nat) + fp.size + ops.size * 5 + k * 3
          = 5 + fp.size + ops.size * 5 + (3 * k + 0) by omega]
    rw [show 5 + fp.size + ops.size * 5 + (3 * k + 0) + 1
          = 5 + fp.size + ops.size * 5 + (3 * k + 1) by omega,
        show 5 + fp.size + ops.size * 5 + (3 * k + 0) + 2
          = 5 + fp.size + ops.size * 5 + (3 * k + 2) by omega]
    rw [t0, t1, t2]
    show Grant.mk (UInt64.ofNat gs[k].id).toNat (UInt64.ofNat gs[k].parent).toNat
        (UInt64.ofNat gs[k].scope).toNat = gs[k]
    obtain ⟨hi, hp, hs⟩ := hgr k hk
    rw [UInt64.toNat_ofNat', UInt64.toNat_ofNat', UInt64.toNat_ofNat',
        Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hp, Nat.mod_eq_of_lt hs]

/-- **The revocations decode back exactly** from the canonical request. -/
theorem decodeRevs_encodeRequest (fp : Array Int) (ops : Array Op)
    (gs : Array Grant) (rs : Array Nat)
    (hn : fp.size < 2 ^ 64) (hm : ops.size < 2 ^ 64) (hng : gs.size < 2 ^ 64)
    (hnr : rs.size < 2 ^ 64)
    (hrev : ∀ (t : Nat) (h : t < rs.size), rs[t] < 2 ^ 64) :
    decodeRevs (encodeRequest fp ops gs rs) = rs := by
  have hw1 : (getWord (encodeRequest fp ops gs rs) 1).toNat = fp.size := by
    rw [(word_count fp ops gs rs).1, UInt64.toNat_ofNat']; omega
  have hw2 : (getWord (encodeRequest fp ops gs rs) 2).toNat = ops.size := by
    rw [(word_count fp ops gs rs).2.1, UInt64.toNat_ofNat']; omega
  have hw3 : (getWord (encodeRequest fp ops gs rs) 3).toNat = gs.size := by
    rw [(word_count fp ops gs rs).2.2.1, UInt64.toNat_ofNat']; omega
  have hw4 : (getWord (encodeRequest fp ops gs rs) 4).toNat = rs.size := by
    rw [(word_count fp ops gs rs).2.2.2, UInt64.toNat_ofNat']; omega
  simp only [decodeRevs, hw1, hw2, hw3, hw4]
  apply Array.ext
  · simp
  · intro t h1 h2
    simp only [Array.getElem_map, Array.getElem_range]
    have ht : t < rs.size := by simpa using h1
    have hidx : 5 + fp.size + ops.size * 5 + gs.size * 3 + t
        < (requestWords fp ops gs rs).length := by
      rw [requestWords_length]; omega
    rw [getWord_encodeRequest fp ops gs rs hidx]
    have hval : (requestWords fp ops gs rs)[5 + fp.size + ops.size * 5 + gs.size * 3 + t]'hidx
        = UInt64.ofNat rs[t] := by
      apply getElem_of_getElem? hidx
      rw [show 5 + fp.size + ops.size * 5 + gs.size * 3 + t
            = 5 + (fp.size + 5 * ops.size + 3 * gs.size + t) by omega,
          getElem?_request_body]
      rw [show fp.size = (baseWords fp).length by rw [length_baseWords],
          show 5 * ops.size = (opWords ops).length by rw [length_opWords],
          show 3 * gs.size = (grantWords gs).length by rw [length_grantWords],
          body_revs _ _ _ _ (by rw [length_revWords]; omega)]
      simp only [revWords, List.getElem?_map, Array.getElem?_toList,
        Array.getElem?_eq_getElem ht]
      rfl
    rw [hval, UInt64.toNat_ofNat', Nat.mod_eq_of_lt (hrev t ht)]

/-- **Whole-request round trip**: the byte-level kernel applied to the
canonical encoding of `(base, ops, grants, revocations)` is exactly the gated
decision layer followed by the proved output codec. Nothing unverified stands
between `uwueave_replay_kernel`'s bytes and `gatedReplayFull`'s mathematics
for canonical requests — including the v3 magic guard, which is *discharged*
here (a canonical request carries the magic, so the refusal branch is dead)
rather than assumed away. -/
theorem replay_encodeRequest (fp : Array Int) (ops : Array Op)
    (gs : Array Grant) (rs : Array Nat)
    (hn : fp.size < 2 ^ 64) (hm : ops.size < 2 ^ 64) (hng : gs.size < 2 ^ 64)
    (hnr : rs.size < 2 ^ 64)
    (hfp : ∀ (i : Nat) (h : i < fp.size), -(2 ^ 63) ≤ fp[i] ∧ fp[i] < 2 ^ 63)
    (hchild : ∀ (j : Nat) (h : j < ops.size), ops[j].child < 2 ^ 64)
    (hcite : ∀ (j : Nat) (h : j < ops.size), ops[j].cite < 2 ^ 64)
    (hdest : ∀ (j : Nat) (h : j < ops.size),
      -(2 ^ 63) ≤ ops[j].dest ∧ ops[j].dest < 2 ^ 63)
    (hgr : ∀ (k : Nat) (h : k < gs.size),
      gs[k].id < 2 ^ 64 ∧ gs[k].parent < 2 ^ 64 ∧ gs[k].scope < 2 ^ 64)
    (hrev : ∀ (t : Nat) (h : t < rs.size), rs[t] < 2 ^ 64) :
    replay (encodeRequest fp ops gs rs)
      = encodeView ((gatedReplayFull gs rs fp ops).overrides
          ++ (gatedReplayFull gs rs fp ops).statuses) := by
  simp only [replay, word_magic, beq_self_eq_true, if_pos]
  rw [decodeBase_encodeRequest fp ops gs rs hn hfp,
      decodeOps_encodeRequest fp ops gs rs hn hm hchild hcite hdest,
      decodeGrants_encodeRequest fp ops gs rs hn hm hng hgr,
      decodeRevs_encodeRequest fp ops gs rs hn hm hng hnr hrev]

end Uwueave.Exec
