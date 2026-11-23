/-
# Uwueave.IncrementalCheckpointPreflight — checkpoint-plus-suffix admission

Shipping preflight used to replay the whole move log from genesis for every
admitted operation. This proof-only leaf justifies a bounded replacement which
runs the *unchanged* Lean kernel on a smaller request:

* a **checkpoint** summarizes a replayed prefix as its exact override view;
* **rebasing** folds that view into the kernel's first-parent block, so each
  node's structural parent in the new request is its effective parent at the
  checkpoint;
* the kernel then replays only the **suffix** of operations ordered after the
  checkpoint's clock, and its answer overlays onto the checkpoint.

`checkpoint_suffix_preflight_eq_full_replay` is the keystone: under the clock
condition the overlay is exactly the full replay's override block, the full
status block is the checkpoint's statuses followed by the suffix's, the replay
order splits the same way, and gate refusals are exactly preserved.

## Scope

The clock condition is necessary, not a convenience. An operation ordered
before the checkpoint can retroactively change verdicts (`Move.view_not_stable`,
witnessed here by `tooth_out_of_order_breaks_equivalence`), so such an operation
must be replayed from an earlier checkpoint. Authority is part of the summary:
`tooth_dropped_revocation_breaks_equivalence` shows that a checkpoint which
forgets a revocation admits a move the full replay refuses.

This module proves a property of the Lean decision layer. It does not prove
that the Rust host selects a valid checkpoint, that Rust's operation order
agrees with `opLe`, or anything about storage durability; those remain host
obligations exercised by `rust/tests/incremental_preflight.rs`.
-/
import Uwueave.ExecRefine

namespace Uwueave.IncrementalCheckpointPreflight

open Uwueave.Exec

set_option autoImplicit false

/-! ## §1. Overlay and rebase -/

/-- Suffix overrides win; a suffix slot of `-2` (no override) falls through to
the checkpoint's value. -/
def overlay (checkpoint delta : Array Int) : Array Int :=
  checkpoint.mapIdx fun i base =>
    let d := delta.getD i (-2)
    if d == -2 then base else d

/-- The first-parent block of a rebased request: every node's effective parent
under `overrides`. -/
def rebase (firstParent overrides : Array Int) : Array Int :=
  firstParent.mapIdx fun i _ => effParent firstParent overrides i

@[simp] theorem size_overlay (c d : Array Int) : (overlay c d).size = c.size := by
  simp [overlay]

@[simp] theorem size_rebase (fp ov : Array Int) : (rebase fp ov).size = fp.size := by
  simp [rebase]

private theorem getD_of_lt {a : Array Int} {i : Nat} {v : Int} (h : i < a.size) :
    a.getD i v = a[i] := by
  simp [Array.getD_eq_getD_getElem?, h]

private theorem getD_of_ge {a : Array Int} {i : Nat} {v : Int} (h : a.size ≤ i) :
    a.getD i v = v := by
  simp [Array.getD_eq_getD_getElem?, h]

private theorem getD_overlay {c d : Array Int} {i : Nat} (hi : i < c.size) :
    (overlay c d).getD i (-2) =
      if d.getD i (-2) == -2 then c[i] else d.getD i (-2) := by
  rw [getD_of_lt (by simpa using hi)]
  simp [overlay]

private theorem getD_rebase {fp ov : Array Int} {i : Nat} (hi : i < fp.size) :
    (rebase fp ov).getD i (-1) = effParent fp ov i := by
  rw [getD_of_lt (by simpa using hi)]
  simp [rebase]

/-- A rebased base under a delta has the same effective parents as the original
base under the overlaid view. -/
theorem effParent_rebase {fp ov δ : Array Int}
    (hov : ov.size = fp.size) (hδ : δ.size = fp.size) (i : Nat) :
    effParent (rebase fp ov) δ i = effParent fp (overlay ov δ) i := by
  by_cases hi : i < fp.size
  · have hovi : i < ov.size := by omega
    simp only [effParent]
    rw [getD_overlay hovi, getD_rebase hi]
    by_cases hd : (δ.getD i (-2) == -2) = true
    · simp only [hd, if_true, effParent, getD_of_lt hovi]
    · simp only [hd, Bool.false_eq_true, if_false]
  · have hδi : δ.size ≤ i := by omega
    have hoi : (overlay ov δ).size ≤ i := by simp; omega
    have hri : (rebase fp ov).size ≤ i := by simp; omega
    have hfi : fp.size ≤ i := by omega
    simp [effParent, getD_of_ge hδi, getD_of_ge hoi, getD_of_ge hri, getD_of_ge hfi]

/-- Materializing an effective-parent block after each batch composes exactly
like overlaying both batches before materializing, as in the host cache. -/
theorem rebase_rebase {fp ov δ : Array Int}
    (hov : ov.size = fp.size) (hδ : δ.size = fp.size) :
    rebase (rebase fp ov) δ = rebase fp (overlay ov δ) := by
  apply Array.ext
  · simp
  · intro i hi hj
    simp only [rebase, Array.getElem_mapIdx]
    exact effParent_rebase hov hδ i

/-- Chain membership reads the view only through `effParent`. -/
theorem chainHits_congr {fp₁ ov₁ fp₂ ov₂ : Array Int}
    (h : ∀ i, effParent fp₁ ov₁ i = effParent fp₂ ov₂ i)
    (start needle fuel : Nat) :
    chainHits fp₁ ov₁ start needle fuel = chainHits fp₂ ov₂ start needle fuel := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
      simp only [chainHits, h start, ih]

private theorem overlay_set {c δ : Array Int} (hδ : δ.size = c.size) {k : Nat}
    {v : Int} (hv : v ≠ -2) :
    (overlay c δ).set! k v = overlay c (δ.set! k v) := by
  simp only [Array.set!_eq_setIfInBounds]
  apply Array.ext
  · simp
  · intro i h₁ h₂
    have hic : i < c.size := by simpa using h₂
    have hiδ : i < δ.size := by omega
    have hleft : ((overlay c δ).setIfInBounds k v)[i]'h₁ =
        if k = i then v else (overlay c δ)[i]'(by simpa using hic) :=
      Array.getElem_setIfInBounds (by simpa using hic)
    have hgetD : (δ.setIfInBounds k v).getD i (-2) =
        if k = i then v else δ.getD i (-2) := by
      rw [getD_of_lt (by simpa using hiδ), getD_of_lt hiδ]
      exact Array.getElem_setIfInBounds hiδ
    rw [hleft]
    simp only [overlay, Array.getElem_mapIdx]
    rw [hgetD]
    by_cases hik : k = i
    · simp [hik, hv]
    · simp [hik]

private theorem overlay_replicate (c : Array Int) :
    overlay c (Array.replicate c.size (-2)) = c := by
  apply Array.ext
  · simp
  · intro i h₁ h₂
    simp [overlay, Array.getD_eq_getD_getElem?, h₂]

/-- One kernel step on the rebased request overlays exactly onto the same step
on the full view. -/
theorem applyOp_overlay {fp ov δ : Array Int}
    (hov : ov.size = fp.size) (hδ : δ.size = fp.size) (op : Op) :
    applyOp fp fp.size (overlay ov δ) op =
      overlay ov (applyOp (rebase fp ov) fp.size δ op) := by
  have hchain := chainHits_congr (effParent_rebase hov hδ)
  unfold applyOp
  by_cases h1 : op.child ≥ fp.size
  · simp only [if_pos h1]
  · have hc : op.child < ov.size := by omega
    simp only [if_neg h1]
    by_cases h2 : (op.dest == -1) = true
    · simp only [if_pos h2]
      exact overlay_set (by omega) (by decide)
    · simp only [h2, Bool.false_eq_true, if_false]
      by_cases h3 : op.dest < 0
      · simp only [if_pos h3]
      · simp only [if_neg h3]
        by_cases h4 : op.dest.toNat ≥ fp.size
        · simp only [if_pos h4]
        · simp only [if_neg h4]
          rw [hchain]
          by_cases h5 : chainHits fp (overlay ov δ) op.dest.toNat op.child
              (fp.size + 1) = true
          · simp only [if_pos h5]
          · simp only [h5, Bool.false_eq_true, if_false]
            exact overlay_set (by omega) (by omega)

/-- The status of one step is the same on the rebased request and the full
view. -/
theorem opStatus_overlay {fp ov δ : Array Int}
    (hov : ov.size = fp.size) (hδ : δ.size = fp.size) (op : Op) :
    opStatus fp fp.size (overlay ov δ) op =
      opStatus (rebase fp ov) fp.size δ op := by
  have hchain := chainHits_congr (effParent_rebase hov hδ)
  simp only [opStatus, hchain]

/-! ## §2. The replay order splits at the clock -/

/-- Move a request slot past a prefix of `k` operations. -/
private def shiftTag (k : Nat) (p : Op × Nat) : Op × Nat := (p.1, k + p.2)

private theorem zipIdxLE_antisymm {a b : Op × Nat}
    (h₁ : List.zipIdxLE opLe a b = true) (h₂ : List.zipIdxLE opLe b a = true) :
    a = b := by
  simp only [List.zipIdxLE] at h₁ h₂
  by_cases hab : opLe a.1 b.1 = true
  · by_cases hba : opLe b.1 a.1 = true
    · simp only [hab, hba, if_true, decide_eq_true_eq] at h₁ h₂
      exact Prod.ext (opLe_antisymm hab hba) (by omega)
    · simp [hba] at h₂
  · simp [hab] at h₁

private theorem zipIdxLE_shift (k : Nat) {a b : Op × Nat}
    (h : List.zipIdxLE opLe a b = true) :
    List.zipIdxLE opLe (shiftTag k a) (shiftTag k b) = true := by
  simp only [List.zipIdxLE, shiftTag] at h ⊢
  by_cases hab : opLe a.1 b.1 = true
  · by_cases hba : opLe b.1 a.1 = true
    · simp only [hab, hba, if_true, decide_eq_true_eq] at h ⊢
      omega
    · simp [hab, hba]
  · simp [hab] at h

private theorem mem_zipIdx_lt {l : List Op} {p : Op × Nat} (h : p ∈ l.zipIdx) :
    p.1 ∈ l ∧ p.2 < l.length := by
  obtain ⟨x, i⟩ := p
  have hm := List.mem_zipIdx h
  refine ⟨?_, by simpa using hm.2.1⟩
  have hi : i < l.length := by simpa using hm.2.1
  have hx : x = l[i]'hi := by simpa using hm.2.2
  simp [hx]

/-- The stable traced sort of a concatenation whose left block is ordered
below its right block is the concatenation of the two sorts, with right-block
slots moved past the left block. -/
private theorem sort_split (P : Op → Bool) (pre suf : List Op)
    (hcross : ∀ p ∈ pre, ∀ o ∈ suf, opLe p o = true) :
    (((pre ++ suf).zipIdx).filter (fun x => P x.1)).mergeSort (List.zipIdxLE opLe) =
      ((pre.zipIdx).filter (fun x => P x.1)).mergeSort (List.zipIdxLE opLe) ++
        (((suf.zipIdx).filter (fun x => P x.1)).mergeSort
          (List.zipIdxLE opLe)).map (shiftTag pre.length) := by
  apply List.Perm.eq_of_pairwise (le := fun a b => List.zipIdxLE opLe a b = true)
  · intro a b _ _ hab hba
    exact zipIdxLE_antisymm hab hba
  · exact List.pairwise_mergeSort (List.zipIdxLE_trans opLe_trans)
      (List.zipIdxLE_total opLe_total) _
  · rw [List.pairwise_append]
    refine ⟨List.pairwise_mergeSort (List.zipIdxLE_trans opLe_trans)
      (List.zipIdxLE_total opLe_total) _, ?_, ?_⟩
    · rw [List.pairwise_map]
      exact (List.pairwise_mergeSort (List.zipIdxLE_trans opLe_trans)
        (List.zipIdxLE_total opLe_total) _).imp (zipIdxLE_shift _)
    · intro a ha b hb
      obtain ⟨b', hb', rfl⟩ := List.mem_map.mp hb
      have ha' := (List.mem_filter.mp (List.mem_mergeSort.mp ha)).1
      have hb'' := (List.mem_filter.mp (List.mem_mergeSort.mp hb')).1
      have haMem := mem_zipIdx_lt ha'
      have hbMem := mem_zipIdx_lt hb''
      have hle := hcross _ haMem.1 _ hbMem.1
      simp only [List.zipIdxLE, shiftTag, hle, if_true]
      by_cases hba : opLe b'.1 a.1 = true
      · simp only [hba, if_true, decide_eq_true_eq]
        omega
      · simp [hba]
  · refine (List.mergeSort_perm _ _).trans ?_
    rw [List.zipIdx_append, List.filter_append]
    refine List.Perm.append (List.mergeSort_perm _ _).symm ?_
    have hmap : (suf.zipIdx (0 + pre.length)).filter (fun x => P x.1) =
        ((suf.zipIdx).filter (fun x => P x.1)).map (shiftTag pre.length) := by
      rw [Nat.zero_add, List.zipIdx_eq_map_add, List.filter_map]
      have hfun : (fun x : Op × Nat => P x.1) ∘
          (fun x : Op × Nat => (x.1, pre.length + x.2)) = fun x => P x.1 := rfl
      rw [hfun]
      rfl
    rw [hmap]
    exact ((List.mergeSort_perm _ _).map _).symm

/-! ## §3. Folding across the split -/

private theorem set!_append_left (a b : Array Int) {i : Nat} (h : i < a.size)
    (v : Int) : (a ++ b).set! i v = a.set! i v ++ b := by
  simp [Array.set!_eq_setIfInBounds, h]

private theorem set!_append_right (a b : Array Int) (j : Nat) (v : Int) :
    (a ++ b).set! (a.size + j) v = a ++ b.set! j v := by
  simp [Array.set!_eq_setIfInBounds]

/-- Folding a block whose slots all lie inside `acc.statuses` leaves an
appended tail untouched. -/
private theorem foldl_prefix_tail {fp : Array Int} {n : Nat} (tail : Array Int) :
    ∀ (l : List (Op × Nat)) (acc : ReplayFull),
      (∀ p ∈ l, p.2 < acc.statuses.size) →
      (l.foldl (applyOpFull fp n) ⟨acc.overrides, acc.statuses ++ tail⟩).overrides =
          (l.foldl (applyOpFull fp n) acc).overrides ∧
      (l.foldl (applyOpFull fp n) ⟨acc.overrides, acc.statuses ++ tail⟩).statuses =
          (l.foldl (applyOpFull fp n) acc).statuses ++ tail := by
  intro l
  induction l with
  | nil => intro acc _; exact ⟨rfl, rfl⟩
  | cons p t ih =>
      intro acc hl
      have hp : p.2 < acc.statuses.size := hl p List.mem_cons_self
      have hstep : applyOpFull fp n ⟨acc.overrides, acc.statuses ++ tail⟩ p =
          ⟨(applyOpFull fp n acc p).overrides,
            (applyOpFull fp n acc p).statuses ++ tail⟩ := by
        simp only [applyOpFull]
        rw [set!_append_left _ _ hp]
      simp only [List.foldl_cons]
      rw [hstep]
      apply ih
      intro q hq
      have hq' := hl q (List.mem_cons_of_mem _ hq)
      simpa [applyOpFull, Array.set!_eq_setIfInBounds] using hq'

/-- The suffix fold on the full view simulates the suffix fold on the rebased
request: the views stay related by `overlay` and the status blocks by the
fixed checkpoint prefix. -/
private theorem foldl_suffix_sim {fp ov cp : Array Int} (hov : ov.size = fp.size) :
    ∀ (l : List (Op × Nat)) (acc acc' : ReplayFull),
      acc.overrides = overlay ov acc'.overrides →
      acc'.overrides.size = fp.size →
      acc.statuses = cp ++ acc'.statuses →
      ((l.map (shiftTag cp.size)).foldl (applyOpFull fp fp.size) acc).overrides =
          overlay ov (l.foldl (applyOpFull (rebase fp ov) fp.size) acc').overrides ∧
      ((l.map (shiftTag cp.size)).foldl (applyOpFull fp fp.size) acc).statuses =
          cp ++ (l.foldl (applyOpFull (rebase fp ov) fp.size) acc').statuses := by
  intro l
  induction l with
  | nil => intro acc acc' ho _ hs; exact ⟨ho, hs⟩
  | cons p t ih =>
      intro acc acc' ho hsize hs
      simp only [List.map_cons, List.foldl_cons]
      apply ih
      · simp only [applyOpFull, shiftTag]
        rw [ho]
        exact applyOp_overlay hov hsize p.1
      · simp only [applyOpFull]
        rw [size_applyOp]
        exact hsize
      · simp only [applyOpFull, shiftTag]
        rw [hs, ho, opStatus_overlay hov hsize, set!_append_right]

/-- **The kernel splits at an ordered boundary.** Replaying a prefix and then,
on the rebased base, a suffix ordered after it is exactly the full replay. -/
theorem gatedReplayFull_append_of_ordered (gs : Array Grant) (rs : Array Nat)
    (fp : Array Int) (pre suf : Array Op)
    (hcross : ∀ p ∈ pre.toList, ∀ o ∈ suf.toList, opLe p o = true) :
    (gatedReplayFull gs rs fp (pre ++ suf)).overrides =
        overlay (gatedReplayFull gs rs fp pre).overrides
          (gatedReplayFull gs rs
            (rebase fp (gatedReplayFull gs rs fp pre).overrides) suf).overrides ∧
    (gatedReplayFull gs rs fp (pre ++ suf)).statuses =
        (gatedReplayFull gs rs fp pre).statuses ++
          (gatedReplayFull gs rs
            (rebase fp (gatedReplayFull gs rs fp pre).overrides) suf).statuses := by
  have hcpOv : (gatedReplayFull gs rs fp pre).overrides.size = fp.size :=
    size_gatedReplay gs rs fp pre
  have hcpSt : (gatedReplayFull gs rs fp pre).statuses.size = pre.size :=
    size_statuses_gatedReplayFull gs rs fp pre
  have hsplit := sort_split (permittedOp gs rs) pre.toList suf.toList hcross
  have hlen : pre.toList.length = (gatedReplayFull gs rs fp pre).statuses.size := by
    simp [hcpSt]
  rw [hlen] at hsplit
  have hinit : initStatuses gs rs (pre ++ suf) =
      initStatuses gs rs pre ++ initStatuses gs rs suf := by
    simp [initStatuses, Array.map_append]
  have hprefix := foldl_prefix_tail (fp := fp) (n := fp.size)
    (initStatuses gs rs suf)
    ((pre.toList.zipIdx.filter (fun p => permittedOp gs rs p.1)).mergeSort
      (List.zipIdxLE opLe))
    ⟨Array.replicate fp.size (-2), initStatuses gs rs pre⟩
    (by
      intro p hp
      have hm := (List.mem_filter.mp (List.mem_mergeSort.mp hp)).1
      have hlt := (mem_zipIdx_lt hm).2
      simpa [initStatuses] using hlt)
  have hcpEq : ((pre.toList.zipIdx.filter (fun p => permittedOp gs rs p.1)).mergeSort
      (List.zipIdxLE opLe)).foldl (applyOpFull fp fp.size)
      ⟨Array.replicate fp.size (-2), initStatuses gs rs pre⟩ =
        gatedReplayFull gs rs fp pre := rfl
  rw [hcpEq] at hprefix
  obtain ⟨hprefixOv, hprefixSt⟩ := hprefix
  have hsim := foldl_suffix_sim (fp := fp)
    (ov := (gatedReplayFull gs rs fp pre).overrides)
    (cp := (gatedReplayFull gs rs fp pre).statuses) hcpOv
    ((suf.toList.zipIdx.filter (fun p => permittedOp gs rs p.1)).mergeSort
      (List.zipIdxLE opLe))
    ((pre.toList.zipIdx.filter (fun p => permittedOp gs rs p.1)).mergeSort
      (List.zipIdxLE opLe) |>.foldl (applyOpFull fp fp.size)
        ⟨Array.replicate fp.size (-2),
          initStatuses gs rs pre ++ initStatuses gs rs suf⟩)
    ⟨Array.replicate fp.size (-2), initStatuses gs rs suf⟩
    (by
      rw [hprefixOv]
      have h := overlay_replicate (gatedReplayFull gs rs fp pre).overrides
      rw [hcpOv] at h
      exact h.symm)
    (by simp)
    hprefixSt
  have hfull : gatedReplayFull gs rs fp (pre ++ suf) =
      (((suf.toList.zipIdx.filter (fun p => permittedOp gs rs p.1)).mergeSort
        (List.zipIdxLE opLe)).map
          (shiftTag (gatedReplayFull gs rs fp pre).statuses.size)).foldl
        (applyOpFull fp fp.size)
        ((pre.toList.zipIdx.filter (fun p => permittedOp gs rs p.1)).mergeSort
          (List.zipIdxLE opLe) |>.foldl (applyOpFull fp fp.size)
            ⟨Array.replicate fp.size (-2),
              initStatuses gs rs pre ++ initStatuses gs rs suf⟩) := by
    show (((pre ++ suf).toList.zipIdx.filter
        (fun p => permittedOp gs rs p.1)).mergeSort (List.zipIdxLE opLe)).foldl
        (applyOpFull fp fp.size)
        ⟨Array.replicate fp.size (-2), initStatuses gs rs (pre ++ suf)⟩ = _
    rw [Array.toList_append, hsplit, hinit, List.foldl_append]
  have hdelta : gatedReplayFull gs rs
      (rebase fp (gatedReplayFull gs rs fp pre).overrides) suf =
      ((suf.toList.zipIdx.filter (fun p => permittedOp gs rs p.1)).mergeSort
        (List.zipIdxLE opLe)).foldl
        (applyOpFull (rebase fp (gatedReplayFull gs rs fp pre).overrides) fp.size)
        ⟨Array.replicate fp.size (-2), initStatuses gs rs suf⟩ := by
    simp only [gatedReplayFull, size_rebase]
  rw [hfull, hdelta]
  exact hsim

/-- The replay order of a concatenation splits at an ordered boundary. -/
theorem replayOrder_append (P : Op → Bool) (pre suf : List Op)
    (hcross : ∀ p ∈ pre, ∀ o ∈ suf, opLe p o = true) :
    ((pre ++ suf).filter P).mergeSort opLe =
      (pre.filter P).mergeSort opLe ++ (suf.filter P).mergeSort opLe := by
  apply List.Perm.eq_of_pairwise (le := fun a b => opLe a b = true)
  · intro a b _ _ hab hba
    exact opLe_antisymm hab hba
  · exact List.pairwise_mergeSort opLe_trans opLe_total _
  · rw [List.pairwise_append]
    refine ⟨List.pairwise_mergeSort opLe_trans opLe_total _,
      List.pairwise_mergeSort opLe_trans opLe_total _, ?_⟩
    intro a ha b hb
    exact hcross a (List.mem_filter.mp (List.mem_mergeSort.mp ha)).1
      b (List.mem_filter.mp (List.mem_mergeSort.mp hb)).1
  · refine (List.mergeSort_perm _ _).trans ?_
    rw [List.filter_append]
    exact List.Perm.append (List.mergeSort_perm _ _).symm
      (List.mergeSort_perm _ _).symm

/-! ## §4. The checkpointed state -/

/-- The durable summary of a replayed prefix: the node index and structural
tree, the authority and revocation frontier, the exact override view, and the
causal clock bounding every summarized operation. -/
structure CheckpointedLogState where
  firstParent : Array Int
  grants : Array Grant
  revocations : Array Nat
  overrides : Array Int
  clock : Option Op

/-- `clock` is at or above `o`. An absent clock covers nothing. -/
def clockCovers : Option Op → Op → Prop
  | none, _ => False
  | some c, o => opLe o c = true

/-- `o` is strictly after `clock`. Every operation is after an absent clock. -/
def clockBelow : Option Op → Op → Bool
  | none, _ => true
  | some c, o => opLt c o

/-- Advance a clock past one operation. -/
def clockJoin (clock : Option Op) (o : Op) : Option Op :=
  match clock with
  | none => some o
  | some c => if opLe c o then some o else some c

/-- Advance a clock past a batch of operations. -/
def advanceClock (clock : Option Op) (ops : Array Op) : Option Op :=
  ops.toList.foldl clockJoin clock

namespace CheckpointedLogState

/-- The empty checkpoint at the genesis of a fixed base and authority. -/
def genesis (fp : Array Int) (gs : Array Grant) (rs : Array Nat) :
    CheckpointedLogState where
  firstParent := fp
  grants := gs
  revocations := rs
  overrides := Array.replicate fp.size (-2)
  clock := none

/-- `s` is the exact summary of having replayed `prefix`. -/
structure Summarizes (s : CheckpointedLogState) (pre : Array Op) : Prop where
  overrides_eq : s.overrides =
    (gatedReplayFull s.grants s.revocations s.firstParent pre).overrides
  clock_covers : ∀ p ∈ pre.toList, clockCovers s.clock p

/-- The rebased first-parent block of the bounded kernel request. -/
def base (s : CheckpointedLogState) : Array Int :=
  rebase s.firstParent s.overrides

/-- Bounded preflight: the unchanged kernel decision layer on the rebased base
and only the suffix. -/
def preflight (s : CheckpointedLogState) (suffix : Array Op) : ReplayFull :=
  gatedReplayFull s.grants s.revocations s.base suffix

/-- Commit a suffix into the checkpoint. -/
def advance (s : CheckpointedLogState) (suffix : Array Op) : CheckpointedLogState :=
  { s with
    overrides := overlay s.overrides (s.preflight suffix).overrides
    clock := advanceClock s.clock suffix }

/-- A checkpoint that has forgotten its revocation frontier. -/
def dropRevocations (s : CheckpointedLogState) : CheckpointedLogState :=
  { s with revocations := #[] }

theorem genesis_summarizes (fp : Array Int) (gs : Array Grant) (rs : Array Nat) :
    (genesis fp gs rs).Summarizes #[] := by
  constructor
  · simp [genesis, gatedReplayFull]
  · simp

end CheckpointedLogState

open CheckpointedLogState

private theorem opLe_of_opLt {a b : Op} (h : opLt a b = true) : opLe a b = true := by
  have hnot : opLe b a = false := by simp [opLe, h]
  have htotal := opLe_total a b
  simpa [hnot] using htotal

private theorem cross_of_clock {clock : Option Op} {pre suf : Array Op}
    (hcovers : ∀ p ∈ pre.toList, clockCovers clock p)
    (habove : ∀ o ∈ suf.toList, clockBelow clock o = true) :
    ∀ p ∈ pre.toList, ∀ o ∈ suf.toList, opLe p o = true := by
  intro p hp o ho
  have hc := hcovers p hp
  have ha := habove o ho
  cases clock with
  | none => exact False.elim hc
  | some c => exact opLe_trans _ _ _ hc (opLe_of_opLt ha)

/-- Everything `checkpoint_suffix_preflight_eq_full_replay` asserts about one
bounded preflight, named clause by clause. -/
structure SuffixAgreement (s : CheckpointedLogState) (pre suffix : Array Op) :
    Prop where
  /-- The resulting tree is exactly the full replay's. -/
  state_exact :
    (gatedReplayFull s.grants s.revocations s.firstParent (pre ++ suffix)).overrides =
      overlay s.overrides (s.preflight suffix).overrides
  /-- Every verdict is exact: prefix verdicts are undisturbed and suffix
  verdicts are the bounded preflight's, in request order. -/
  verdicts_exact :
    (gatedReplayFull s.grants s.revocations s.firstParent (pre ++ suffix)).statuses =
      (gatedReplayFull s.grants s.revocations s.firstParent pre).statuses ++
        (s.preflight suffix).statuses
  /-- The replay order is the prefix's followed by the suffix's. -/
  order_exact :
    ((pre ++ suffix).toList.filter (permittedOp s.grants s.revocations)).mergeSort opLe =
      (pre.toList.filter (permittedOp s.grants s.revocations)).mergeSort opLe ++
        (suffix.toList.filter (permittedOp s.grants s.revocations)).mergeSort opLe
  /-- A suffix operation is refused by the bounded preflight exactly when the
  checkpoint's authority frontier refuses it. -/
  refusal_exact : ∀ (j : Nat) (hj : j < suffix.size),
    (s.preflight suffix).statuses.getD j 0 = 3 ↔
      permittedOp s.grants s.revocations suffix[j] = false

/-- **Checkpoint-plus-suffix preflight is full replay.** From a checkpoint that
exactly summarizes `prefix`, a suffix ordered strictly after its clock receives
the same resulting state, verdicts, replay order, and revocation refusals as
replaying `prefix ++ suffix` from genesis. -/
theorem checkpoint_suffix_preflight_eq_full_replay
    {s : CheckpointedLogState} {pre suffix : Array Op}
    (hs : s.Summarizes pre)
    (habove : ∀ o ∈ suffix.toList, clockBelow s.clock o = true) :
    SuffixAgreement s pre suffix := by
  have hcross := cross_of_clock hs.clock_covers habove
  obtain ⟨hov, hst⟩ := gatedReplayFull_append_of_ordered s.grants s.revocations
    s.firstParent pre suffix hcross
  have hpre : s.preflight suffix =
      gatedReplayFull s.grants s.revocations
        (rebase s.firstParent
          (gatedReplayFull s.grants s.revocations s.firstParent pre).overrides)
        suffix := by
    simp only [preflight, base]
    rw [hs.overrides_eq]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hov, hpre, ← hs.overrides_eq]
  · rw [hst, hpre]
  · rw [Array.toList_append]
    exact replayOrder_append _ _ _ hcross
  · intro j hj
    exact gated_status_eq_three_iff _ _ _ _ hj

/-- The host certifies a singleton on its predecessor view. Later sorted moves
cannot alter its status, even when the candidate arrived late. -/
theorem candidate_statuses_before_later_moves
    {s : CheckpointedLogState} {pre later : Array Op} {candidate : Op}
    (hs : s.Summarizes pre) (hc : clockBelow s.clock candidate = true)
    (hl : ∀ p ∈ (pre ++ #[candidate]).toList, ∀ o ∈ later.toList, opLe p o = true) :
    ((gatedReplayFull s.grants s.revocations s.firstParent
      ((pre ++ #[candidate]) ++ later)).statuses)[pre.size]? =
      (s.preflight #[candidate]).statuses[0]? := by
  have hagree := checkpoint_suffix_preflight_eq_full_replay (suffix := #[candidate]) hs
    (by simpa using hc)
  rw [(gatedReplayFull_append_of_ordered _ _ _ _ _ hl).2, hagree.verdicts_exact]
  simp [Array.getElem?_append, size_statuses_gatedReplayFull, CheckpointedLogState.preflight]

/-- The bounded request's bytes are answered by the shipping byte-level kernel
with exactly the bounded decision layer, so the certificate's request and
response are the objects the keystone is about. -/
theorem checkpoint_request_replays_preflight (s : CheckpointedLogState)
    (suffix : Array Op)
    (hn : s.base.size < 2 ^ 64) (hm : suffix.size < 2 ^ 64)
    (hng : s.grants.size < 2 ^ 64) (hnr : s.revocations.size < 2 ^ 64)
    (hfp : ∀ (i : Nat) (h : i < s.base.size),
      -(2 ^ 63) ≤ s.base[i] ∧ s.base[i] < 2 ^ 63)
    (hchild : ∀ (j : Nat) (h : j < suffix.size), suffix[j].child < 2 ^ 64)
    (hcite : ∀ (j : Nat) (h : j < suffix.size), suffix[j].cite < 2 ^ 64)
    (hdest : ∀ (j : Nat) (h : j < suffix.size),
      -(2 ^ 63) ≤ suffix[j].dest ∧ suffix[j].dest < 2 ^ 63)
    (hgr : ∀ (k : Nat) (h : k < s.grants.size),
      s.grants[k].id < 2 ^ 64 ∧ s.grants[k].parent < 2 ^ 64 ∧ s.grants[k].scope < 2 ^ 64)
    (hrev : ∀ (t : Nat) (h : t < s.revocations.size), s.revocations[t] < 2 ^ 64) :
    replay (encodeRequest s.base suffix s.grants s.revocations) =
      encodeView ((s.preflight suffix).overrides ++ (s.preflight suffix).statuses) :=
  replay_encodeRequest s.base suffix s.grants s.revocations hn hm hng hnr hfp
    hchild hcite hdest hgr hrev

/-! ## §5. Commit, crash, and recovery -/

private theorem clockJoin_covers_old {c : Option Op} {o p : Op}
    (h : clockCovers c p) : clockCovers (clockJoin c o) p := by
  cases c with
  | none => exact False.elim h
  | some k =>
      simp only [clockJoin]
      by_cases hk : opLe k o = true
      · simpa [hk, clockCovers] using opLe_trans _ _ _ h hk
      · simpa [hk, clockCovers] using h

private theorem clockJoin_covers_new (c : Option Op) (o : Op) :
    clockCovers (clockJoin c o) o := by
  cases c with
  | none => exact opLe_refl o
  | some k =>
      simp only [clockJoin]
      by_cases hk : opLe k o = true
      · simpa [hk, clockCovers] using opLe_refl o
      · have htotal := opLe_total k o
        have hok : opLe o k = true := by simpa [hk] using htotal
        simpa [hk, clockCovers] using hok

private theorem foldl_clockJoin_covers_old (l : List Op) :
    ∀ (c : Option Op) (p : Op), clockCovers c p →
      clockCovers (l.foldl clockJoin c) p := by
  induction l with
  | nil => intro c p h; exact h
  | cons x t ih =>
      intro c p h
      exact ih _ _ (clockJoin_covers_old h)

private theorem foldl_clockJoin_covers_mem (l : List Op) :
    ∀ (c : Option Op) (p : Op), p ∈ l → clockCovers (l.foldl clockJoin c) p := by
  induction l with
  | nil => intro c p h; simp at h
  | cons x t ih =>
      intro c p h
      rcases List.mem_cons.mp h with rfl | hp
      · exact foldl_clockJoin_covers_old t _ _ (clockJoin_covers_new c p)
      · exact ih _ _ hp

/-- Committing a suffix yields the exact summary of the longer log. -/
theorem Summarizes.advance {s : CheckpointedLogState} {pre suffix : Array Op}
    (hs : s.Summarizes pre)
    (habove : ∀ o ∈ suffix.toList, clockBelow s.clock o = true) :
    (s.advance suffix).Summarizes (pre ++ suffix) := by
  have hagree := checkpoint_suffix_preflight_eq_full_replay hs habove
  constructor
  · exact hagree.state_exact.symm
  · intro p hp
    rw [Array.toList_append] at hp
    rcases List.mem_append.mp hp with hpre | hsuf
    · exact foldl_clockJoin_covers_old _ _ _ (hs.clock_covers p hpre)
    · exact foldl_clockJoin_covers_mem _ _ _ hsuf

/-- Recovery folds the durable admission batches, in order, through the same
commit used by the live runtime. -/
def replayBatches (s : CheckpointedLogState) : List (Array Op) → CheckpointedLogState
  | [] => s
  | batch :: rest => replayBatches (s.advance batch) rest

/-- Every batch is strictly after the clock its predecessors produced. -/
def BatchesAbove : Option Op → List (Array Op) → Prop
  | _, [] => True
  | clock, batch :: rest =>
      (∀ o ∈ batch.toList, clockBelow clock o = true) ∧
        BatchesAbove (advanceClock clock batch) rest

/-- The operations of a batch list, in admission order. -/
def batchOps : List (Array Op) → Array Op
  | [] => #[]
  | batch :: rest => batch ++ batchOps rest

/-- Replaying durable batches summarizes the prefix followed by all of them. -/
theorem replayBatches_summarizes {s : CheckpointedLogState} {pre : Array Op}
    (batches : List (Array Op)) (hs : s.Summarizes pre)
    (habove : BatchesAbove s.clock batches) :
    (replayBatches s batches).Summarizes (pre ++ batchOps batches) := by
  induction batches generalizing s pre with
  | nil => simpa [replayBatches, batchOps] using hs
  | cons batch rest ih =>
      have hnext := Summarizes.advance hs habove.1
      have hrest := ih hnext habove.2
      simpa [replayBatches, batchOps, Array.append_assoc] using hrest

/-- A crash between any two batches loses nothing: resuming from the recovered
state is the same state as never having crashed. -/
theorem replayBatches_append (s : CheckpointedLogState)
    (durable rest : List (Array Op)) :
    replayBatches (replayBatches s durable) rest =
      replayBatches s (durable ++ rest) := by
  induction durable generalizing s with
  | nil => rfl
  | cons batch tail ih => exact ih (s.advance batch)

/-- **Crash recovery is full replay.** Recover the durable batches from genesis
and continue with any later suffix ordered after the recovered clock. The
resulting view, every verdict, the order, and every refusal agree exactly with
replaying the entire log from genesis. -/
theorem crash_recovery_eq_full_replay
    (fp : Array Int) (gs : Array Grant) (rs : Array Nat)
    (durable : List (Array Op)) (suffix : Array Op)
    (hdurable : BatchesAbove none durable)
    (hsuffix : ∀ o ∈ suffix.toList,
      clockBelow (replayBatches (genesis fp gs rs) durable).clock o = true) :
    (replayBatches (genesis fp gs rs) durable).Summarizes (#[] ++ batchOps durable) ∧
      SuffixAgreement (replayBatches (genesis fp gs rs) durable)
        (#[] ++ batchOps durable) suffix := by
  have hrecovered := replayBatches_summarizes durable (genesis_summarizes fp gs rs)
    (by simpa [genesis] using hdurable)
  exact ⟨hrecovered, checkpoint_suffix_preflight_eq_full_replay hrecovered hsuffix⟩

/-! ## §6. Concrete witness and falsifiers -/

private theorem mergeSort_two {α : Type _} {le : α → α → Bool} {a b : α} :
    [a, b].mergeSort le = if le a b then [a, b] else [b, a] := by
  rw [List.mergeSort]
  simp [List.merge]

/-- Three structural roots. -/
private def witnessBase : Array Int := #[-1, -1, -1]

/-- One root-issued grant covering all three nodes. -/
private def witnessGrants : Array Grant := #[⟨1, 0, 3⟩]

private def moveOne : Op := { lamport := 1, replica := 0, child := 1, dest := 0, cite := 1 }
private def moveTwo : Op := { lamport := 2, replica := 0, child := 2, dest := 1, cite := 1 }

private theorem witness_active :
    activeFrom witnessGrants #[] 1 = true := by
  rw [activeFrom, show findGrant witnessGrants 1 = some ⟨1, 0, 3⟩ from rfl]
  simp [isRevoked]

private theorem witness_revoked :
    activeFrom witnessGrants #[1] 1 = false := by
  rw [activeFrom, show findGrant witnessGrants 1 = some ⟨1, 0, 3⟩ from rfl]
  simp [isRevoked]

private theorem permitted_of_active {rs : Array Nat} {o : Op}
    (hactive : activeFrom witnessGrants rs 1 = true)
    (hcite : o.cite = 1) (hchild : o.child < 3) :
    permittedOp witnessGrants rs o = true := by
  simp only [permittedOp, hcite,
    show findGrant witnessGrants 1 = some ⟨1, 0, 3⟩ from rfl, hactive,
    Bool.true_and, decide_eq_true_eq]
  exact hchild

private theorem refused_of_revoked {o : Op} (hcite : o.cite = 1) :
    permittedOp witnessGrants #[1] o = false := by
  simp only [permittedOp, hcite,
    show findGrant witnessGrants 1 = some ⟨1, 0, 3⟩ from rfl, witness_revoked,
    Bool.false_and]

private theorem replay_one_permitted {rs : Array Nat} {fp : Array Int} {o : Op}
    (hp : permittedOp witnessGrants rs o = true) :
    gatedReplayFull witnessGrants rs fp #[o] =
      [(o, 0)].foldl (applyOpFull fp fp.size)
        ⟨Array.replicate fp.size (-2), #[2]⟩ := by
  simp [gatedReplayFull, initStatuses, hp, List.zipIdx]

private theorem replay_one_refused {rs : Array Nat} {fp : Array Int} {o : Op}
    (hp : permittedOp witnessGrants rs o = false) :
    gatedReplayFull witnessGrants rs fp #[o] =
      ⟨Array.replicate fp.size (-2), #[3]⟩ := by
  simp [gatedReplayFull, initStatuses, hp, List.zipIdx]

private theorem replay_two_ordered {rs : Array Nat} {fp : Array Int} {a b : Op}
    (ha : permittedOp witnessGrants rs a = true)
    (hb : permittedOp witnessGrants rs b = true)
    (hle : List.zipIdxLE opLe (a, 0) (b, 1) = true) :
    gatedReplayFull witnessGrants rs fp #[a, b] =
      [(a, 0), (b, 1)].foldl (applyOpFull fp fp.size)
        ⟨Array.replicate fp.size (-2), #[2, 2]⟩ := by
  have hfilter : ([(a, 0), (b, 1)] : List (Op × Nat)).filter
      (fun p => permittedOp witnessGrants rs p.1) = [(a, 0), (b, 1)] := by
    simp [ha, hb]
  have hstatuses : initStatuses witnessGrants rs #[a, b] = #[2, 2] := by
    simp [initStatuses, ha, hb]
  unfold gatedReplayFull
  rw [hstatuses, show (#[a, b] : Array Op).toList.zipIdx = [(a, 0), (b, 1)] from rfl,
    hfilter, mergeSort_two, hle]
  rfl

/-- **Concrete witness.** The keystone's premises are satisfiable on a real
two-move log: the checkpoint after the first move, plus the rebased one-move
suffix, computes the full replay's exact view and verdicts. -/
theorem checkpoint_witness :
    let cp : CheckpointedLogState :=
      { firstParent := witnessBase, grants := witnessGrants, revocations := #[],
        overrides := #[-2, 0, -2], clock := some moveOne }
    cp.Summarizes #[moveOne] ∧ clockBelow cp.clock moveTwo = true ∧
      cp.base = #[-1, 0, -1] ∧
      (cp.preflight #[moveTwo]).overrides = #[-2, -2, 1] ∧
      (cp.preflight #[moveTwo]).statuses = #[0] ∧
      (gatedReplayFull witnessGrants #[] witnessBase #[moveOne, moveTwo]).overrides =
        #[-2, 0, 1] ∧
      (gatedReplayFull witnessGrants #[] witnessBase #[moveOne, moveTwo]).statuses =
        #[0, 0] := by
  intro cp
  have hone : permittedOp witnessGrants #[] moveOne = true :=
    permitted_of_active witness_active rfl (by decide)
  have htwo : permittedOp witnessGrants #[] moveTwo = true :=
    permitted_of_active witness_active rfl (by decide)
  have hbase : cp.base = #[-1, 0, -1] := by decide
  have hsummary : cp.Summarizes #[moveOne] := by
    constructor
    · show (#[-2, 0, -2] : Array Int) =
        (gatedReplayFull witnessGrants #[] witnessBase #[moveOne]).overrides
      rw [replay_one_permitted hone]
      decide
    · intro p hp
      have hp' : p = moveOne := by simpa using hp
      subst hp'
      exact opLe_refl _
  have hdelta : cp.preflight #[moveTwo] =
      [(moveTwo, 0)].foldl (applyOpFull #[-1, 0, -1] (#[-1, 0, -1] : Array Int).size)
        ⟨Array.replicate (#[-1, 0, -1] : Array Int).size (-2), #[2]⟩ := by
    show gatedReplayFull witnessGrants #[] cp.base #[moveTwo] = _
    rw [hbase, replay_one_permitted htwo]
  have hfull := replay_two_ordered (fp := witnessBase) hone htwo
    (show List.zipIdxLE opLe (moveOne, 0) (moveTwo, 1) = true by decide)
  refine ⟨hsummary, by decide, hbase, ?_, ?_, ?_, ?_⟩
  · rw [hdelta]; decide
  · rw [hdelta]; decide
  · rw [hfull]; decide
  · rw [hfull]; decide

/-- A checkpoint that revoked grant 1. Its summarized prefix is empty, so it is
valid at genesis. -/
private def revokedCheckpoint : CheckpointedLogState :=
  CheckpointedLogState.genesis witnessBase witnessGrants #[1]

/-- **Tooth: authority is load-bearing.** Dropping the revocation frontier from
a valid checkpoint flips a refused move to an applied one, so no equivalence
with full replay can survive it. -/
theorem tooth_dropped_revocation_breaks_equivalence :
    revokedCheckpoint.Summarizes #[] ∧
      (gatedReplayFull revokedCheckpoint.grants revokedCheckpoint.revocations
        revokedCheckpoint.firstParent (#[] ++ #[moveOne])).statuses = #[3] ∧
      (revokedCheckpoint.preflight #[moveOne]).statuses = #[3] ∧
      (revokedCheckpoint.dropRevocations.preflight #[moveOne]).statuses = #[0] ∧
      ¬ ∀ (s : CheckpointedLogState) (pre suffix : Array Op),
        s.Summarizes pre →
        (∀ o ∈ suffix.toList, clockBelow s.clock o = true) →
        (gatedReplayFull s.grants s.revocations s.firstParent (pre ++ suffix)).statuses =
          (gatedReplayFull s.grants s.revocations s.firstParent pre).statuses ++
            (s.dropRevocations.preflight suffix).statuses := by
  have hsummary : revokedCheckpoint.Summarizes #[] :=
    CheckpointedLogState.genesis_summarizes _ _ _
  have hrefused : permittedOp witnessGrants #[1] moveOne = false :=
    refused_of_revoked rfl
  have hpermitted : permittedOp witnessGrants #[] moveOne = true :=
    permitted_of_active witness_active rfl (by decide)
  have hfull : (gatedReplayFull witnessGrants #[1] witnessBase (#[] ++ #[moveOne])).statuses =
      #[3] := by
    rw [show (#[] ++ #[moveOne] : Array Op) = #[moveOne] from rfl,
      replay_one_refused hrefused]
  have hhonest : (revokedCheckpoint.preflight #[moveOne]).statuses = #[3] := by
    show (gatedReplayFull witnessGrants #[1] revokedCheckpoint.base #[moveOne]).statuses = _
    rw [replay_one_refused hrefused]
  have hdropped : (revokedCheckpoint.dropRevocations.preflight #[moveOne]).statuses = #[0] := by
    show (gatedReplayFull witnessGrants #[] revokedCheckpoint.dropRevocations.base
      #[moveOne]).statuses = _
    rw [replay_one_permitted hpermitted]
    decide
  refine ⟨hsummary, hfull, hhonest, hdropped, ?_⟩
  intro hall
  have h := hall revokedCheckpoint #[] #[moveOne] hsummary (by
    intro o _
    rfl)
  have hempty : (gatedReplayFull revokedCheckpoint.grants revokedCheckpoint.revocations
      revokedCheckpoint.firstParent #[]).statuses = #[] := by
    simp [gatedReplayFull, initStatuses]
  rw [hempty, hdropped] at h
  have hfull' : (gatedReplayFull revokedCheckpoint.grants revokedCheckpoint.revocations
      revokedCheckpoint.firstParent (#[] ++ #[moveOne])).statuses = #[3] := hfull
  rw [hfull'] at h
  exact absurd h (by decide)

/-- A local counterexample check requires a kernel proof of the negated claim. -/
local macro "#tooth " claim:term " refuted_by " evidence:term : command =>
  `(example : ¬ $claim := $evidence)

#tooth (∀ (s : CheckpointedLogState) (pre suffix : Array Op),
    s.Summarizes pre →
    (∀ o ∈ suffix.toList, clockBelow s.clock o = true) →
    (gatedReplayFull s.grants s.revocations s.firstParent (pre ++ suffix)).statuses =
      (gatedReplayFull s.grants s.revocations s.firstParent pre).statuses ++
        (s.dropRevocations.preflight suffix).statuses)
  refuted_by tooth_dropped_revocation_breaks_equivalence.2.2.2.2

private def lateMove : Op := { lamport := 2, replica := 0, child := 0, dest := 1, cite := 1 }
private def earlyMove : Op := { lamport := 1, replica := 0, child := 1, dest := 0, cite := 1 }

/-- **Tooth: the clock is load-bearing.** Take a valid checkpoint after a later
move, then preflight an *older* move that violates the clock premise. The
bounded answer disagrees with full replay, which is why such an operation must
be replayed from an earlier checkpoint. -/
theorem tooth_out_of_order_breaks_equivalence :
    let cp : CheckpointedLogState :=
      { firstParent := #[-1, -1, -1], grants := witnessGrants, revocations := #[],
        overrides := #[1, -2, -2], clock := some lateMove }
    cp.Summarizes #[lateMove] ∧
      clockBelow cp.clock earlyMove = false ∧
      (cp.preflight #[earlyMove]).statuses = #[1] ∧
      (gatedReplayFull witnessGrants #[] #[-1, -1, -1] #[lateMove, earlyMove]).statuses =
        #[1, 0] := by
  intro cp
  have hlate : permittedOp witnessGrants #[] lateMove = true :=
    permitted_of_active witness_active rfl (by decide)
  have hearly : permittedOp witnessGrants #[] earlyMove = true :=
    permitted_of_active witness_active rfl (by decide)
  have hsummary : cp.Summarizes #[lateMove] := by
    constructor
    · show (#[1, -2, -2] : Array Int) =
        (gatedReplayFull witnessGrants #[] #[-1, -1, -1] #[lateMove]).overrides
      rw [replay_one_permitted hlate]
      decide
    · intro p hp
      have hp' : p = lateMove := by simpa using hp
      subst hp'
      exact opLe_refl _
  have hbase : cp.base = #[1, -1, -1] := by decide
  have hdelta : (cp.preflight #[earlyMove]).statuses = #[1] := by
    show (gatedReplayFull witnessGrants #[] cp.base #[earlyMove]).statuses = _
    rw [hbase, replay_one_permitted hearly]
    decide
  have hfull : (gatedReplayFull witnessGrants #[] #[-1, -1, -1]
      #[lateMove, earlyMove]).statuses = #[1, 0] := by
    have hfilter : ([(lateMove, 0), (earlyMove, 1)] : List (Op × Nat)).filter
        (fun p => permittedOp witnessGrants #[] p.1) =
        [(lateMove, 0), (earlyMove, 1)] := by
      simp [hlate, hearly]
    have hinit : initStatuses witnessGrants #[] #[lateMove, earlyMove] = #[2, 2] := by
      simp [initStatuses, hlate, hearly]
    unfold gatedReplayFull
    rw [hinit,
      show (#[lateMove, earlyMove] : Array Op).toList.zipIdx =
        [(lateMove, 0), (earlyMove, 1)] from rfl,
      hfilter, mergeSort_two,
      show List.zipIdxLE opLe (lateMove, 0) (earlyMove, 1) = false by decide]
    decide
  exact ⟨hsummary, by decide, hdelta, hfull⟩

end Uwueave.IncrementalCheckpointPreflight
