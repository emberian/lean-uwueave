/-
# Uwueave.ListProofs -- small structural lemmas shared by tree traversals

`Sequence`, `SeqKernel`, and `Fugue` each flatten a duplicate-free family of
subtree chunks.  Their domain-specific work proves two facts: each chunk emits
an element at most once, and chunks rooted at distinct siblings are disjoint.
The list induction which turns those facts into a duplicate-free `flatMap` is
independent of trees, anchors, ranks, and fuel, so it lives here once.

This module is proof-only.  It changes no executable traversal and introduces
no search or automation.
-/
import Std

namespace Uwueave.ListProofs

universe u v

/-- Flattening a duplicate-free index list preserves duplicate-freedom when
every indexed chunk is duplicate-free and chunks at distinct indices have
disjoint membership. -/
theorem flatMap_nodup_of_nodup_of_pairwise_disjoint
    {α : Type u} {β : Type v} (f : α → List β) {xs : List α}
    (indices : xs.Nodup)
    (chunks : ∀ x, x ∈ xs → (f x).Nodup)
    (separate : ∀ x, x ∈ xs → ∀ y, y ∈ xs → x ≠ y →
      ∀ value, value ∈ f x → value ∈ f y → False) :
    (xs.flatMap f).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x rest ih =>
      rw [List.flatMap_cons, List.nodup_append]
      obtain ⟨xNotMem, restNodup⟩ := List.nodup_cons.mp indices
      refine ⟨chunks x List.mem_cons_self, ?_, ?_⟩
      · exact ih restNodup
          (fun y hy => chunks y (List.mem_cons_of_mem x hy))
          (fun y hy z hz hne => separate y (List.mem_cons_of_mem x hy)
            z (List.mem_cons_of_mem x hz) hne)
      · intro left leftMem right rightMem
        obtain ⟨y, yMem, rightMemY⟩ := List.mem_flatMap.mp rightMem
        intro equal
        subst right
        have xNeY : x ≠ y := fun hxy => xNotMem (hxy ▸ yMem)
        exact separate x List.mem_cons_self y (List.mem_cons_of_mem x yMem)
          xNeY left leftMem rightMemY

/-- Count form of `flatMap_nodup_of_nodup_of_pairwise_disjoint`.  This is the
shape consumed by the three fueled traversal inductions. -/
theorem flatMap_count_le_one_of_nodup_of_pairwise_disjoint
    {α : Type u} {β : Type v} [BEq β] [LawfulBEq β]
    (f : α → List β) {xs : List α}
    (indices : xs.Nodup)
    (chunks : ∀ x, x ∈ xs → ∀ value, (f x).count value ≤ 1)
    (separate : ∀ x, x ∈ xs → ∀ y, y ∈ xs → x ≠ y →
      ∀ value, value ∈ f x → value ∈ f y → False) :
    ∀ value, (xs.flatMap f).count value ≤ 1 := by
  apply List.nodup_iff_count.mp
  apply flatMap_nodup_of_nodup_of_pairwise_disjoint f indices
  · intro x hx
    exact List.nodup_iff_count.mpr (chunks x hx)
  · exact separate

/-- A selected `flatMap` chunk is a sublist of the whole flattening. -/
theorem sublist_flatMap_of_mem {α : Type u} {β : Type v} (f : α → List β) :
    ∀ (xs : List α) (x : α), x ∈ xs → (f x).Sublist (xs.flatMap f) := by
  intro xs
  induction xs with
  | nil => intro x hx; cases hx
  | cons head tail ih =>
      intro x hx
      rw [List.flatMap_cons]
      cases hx with
      | head => exact List.sublist_append_left _ _
      | tail _ hx => exact (ih x hx).trans (List.sublist_append_right _ _)

/-! ## Acceptance fixtures -/

private def fixtureChunk : Bool → List Nat
  | false => [0, 1]
  | true => [2, 3]

private theorem fixtureChunk_nodup (index : Bool) :
    (fixtureChunk index).Nodup := by
  cases index <;> decide

private theorem fixtureChunk_separate (left right : Bool) (different : left ≠ right)
    (value : Nat) (leftMem : value ∈ fixtureChunk left)
    (rightMem : value ∈ fixtureChunk right) : False := by
  cases left <;> cases right
  · exact absurd rfl different
  · simp [fixtureChunk] at leftMem rightMem
    omega
  · simp [fixtureChunk] at leftMem rightMem
    omega
  · exact absurd rfl different

/-- The generic theorem accepts two concrete disjoint chunks. -/
theorem fixture_flatMap_nodup :
    ([false, true].flatMap fixtureChunk).Nodup := by
  apply flatMap_nodup_of_nodup_of_pairwise_disjoint fixtureChunk
  · decide
  · intro index _
    exact fixtureChunk_nodup index
  · intro left _ right _ different value leftMem rightMem
    exact fixtureChunk_separate left right different value leftMem rightMem

/-- The count-facing wrapper computes the same fixture bound. -/
theorem fixture_flatMap_count_le_one :
    ∀ value, ([false, true].flatMap fixtureChunk).count value ≤ 1 := by
  apply flatMap_count_le_one_of_nodup_of_pairwise_disjoint fixtureChunk
  · decide
  · intro index _ value
    exact List.nodup_iff_count.mp (fixtureChunk_nodup index) value
  · intro left _ right _ different value leftMem rightMem
    exact fixtureChunk_separate left right different value leftMem rightMem

/-- The shared sublist lemma retains the selected right-hand chunk. -/
theorem fixture_chunk_sublist :
    (fixtureChunk true).Sublist ([false, true].flatMap fixtureChunk) :=
  sublist_flatMap_of_mem fixtureChunk [false, true] true (by simp)

end Uwueave.ListProofs
