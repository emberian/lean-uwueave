/-
# Uwueave.MVRegister — the multi-value register: keep the fork, show the fork.

`Catalog.lean` proved the LWW pair: a lone LWW register is invariant-proof
*because its join throws one write away*, and that silent loss is exactly what
breaks relational invariants across two registers. The **multi-value register**
is the other end of the trade: keep *every* write not causally superseded, and
surface concurrent writes as an explicit conflict set for the application (or
the human) to resolve.

For a loom this is not a consolation prize — it is the product. A weave *wants*
forks to be visible, navigable objects; "resolve" is often "keep both branches
forever". The MV-register is the single-slot version of that stance, and it is
also the substrate on which multi-user undo/redo is well-posed (Kleppmann,
PaPoC'24: undo = a new write of an old value at a *fresh* clock — an ordinary
op, no new machinery).

Construction: the replicated state is the grow-only set of tagged writes
(value, vector clock) — monotone, an inherited `MergeState`, nothing to prove.
The *register value* is a derived view: the writes not strictly dominated by
another present write. This is the derived-view pattern of `Move.lean` again
(`derived_view_sec` applies verbatim), with the view-level guarantees proved
here:

  * `view_antichain` — no visible write supersedes another: what you see is
    exactly the causal frontier;
  * `conflict_surfaces` — genuinely concurrent writes are **both** visible
    after merge, where LWW would silently pick one;
  * `resolution_is_a_write` — clearing a conflict is an ordinary write at a
    dominating clock; the merge has no special resolution case to get wrong.
-/
import Uwueave.Move

namespace Uwueave.MVRegister

open Uwueave Uwueave.Catalog

/-- A tagged write: value, then a two-replica vector clock (kept concrete —
`(Nat × Nat)` — so every example below is decidable; the construction is
uniform in the index type). -/
abbrev Write := Nat × (Nat × Nat)

/-- The replicated state: every write ever issued. Grow-only; the register
never merges *values*, only accumulates observations. -/
abbrev MVReg := GSet Write

example : MergeState MVReg := inferInstance

/-- `Dom c c'`: clock `c'` strictly dominates `c` (componentwise ≤, not
equal) — the write carrying `c` is causally superseded by one carrying `c'`. -/
def Dom (c c' : Nat × Nat) : Prop :=
  c.1 ≤ c'.1 ∧ c.2 ≤ c'.2 ∧ c ≠ c'

instance (c c' : Nat × Nat) : Decidable (Dom c c') := by
  unfold Dom; infer_instance

/-- The derived view: a write is visible iff present and not strictly
dominated by any present write. This is a pure function of the state —
`derived_view_sec` (order-independence, redelivery-immunity) applies to it
as-is. -/
def InView (s : MVReg) (w : Write) : Prop :=
  s w = true ∧ ∀ w', s w' = true → ¬ Dom w.2 w'.2

/-- **The view is an antichain**: no visible write is dominated by any present
write — in particular not by another visible one. (By construction; the point
of naming it is that this is the register's whole contract.) -/
theorem view_antichain (s : MVReg) (w w' : Write)
    (hw : InView s w) (hw' : s w' = true) : ¬ Dom w.2 w'.2 :=
  hw.2 w' hw'

/-! ### The concrete stories, as theorems -/

/-- Replica A's write: value 5 at clock (1,0). -/
def wA : Write := (5, (1, 0))
/-- Replica B's concurrent write: value 7 at clock (0,1). -/
def wB : Write := (7, (0, 1))
/-- A later resolving write: value 9 at clock (1,1), above both. -/
def wR : Write := (9, (1, 1))

/-- The merged state holding both concurrent writes. -/
def sAB : MVReg := (fun w => w == wA) ⊔ (fun w => w == wB)

/-- The state after a resolution write lands on top. -/
def sABR : MVReg := sAB ⊔ (fun w => w == wR)

/-- **Concurrent writes both surface.** After merging A's and B's replicas,
*both* writes are in view — the conflict is an object the application can
render (two branches of a one-slot weave), not a coin-flip. Compare
`Catalog.lww_every_invariant_iconfluent`'s selection: LWW here would show
exactly one of `5`, `7`, with no trace of the other. -/
theorem conflict_surfaces : InView sAB wA ∧ InView sAB wB := by
  constructor <;> refine ⟨by decide, ?_⟩ <;>
    · intro w' h'
      have hw' : w' = wA ∨ w' = wB := by
        simp [sAB, gset_mem_merge, wA, wB] at h'
        rcases h' with h | h
        · exact Or.inl (by cases w'; simp_all [wA])
        · exact Or.inr (by cases w'; simp_all [wB])
      rcases hw' with h | h <;> (subst h; decide)

/-- **Resolution is just a write.** After `wR` (clock above both) lands, the
old conflict is gone from view and the resolution is visible. No special merge
case, no resolution protocol — the same lattice all the way down. -/
theorem resolution_is_a_write : ¬ InView sABR wA ∧ InView sABR wR := by
  constructor
  · intro ⟨_, hnodom⟩
    exact hnodom wR (by decide) (by decide)
  · refine ⟨by decide, ?_⟩
    intro w' h'
    have hw' : w' = wA ∨ w' = wB ∨ w' = wR := by
      simp [sABR, sAB, gset_mem_merge, wA, wB, wR] at h'
      rcases h' with (h | h) | h
      · exact Or.inl (by cases w'; simp_all [wA])
      · exact Or.inr (Or.inl (by cases w'; simp_all [wB]))
      · exact Or.inr (Or.inr (by cases w'; simp_all [wR]))
    rcases hw' with h | h | h <;> (subst h; decide)

end Uwueave.MVRegister
