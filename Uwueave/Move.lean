/-
# Uwueave.Move — nonmonotonic edits by the derived-view (op-log) pattern.

`Acyclicity.lean` ends at the island's shore: append-only, parents-fixed
insertion is free, but **node moving** — which universal-weave's DAG weave
supports, and which every filesystem-shaped application wants — re-points
existing edges. Concurrent moves can close a cycle
(`acyclicity_not_iconfluent`), so a naive "the graph is the CRDT" design is
ruled out by necessity, not by lack of cleverness.

The pattern that works — Kleppmann–Mulligan–Gomes–Beresford's move operation,
and in general every op-based design of this family — is:

  **Replicate the monotone thing. Derive the invariant-bearing thing.**

The replicated state is the *set of operations ever issued* — a grow-only set,
trivially a CRDT. The tree/DAG a user sees is a **pure function** of that set:
order the ops by timestamp, apply each, *skip* any op whose application would
violate the invariant. Convergence is inherited from the log (a function of
equal inputs is equal); the invariant holds at every replica *by construction*
of the interpreter.

This file proves the pattern's guarantee once, generically
(`derived_view_sec`), and then — because no honest account stops there — proves
its **price** on a concrete miniature: the derived view is *not stable*. An op
you already applied can be retroactively skipped when an older remote op
arrives (`view_not_stable`). The square edit's nonmonotonicity did not vanish;
it moved out of the merge (where it would block convergence) and into the
*meaning* of your local history (where it is an anomaly users can see —
"my move undid itself"). That trade is usually right for a loom and it is
still a trade.
-/
import Uwueave.Acyclicity

namespace Uwueave.Move

open Uwueave Uwueave.Catalog

/-! ## §1. The pattern's guarantee, once and generically.

`L` is any log-shaped CRDT (any `MergeState`); `interp` is any deterministic
interpreter; `I` is any view invariant the interpreter enforces by
construction. Nothing else is assumed — that is the pattern's whole appeal. -/

section DerivedView

variable {L View : Type u} [MergeState L]

/-- **Strong eventual consistency + invariant preservation of a derived view,
in one statement.** For any replica history: deltas may arrive in either order
(1), duplicated (2), and the view is legal at every point regardless (3).

(1) and (2) are the log's merge laws pushed through `interp` — this is why the
pattern asks the *log* to be the CRDT and asks nothing of the view. (3) is the
interpreter's enforcement obligation `henf`, discharged per-design (for the
move op: "skip cycle-creating moves", proved for a miniature in §2). -/
theorem derived_view_sec (interp : L → View) (I : View → Prop)
    (henf : ∀ log, I (interp log)) (base Δ₁ Δ₂ : L) :
    interp ((base ⊔ Δ₁) ⊔ Δ₂) = interp ((base ⊔ Δ₂) ⊔ Δ₁)
    ∧ interp ((base ⊔ Δ₁) ⊔ Δ₁) = interp (base ⊔ Δ₁)
    ∧ I (interp ((base ⊔ Δ₁) ⊔ Δ₂)) := by
  refine ⟨?_, ?_, henf _⟩
  · rw [merge_assoc, merge_comm Δ₁ Δ₂, ← merge_assoc]
  · rw [merge_assoc, merge_idem]

end DerivedView

/-! ## §2. The price, on a concrete miniature.

Two nodes `n₀`(= `false`) and `n₁`(= `true`) under an implicit root; two move
ops. The interpreter is the Kleppmann rule restricted to this universe: apply
in timestamp order, skip a move that would create a cycle.

  * `o₁` (t = 2): move n₀ under n₁.
  * `o₂` (t = 1): move n₁ under n₀.

A replica holding only `o₁` shows n₀ under n₁. When `o₂` arrives — *older*,
so it sorts first — the replay applies `o₂`, then finds `o₁` cycle-creating
and skips it. The final view keeps `o₂`'s move and drops `o₁`'s: the edit the
local user watched happen has been un-happened by an op from the past. -/

/-- A move operation: at Lamport time `t`, re-parent `child` under `dest`
(`none` = the root). -/
structure MoveOp where
  t     : Nat
  child : Bool
  dest  : Option Bool
  deriving DecidableEq, Repr

/-- t = 2: move n₀ under n₁. -/
def o₁ : MoveOp := ⟨2, false, some true⟩
/-- t = 1: move n₁ under n₀. -/
def o₂ : MoveOp := ⟨1, true, some false⟩

/-- The view: each node's parent (`none` = root). -/
abbrev Parent := Bool → Option Bool

/-- The timestamp-ordered, cycle-skipping replay, specialized to the two-op
universe (ops other than `o₁`, `o₂` are ignored; the general algorithm is the
same replay over the whole log). The four branches are the four possible
sub-logs, each replayed by hand so every skip is visible:

  * only `o₁`      → n₀ under n₁.
  * only `o₂`      → n₁ under n₀.
  * both — `o₂` first (t=1 < t=2), then `o₁` **skipped** (n₁ is under n₀, so
    parenting n₀ under n₁ closes a cycle) → n₁ under n₀ alone.
  * neither        → both under root. -/
def miniInterp (log : GSet MoveOp) : Parent :=
  if log o₁ then
    if log o₂ then fun n => if n = true then some false else none
    else fun n => if n = false then some true else none
  else
    if log o₂ then fun n => if n = true then some false else none
    else fun _ => none

/-- Two-node acyclicity of a parent view: the nodes are not each other's
parents. -/
def ViewAcyclic (p : Parent) : Prop :=
  ¬ (p false = some true ∧ p true = some false)

/-- **The interpreter enforces acyclicity by construction** — the obligation
`derived_view_sec` asks for, discharged for the miniature. (For the full
algorithm this is Kleppmann et al.'s Isabelle-verified Theorem 1; the shape of
the argument is the same case analysis, over replay prefixes.) -/
theorem miniInterp_acyclic (log : GSet MoveOp) : ViewAcyclic (miniInterp log) := by
  unfold miniInterp ViewAcyclic
  by_cases h1 : log o₁ = true <;> by_cases h2 : log o₂ = true <;>
    simp [h1, h2]

/-- Log inclusion, pointwise (the observable "has seen at least these ops"). -/
def LogLe (l l' : GSet MoveOp) : Prop := ∀ o, l o = true → l' o = true

/-- ⚠ **The derived view is NOT stable under log growth.** The log with only
`o₁` shows n₀ under n₁; the *larger* log with both ops does not. Growth of the
monotone substrate does not grow the view — a fact any UI over this pattern
must design for (Kleppmann surfaces it as moves that "jump back"; a loom will
surface it as a reparented subtree snapping to a different branch when a peer's
older edit syncs in). This is the residual square-ness of the square edit, and
no op-log design removes it: it is the arbitration, made visible. -/
theorem view_not_stable :
    ∃ l l' : GSet MoveOp, LogLe l l'
      ∧ miniInterp l  false = some true
      ∧ miniInterp l' false ≠ some true := by
  refine ⟨fun o => o == o₁, fun o => o == o₁ || o == o₂, ?_, by decide, by decide⟩
  intro o h
  simp at h
  subst h
  decide

end Uwueave.Move
