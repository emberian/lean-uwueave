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

§3 bridges the miniature to the executable kernel (`Uwueave/Exec.lean`):
the four-branch table and the kernel's sort-and-fold are the same rule, and
the real `absReplay`, run on the fixed 2-node encoding of each sub-log,
produces exactly the table's answer — machine-checked, on this universe.
-/
import Uwueave.Acyclicity
import Uwueave.Exec

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

/-! ## §3. The bridge to the executable kernel (`Uwueave/Exec.lean`)

`miniInterp` presents the Kleppmann rule as a four-branch table; the kernel
presents it as sort-and-fold. This section machine-checks **"same rule, two
presentations"** on the miniature, in two steps:

  * **presentation** — `miniReplay`, defined the kernel's way (filter the
    log's present ops, sort by the total order, fold apply-if-no-cycle),
    equals the table on every log (`miniReplay_eq_miniInterp`);
  * **value** — the real `Exec.absReplay`, run on the fixed 2-node encoding
    of each of the four sub-logs, produces exactly the override array whose
    `effParent` reading is `miniInterp`'s answer (the four arrays by name,
    then `absReplay_matches_miniInterp`); and the kernel's v2 status block
    reports `o₁` skipped-by-cycle on the both-ops log
    (`absReplayFull_both_statuses`) — `view_not_stable`, now observable.

⚠ **Scope, stated plainly**: the two-op, two-node universe only — this
section is the concrete, symbol-level anchor. The *general* connection of
the kernel to the derived-view abstraction is not here and not open: it is
`ExecRefine` §6 (`kernel_derived_view_sec`, `absReplay_ext_mem` — the replay
is a function of the op set, with `derived_view_sec`'s clauses proved for
`absReplay` itself, over arbitrary universes). -/

/-- Does the effective-ancestor chain from `start` pass through `needle`?
Fuel-totalized mirror of the kernel's `chainHits`, on the miniature's view
type. -/
def miniChainHits (p : Parent) (start needle : Bool) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
    if start = needle then true
    else
      match p start with
      | none => false
      | some q => miniChainHits p q needle fuel

/-- Apply one move — or skip it, per the cycle rule — the kernel's `applyOp`
on the miniature: a move to root always applies; a move under `d` applies
only when the chain from `d` misses the child. Fuel `3` is the kernel's
literal `n + 1` at `n = 2`. -/
def miniApply (p : Parent) (op : MoveOp) : Parent :=
  match op.dest with
  | none => fun n => if n = op.child then none else p n
  | some d =>
    if miniChainHits p d op.child 3 then p
    else fun n => if n = op.child then some d else p n

/-- **The kernel-shaped replay** of the two-op universe: filter the log's
present ops, sort by timestamp (the total order — the two timestamps are
distinct, so the tie-breakers of the full `(lamport, replica, child, dest)`
order never fire here), and fold apply-if-no-cycle over the all-root view.
Contrast `miniInterp`: the same rule presented as a four-branch table. -/
def miniReplay (log : GSet MoveOp) : Parent :=
  (([o₁, o₂].filter log).mergeSort (fun a b => a.t ≤ b.t)).foldl miniApply
    (fun _ => none)

private theorem mergeSort_pair {α : Type _} {le : α → α → Bool} {a b : α} :
    [a, b].mergeSort le = if le a b then [a, b] else [b, a] := by
  rw [List.mergeSort]
  simp [List.merge]

/-- **The bridge, presentation side**: the kernel-shaped replay and the
four-branch table are the same function of the log. The proof is exactly the
case analysis over the four sub-logs — only membership of `o₁` and `o₂`
matters to either side. -/
theorem miniReplay_eq_miniInterp (log : GSet MoveOp) :
    miniReplay log = miniInterp log := by
  unfold miniReplay miniInterp
  by_cases h1 : log o₁ = true <;> by_cases h2 : log o₂ = true <;>
    simp only [List.filter_cons, List.filter_nil, h1, h2, if_true, if_false,
      Bool.false_eq_true, List.mergeSort_nil, List.mergeSort_singleton,
      mergeSort_pair] <;>
    · funext n
      cases n <;> rfl

/-- Node encoding of the fixed 2-node layout: `n₀`(= `false`) ↦ index `0`,
`n₁`(= `true`) ↦ index `1`. -/
def encNode (b : Bool) : Nat := if b then 1 else 0

/-- Destination encoding: root ↦ `-1`, a node ↦ its index. -/
def encDest : Option Bool → Int
  | none => -1
  | some b => (encNode b : Int)

/-- Op encoding under the fixed layout: `lamport` = the timestamp, `replica`
= `0` (the miniature has no replica field; timestamps are distinct so the
tie-breaker is never consulted). -/
def encOp (op : MoveOp) : Exec.Op :=
  { lamport := UInt64.ofNat op.t
    replica := 0
    child   := encNode op.child
    dest    := encDest op.dest }

/-- The miniature's structural base: two root nodes (`firstParent = [-1, -1]`,
the request's parent block for the 2-node layout). -/
def miniBase : Array Int := #[-1, -1]

/-- A sub-log, encoded as the kernel's op array (present ops only, `o₁`
slot first — the kernel sorts, so request order is immaterial to the view). -/
def encLog (log : GSet MoveOp) : Array Exec.Op :=
  (if log o₁ then #[encOp o₁] else #[]) ++ (if log o₂ then #[encOp o₂] else #[])

/-- Read one override/effective-parent word of the 2-node layout back into
the miniature's view: negative = root, `0`/`1` = the node with that index. -/
def decNode (v : Int) : Option Bool := if v < 0 then none else some (v == 1)

/- The mergeSort layer, discharged once per arity so the remaining kernel
computation is structural and `decide` can finish each concrete case. -/

private theorem absReplay_zero (fp : Array Int) :
    Exec.absReplay fp #[] =
      (([] : List (Exec.Op × Nat)).foldl (Exec.applyOpFull fp fp.size)
        ⟨Array.replicate fp.size (-2), Array.replicate 0 2⟩).overrides := by
  simp only [Exec.absReplay, Exec.absReplayFull]
  rw [show (#[] : Array Exec.Op).toList.zipIdx = [] from rfl, List.mergeSort_nil]
  rfl

private theorem absReplay_one (fp : Array Int) (e : Exec.Op) :
    Exec.absReplay fp #[e] =
      ([(e, 0)].foldl (Exec.applyOpFull fp fp.size)
        ⟨Array.replicate fp.size (-2), Array.replicate 1 2⟩).overrides := by
  simp only [Exec.absReplay, Exec.absReplayFull]
  rw [show (#[e] : Array Exec.Op).toList.zipIdx = [(e, 0)] from rfl,
    List.mergeSort_singleton]
  rfl

private theorem absReplayFull_two (fp : Array Int) (e₁ e₂ : Exec.Op) :
    Exec.absReplayFull fp #[e₁, e₂] =
      ((if List.zipIdxLE Exec.opLe (e₁, 0) (e₂, 1)
          then [(e₁, 0), (e₂, 1)] else [(e₂, 1), (e₁, 0)]).foldl
        (Exec.applyOpFull fp fp.size)
        ⟨Array.replicate fp.size (-2), Array.replicate 2 2⟩) := by
  simp only [Exec.absReplayFull]
  rw [show (#[e₁, e₂] : Array Exec.Op).toList.zipIdx = [(e₁, 0), (e₂, 1)] from rfl,
    mergeSort_pair]
  rfl

/-- Kernel value, sub-log ∅: no overrides. -/
theorem absReplay_mini_neither : Exec.absReplay miniBase #[] = #[-2, -2] := by
  rw [absReplay_zero]; decide

/-- Kernel value, sub-log `{o₁}`: node 0 overridden under node 1 —
`miniInterp`'s "n₀ under n₁". -/
theorem absReplay_mini_only₁ :
    Exec.absReplay miniBase #[encOp o₁] = #[1, -2] := by
  rw [absReplay_one]; decide

/-- Kernel value, sub-log `{o₂}`: node 1 overridden under node 0 —
`miniInterp`'s "n₁ under n₀". -/
theorem absReplay_mini_only₂ :
    Exec.absReplay miniBase #[encOp o₂] = #[-2, 0] := by
  rw [absReplay_one]; decide

/-- Kernel value, sub-log `{o₁, o₂}`: the older `o₂` sorts first and applies;
`o₁` is then cycle-skipped — the kernel computes exactly `miniInterp`'s
"n₁ under n₀ alone". -/
theorem absReplay_mini_both :
    Exec.absReplay miniBase #[encOp o₁, encOp o₂] = #[-2, 0] := by
  rw [Exec.absReplay, absReplayFull_two]; decide

/-- **`view_not_stable`, now observable**: on the both-ops sub-log the v2
status block reports request slot 0 (`o₁`) as `1` = skipped by the cycle
rule, and slot 1 (`o₂`) as `0` = applied. The anomaly §2 proves abstractly is
exactly what the kernel's trace shows. -/
theorem absReplayFull_both_statuses :
    (Exec.absReplayFull miniBase #[encOp o₁, encOp o₂]).statuses = #[1, 0] := by
  rw [absReplayFull_two]; decide

/-- **The bridge, value side**: for every log (the four sub-logs, by case
analysis on the two memberships) and every node, reading the kernel's
effective parent of that node's index — overrides from `absReplay` over the
2-node base — through `decNode` gives exactly `miniInterp`'s answer. Same
rule, two presentations, at the level of the shipping decision layer. -/
theorem absReplay_matches_miniInterp (log : GSet MoveOp) (b : Bool) :
    decNode (Exec.effParent miniBase (Exec.absReplay miniBase (encLog log))
      (encNode b)) = miniInterp log b := by
  unfold encLog miniInterp
  by_cases h1 : log o₁ = true <;> by_cases h2 : log o₂ = true <;>
    simp only [h1, h2, if_true, if_false, Bool.false_eq_true]
  · show decNode (Exec.effParent miniBase
        (Exec.absReplay miniBase #[encOp o₁, encOp o₂]) (encNode b)) = _
    rw [absReplay_mini_both]; cases b <;> rfl
  · show decNode (Exec.effParent miniBase
        (Exec.absReplay miniBase #[encOp o₁]) (encNode b)) = _
    rw [absReplay_mini_only₁]; cases b <;> rfl
  · show decNode (Exec.effParent miniBase
        (Exec.absReplay miniBase #[encOp o₂]) (encNode b)) = _
    rw [absReplay_mini_only₂]; cases b <;> rfl
  · show decNode (Exec.effParent miniBase
        (Exec.absReplay miniBase #[]) (encNode b)) = _
    rw [absReplay_mini_neither]; cases b <;> rfl

end Uwueave.Move
