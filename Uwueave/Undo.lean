/-
# Uwueave.Undo — multi-user undo/redo as ordinary writes (Stewen–Kleppmann, PaPoC'24).

`MVRegister.lean` closed with a promise: the MV-register "is also the substrate
on which multi-user undo/redo is well-posed". This file keeps it. The core
insight of Stewen & Kleppmann, *Undo and Redo Support for Replicated Registers*
(PaPoC'24), in miniature: **an undo is an ordinary write** — it carries the
value the undone write overwrote, at a fresh clock dominating everything its
issuer has seen — and a redo is the undo of the undo, one more ordinary write.
No new operation type ever reaches the merge, so every theorem already proved
about the MV-register (`view_antichain`, `conflict_surfaces`, the derived-view
SEC of `Move.lean`) covers undo and redo *for free*. That inheritance is the
theorem set:

  * `overwrite_supersedes` / `undo_restores` / `redo_restores` — the story:
    after the overwrite only the new value is in view; after the undo only the
    restored value; after the redo only the re-restored one. Each is an exact
    view characterization (`InView s w ↔ w = …`), so "only" is proved, not
    implied.
  * `undo_preserves_history` / `redo_preserves_history` — undo restores the
    *value* and never rewrites *history*: every write stays in the grow-only
    state, and the undo is a distinct write from the write whose value it
    restores (same value, different clock).
  * `undo_conflicts_visibly` / `undo_does_not_silently_lose` — the multiplayer
    punchline: an undo racing an ordinary concurrent write is just two
    concurrent writes, so **both** surface as an MV conflict (the
    `conflict_surfaces` shape). The undo neither silently loses to nor silently
    destroys the concurrent edit.

## Honest scope — what the paper has that this miniature does not

The paper's contribution is an *algorithm*; this file formalizes the *semantic
observation the algorithm rests on*, in one concrete story. Not modeled here:

  * `RestoreOp` as a distinct operation type carrying an anchor OpId, resolved
    by traversing the operation-history DAG (their Algorithm 1). Our undo is
    handed its restored value directly (`u1 := (w0.1, …)`); the history search
    that *finds* that value is precisely what their algorithm does and we do
    not.
  * The undo/redo stacks — local-only LIFO stacks, redo-stack clearing on a
    fresh `SetOp`, arbitrary undo depth, and the local-vs-global-undo
    distinction their §2 surveys — i.e. all the machinery that decides *which*
    operation an undo targets. Our story has one undo and one redo, each handed
    its target.
  * Undo–Redo Neutrality as a general principle (n undos then n redos restore
    the starting state, their §2): we prove exactly one round trip
    (`redo_restores`), not the induction.
  * `OpIdTrace` sibling ordering (their Algorithms 2–3): our conflict set is an
    unordered antichain; theirs is deterministically sorted for display.
  * The paper has no formal development to port — its evidence is a TypeScript
    prototype plus unit tests — so nothing here "checks their proofs". This
    file machine-checks the miniature, and only the miniature.

Clock discipline: user A issues every write of the main story at clocks
`(1,0), (2,0), (3,0), (4,0)` — each dominating everything A has seen, the
Lamport rule the paper's OpIds implement. The race act forks the story after
the undo: user B, who has seen `w0` and `w1` but not `u1`, writes at `(2,1)`,
incomparable with `u1`'s `(3,0)`. So `s01ur` (redo landed) and `s01uC` (race
merged) are alternative continuations of `s01u`, not stages of one timeline.
-/
import Uwueave.MVRegister

namespace Uwueave.Undo

open Uwueave Uwueave.Catalog Uwueave.MVRegister

/-! ### The cast -/

/-- Act 1 — the initial write: value `1` at clock `(1, 0)`, user A's first op. -/
def w0 : Write := (1, (1, 0))

/-- Act 2 — the overwrite: value `2` at clock `(2, 0)`, causally after `w0`. -/
def w1 : Write := (2, (2, 0))

/-- Act 3 — the undo of `w1`: an ordinary write carrying `w0`'s value (the
value `w1` overwrote — `w0.1` *by construction*) at a fresh clock dominating
everything A has seen. This is the paper's `RestoreOp` collapsed to its effect:
nothing about it is undo-specific, and the register cannot tell it from any
other write. -/
def u1 : Write := (w0.1, (3, 0))

/-- Act 4 — the redo: the undo of the undo, an ordinary write carrying `w1`'s
value at the next fresh clock. -/
def r1 : Write := (w1.1, (4, 0))

/-- The race — user B's ordinary concurrent write: value `8` at clock `(2, 1)`.
B has seen `w0` and `w1` but not the undo, so `wC`'s clock is incomparable
with `u1`'s: neither dominates. -/
def wC : Write := (8, (2, 1))

/-! ### The states, and what they hold -/

/-- The register after acts 1–2: `w0` overwritten by `w1`. -/
def s01 : MVReg := (fun w => w == w0) ⊔ (fun w => w == w1)

/-- The register after the undo lands on top. -/
def s01u : MVReg := s01 ⊔ (fun w => w == u1)

/-- The register after the redo lands on top of the undo. -/
def s01ur : MVReg := s01u ⊔ (fun w => w == r1)

/-- The *other* continuation of `s01u`: A's undo merged with B's concurrent
write (no redo on this branch). -/
def s01uC : MVReg := s01u ⊔ (fun w => w == wC)

/-- `s01` holds exactly `w0` and `w1` — the case split every view theorem
below runs on. -/
theorem mem_s01 {w : Write} (h : s01 w = true) : w = w0 ∨ w = w1 := by
  simp [s01, gset_mem_merge, w0, w1] at h
  rcases h with h | h
  · exact Or.inl (by cases w; simp_all [w0])
  · exact Or.inr (by cases w; simp_all [w1])

/-- `s01u` holds exactly the three writes of the undo story. -/
theorem mem_s01u {w : Write} (h : s01u w = true) :
    w = w0 ∨ w = w1 ∨ w = u1 := by
  simp [s01u, s01, gset_mem_merge, w0, w1, u1] at h
  rcases h with (h | h) | h
  · exact Or.inl (by cases w; simp_all [w0])
  · exact Or.inr (Or.inl (by cases w; simp_all [w1]))
  · exact Or.inr (Or.inr (by cases w; simp_all [w0, u1]))

/-- `s01ur` holds exactly the four writes of the undo/redo story. -/
theorem mem_s01ur {w : Write} (h : s01ur w = true) :
    w = w0 ∨ w = w1 ∨ w = u1 ∨ w = r1 := by
  simp [s01ur, s01u, s01, gset_mem_merge, w0, w1, u1, r1] at h
  rcases h with ((h | h) | h) | h
  · exact Or.inl (by cases w; simp_all [w0])
  · exact Or.inr (Or.inl (by cases w; simp_all [w1]))
  · exact Or.inr (Or.inr (Or.inl (by cases w; simp_all [w0, u1])))
  · exact Or.inr (Or.inr (Or.inr (by cases w; simp_all [w1, r1])))

/-- `s01uC` holds exactly the three story writes plus B's concurrent one. -/
theorem mem_s01uC {w : Write} (h : s01uC w = true) :
    w = w0 ∨ w = w1 ∨ w = u1 ∨ w = wC := by
  simp [s01uC, s01u, s01, gset_mem_merge, w0, w1, u1, wC] at h
  rcases h with ((h | h) | h) | h
  · exact Or.inl (by cases w; simp_all [w0])
  · exact Or.inr (Or.inl (by cases w; simp_all [w1]))
  · exact Or.inr (Or.inr (Or.inl (by cases w; simp_all [w0, u1])))
  · exact Or.inr (Or.inr (Or.inr (by cases w; simp_all [wC])))

/-! ### Act 2 — the overwrite settles -/

/-- **Before the undo, only the overwrite is in view.** The view of `s01` is
exactly `{w1}` — value `2`, nothing else. (At `w := w1` the `←` direction
gives the non-vacuous half: value `2` really is visible.) -/
theorem overwrite_supersedes (w : Write) : InView s01 w ↔ w = w1 := by
  constructor
  · intro ⟨hmem, hnodom⟩
    rcases mem_s01 hmem with h | h
    · subst h; exact absurd (by decide : Dom w0.2 w1.2) (hnodom w1 (by decide))
    · exact h
  · intro h; subst h
    refine ⟨by decide, ?_⟩
    intro w' h'
    rcases mem_s01 h' with h | h <;> (subst h; decide)

/-! ### Act 3 — the undo works, without rewriting anything -/

/-- **The undo worked: only the restored value is in view.** After `u1` lands,
the view of `s01u` is exactly `{u1}` — and `u1` carries `w0.1` by
construction, so what is visible is the pre-overwrite value `1`. The undo won
by the same rule any write wins: a dominating clock, not an undo-specific
merge case. -/
theorem undo_restores (w : Write) : InView s01u w ↔ w = u1 := by
  constructor
  · intro ⟨hmem, hnodom⟩
    rcases mem_s01u hmem with h | h | h
    · subst h; exact absurd (by decide : Dom w0.2 u1.2) (hnodom u1 (by decide))
    · subst h; exact absurd (by decide : Dom w1.2 u1.2) (hnodom u1 (by decide))
    · exact h
  · intro h; subst h
    refine ⟨by decide, ?_⟩
    intro w' h'
    rcases mem_s01u h' with h | h | h <;> (subst h; decide)

/-- **Undo restores the value, never rewrites history.** All three writes —
the original, the overwrite, and the undo — remain in the grow-only state
forever, and the undo is a *distinct* write from `w0` (same value, different
clock). "Undo" removed nothing; it only added. -/
theorem undo_preserves_history :
    s01u w0 = true ∧ s01u w1 = true ∧ s01u u1 = true ∧ u1 ≠ w0 := by
  decide

/-! ### Act 4 — redo is the undo of the undo -/

/-- **After the redo, only the re-restored value is in view.** `r1` is one more
ordinary write — `w1`'s value at the next fresh clock — and the view of
`s01ur` is exactly `{r1}`: value `2` again. One full undo/redo round trip of
the visible value, with no machinery beyond the write. -/
theorem redo_restores (w : Write) : InView s01ur w ↔ w = r1 := by
  constructor
  · intro ⟨hmem, hnodom⟩
    rcases mem_s01ur hmem with h | h | h | h
    · subst h; exact absurd (by decide : Dom w0.2 r1.2) (hnodom r1 (by decide))
    · subst h; exact absurd (by decide : Dom w1.2 r1.2) (hnodom r1 (by decide))
    · subst h; exact absurd (by decide : Dom u1.2 r1.2) (hnodom r1 (by decide))
    · exact h
  · intro h; subst h
    refine ⟨by decide, ?_⟩
    intro w' h'
    rcases mem_s01ur h' with h | h | h | h <;> (subst h; decide)

/-- The redo, too, only ever adds: all four writes persist, and the redo is a
distinct write from the overwrite whose value it restores. -/
theorem redo_preserves_history :
    s01ur w0 = true ∧ s01ur w1 = true ∧ s01ur u1 = true ∧ s01ur r1 = true ∧
      r1 ≠ w1 := by
  decide

/-! ### The multiplayer theorem — an undo races an ordinary write -/

/-- **A concurrent undo and an ordinary write are just two concurrent
writes.** Merging A's undo with B's concurrent write leaves the view of
`s01uC` exactly `{u1, wC}`: an ordinary MV conflict, rendered to the
application like any other. Compare `MVRegister.conflict_surfaces` — same
phenomenon, and *that is the point*: no undo-specific merge case exists to
get this wrong. -/
theorem undo_conflicts_visibly (w : Write) :
    InView s01uC w ↔ (w = u1 ∨ w = wC) := by
  constructor
  · intro ⟨hmem, hnodom⟩
    rcases mem_s01uC hmem with h | h | h | h
    · subst h; exact absurd (by decide : Dom w0.2 u1.2) (hnodom u1 (by decide))
    · subst h; exact absurd (by decide : Dom w1.2 u1.2) (hnodom u1 (by decide))
    · exact Or.inl h
    · exact Or.inr h
  · intro h
    rcases h with h | h <;> subst h <;>
      · refine ⟨by decide, ?_⟩
        intro w' h'
        rcases mem_s01uC h' with h | h | h | h <;> (subst h; decide)

/-- The headline pair, `conflict_surfaces`-shaped: after the race merges,
**both** the undo and the concurrent write are in view. The undo does not
silently lose to the concurrent edit, and does not silently destroy it — the
fork is a visible object for the application (or the human) to resolve. -/
theorem undo_does_not_silently_lose : InView s01uC u1 ∧ InView s01uC wC :=
  ⟨(undo_conflicts_visibly u1).mpr (Or.inl rfl),
   (undo_conflicts_visibly wC).mpr (Or.inr rfl)⟩

end Uwueave.Undo
