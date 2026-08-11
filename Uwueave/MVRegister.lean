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
import Uwueave.Causality

namespace Uwueave.MVRegister

open Uwueave Uwueave.Catalog Uwueave.Causality

/-- A tagged write: value, then a two-replica vector clock (kept concrete —
`(Nat × Nat)` — so every example below is decidable; the construction is
uniform in the index type). -/
abbrev Write := Nat × (Nat × Nat)

/-- The replicated state: every write ever issued. Grow-only; the register
never merges *values*, only accumulates observations. -/
abbrev MVReg := GSet Write

example : MergeState MVReg := inferInstance

/-- `Dom c c'`: clock `c'` strictly dominates `c` (componentwise ≤, not
equal) — the write carrying `c` is causally superseded by one carrying `c'`.
An abbreviation for the shared kit's `Causality.Clock.lt` (same proposition,
now spelled once), so this file, `Undo`, and `Causality` mean the same thing
by "dominates" — and the kit's algebra (`Clock.lt_asymm`, `Clock.lt_irrefl`,
…) and decidability apply to `Dom` directly. -/
abbrev Dom (c c' : Clock) : Prop := Clock.lt c c'

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

/-! ### The general laws — every state, not just the story

The theorems above pin the behaviour on concrete writes; these are the
∀-general laws behind them, over the shared clock kit (`Causality.Clock`). -/

/-- The one-write state. The story states are merges of these:
`sAB` is definitionally `single wA ⊔ single wB`. -/
abbrev single (w : Write) : MVReg := fun w' => w' == w

/-- **Concurrent maximal writes all surface — the general law.** In ANY
state, two present writes whose clocks are concurrent, neither of which is
strictly dominated by any present write, are BOTH in view — and they are
genuinely distinct writes (`Clock.concurrent_ne`), so what surfaces is a real
two-branch conflict, not one write counted twice. `conflict_surfaces` is the
`sAB` instance (certified by the example below). Like `view_antichain` this
is close to the definition — presence and maximality *are* `InView` — and
naming it is the point: this is the register's whole contract, stated once
for every state instead of once per story. -/
theorem conflict_surfaces_general {s : MVReg} {w w' : Write}
    (hw : s w = true) (hw' : s w' = true)
    (hcc : Clock.Concurrent w.2 w'.2)
    (hmax : ∀ v, s v = true → ¬ Dom w.2 v.2)
    (hmax' : ∀ v, s v = true → ¬ Dom w'.2 v.2) :
    w ≠ w' ∧ InView s w ∧ InView s w' :=
  ⟨fun heq => Clock.concurrent_ne hcc (congrArg Prod.snd heq),
   ⟨hw, hmax⟩, ⟨hw', hmax'⟩⟩

/-- `sAB` holds exactly `wA` and `wB` — the case split for instantiating the
general laws on the story state. -/
theorem mem_sAB {w : Write} (h : sAB w = true) : w = wA ∨ w = wB := by
  simp [sAB, gset_mem_merge, wA, wB] at h
  rcases h with h | h
  · exact Or.inl (by cases w; simp_all [wA])
  · exact Or.inr (by cases w; simp_all [wB])

/-- `conflict_surfaces` really is an instance of the general law. -/
example : InView sAB wA ∧ InView sAB wB :=
  (conflict_surfaces_general (by decide) (by decide) (by decide)
    (fun v hv => by rcases mem_sAB hv with rfl | rfl <;> decide)
    (fun v hv => by rcases mem_sAB hv with rfl | rfl <;> decide)).2

/-- **Where merged visibility comes from.** A write in view after a merge was
present on (at least) one side and in view *there*: as sets,
`InView (s ⊔ t) ⊆ InView s ∪ InView t`. (Maximality against the union is in
particular maximality against each part.) -/
theorem inView_merge_from_parts {s t : MVReg} {w : Write}
    (h : InView (s ⊔ t) w) : InView s w ∨ InView t w := by
  obtain ⟨hmem, hnodom⟩ := h
  have hsub : ∀ v : Write, s v = true ∨ t v = true → (s ⊔ t) v = true := by
    intro v hv
    show (s v || t v) = true
    rcases hv with hv | hv <;> simp [hv]
  have hor : s w = true ∨ t w = true := by
    simpa [gset_mem_merge] using hmem
  rcases hor with hs | ht
  · exact Or.inl ⟨hs, fun v hv => hnodom v (hsub v (Or.inl hv))⟩
  · exact Or.inr ⟨ht, fun v hv => hnodom v (hsub v (Or.inr hv))⟩

/-- ⚠ **The converse fails: the merged view is NOT the union of the views.**
A write in view at `s` can be strictly dominated by a write `t` contributes,
so it drops *out* of view when the states merge. Witness: `wA` is in view at
`single wA`, but merging in `single wR` — whose clock `(1,1)` dominates
`wA`'s `(1,0)` — evicts it: `¬ InView (single wA ⊔ single wR) wA`.
Visibility is not preserved by merge (only presence is), and
`inView_merge_from_parts` is an inclusion, not an equality. -/
theorem inView_merge_not_union :
    ∃ (s t : MVReg) (w : Write), InView s w ∧ ¬ InView (s ⊔ t) w := by
  refine ⟨single wA, single wR, wA, ⟨by decide, ?_⟩, ?_⟩
  · intro v hv
    have hveq : v = wA := by cases v; simp_all [single, wA]
    subst hveq
    decide
  · intro ⟨hmem, hnodom⟩
    exact hnodom wR (by decide) (by decide)

end Uwueave.MVRegister
