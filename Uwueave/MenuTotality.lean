/-
# Uwueave.MenuTotality — the menu and the solver, in contact.

`Exits.lean` builds a priced exit menu and names two limits in its own module
docstring. `SeamColoring.lean` — written later, and not cited by `Exits.lean`
anywhere — happens to be the thing those limits were waiting for. This file is
what becomes provable when the two stand next to each other. It edits neither;
everything below relates them by theorem.

## The two limits, quoted, and their verdicts here

`Exits.lean:80-97` — ⟨UNDONE⟩ **"A menu is not a solver."** It even spells out
the missing signature,

    synth : (I : Invariant S) → Option (Σ Seg, {σ : S → Seg // SegmentedIConfluent σ I})

and says the interesting statement is about **non-triviality**, because two
trivial inhabitants exist (`fun _ => none`, and the identity seam
`identity_seam_segmented`). §3 supplies `synth` from
`SeamColoring.synthesizeSeam?`, and proves it is neither: on the uniqueness
ceiling it returns `some` (`synth_pin_isSome`), the projection it returns
identifies two **distinct** states (`pin_synth_is_non_trivial`), and it charges
strictly fewer crossings than the identity seam on a workload where the identity
seam charges one (`pin_synth_beats_full_coordination`). ⚠ The escrow half of
that ⟨UNDONE⟩ — synthesising a quota partition — is untouched here and survives.

`Exits.lean:101-105` — ⟨UNDONE⟩ **"The menu is not proved exhaustive."** §2 and
§3 move this **for the seam row over a covering finite pool**, and the honest
word is *moved*, not closed: availability of a seam row becomes **decidable**
(`decidableSeamApplies`, and `pin_seam_row_decided` discharges by `decide` what
`Cost.seamFalse_segmented` spends thirty-five lines on), so a row that is
available is now *found* rather than waited for; and `seam_row_dichotomy` says
the synthesiser either returns a certified row or reports a failure **located in
the stability clause** — never in the colouring clause, which
`greedySeamFor_properColoring` supplies unconditionally.

⚠ What survives: a `none` from `seamRow?` says the *greedy* colouring is not
fiber-stable, **not** that no seam exists — searching over colourings is
`SeamColoring.lean`'s ⟨UNDONE⟩ "minimum colourings", inherited here untouched.
Every other row of the eight is still un-exhausted. And on an infinite carrier
the covering pool does not exist; §4 shows that is not slack in the proof but a
real obstruction — `atMostOne_seam_row_refuted_at_every_finite_segment`.

⚠ Non-triviality is the *right* bar and `Exits.lean:93-97` sets it; what is met
here is that bar on one clash, not a general theorem that synthesis always
beats the identity.

`Exits.lean:106-110` — ⟨UNDONE⟩ **"`Exit.seam`'s `floor` field is free data."**
§1 proves that it is: `seam_applies_ignores_the_floor` is `Iff.rfl`, so no
property of the number is derivable from `Applies`, and
`applies_certifies_no_floor` exhibits an applicable row whose quoted floor `5`
exceeds the workload's true cost `0`. §5 closes it with `CertifiedSeam`, a
structure whose floor is *forced by a carried clique* — and forced under **every**
valid seam, not just the carried one (`CertifiedSeam.floor_is_forced`).

## §4 is the new mathematics: the clique bound

`SeamColoring.lean:87-89` lists as ⟨UNDONE⟩: *"a `k`-clique in the clash graph
forces `k` fibers, hence `k-1` crossings — is not here."* It is here.

  * **(a) Do ceiling clashes form a clique?** As stated, **no**, and the witness
    is `ceiling_graph_is_not_complete`: the empty set is legal, distinct from a
    singleton, and does **not** clash with it. The corrected statement is
    proved, in both directions: over `Ceiling.UniqueOn sel`, two singletons
    clash **iff** they are distinct and share a `sel`-key
    (`uniqueOn_singletons_clash_iff`). So the singleton subgraph of a ceiling is
    a disjoint union of cliques, one complete clique per key
    (`ceiling_clique_of_key`) — and `ceiling_different_keys_do_not_clash` is the
    witness that the union is genuinely disjoint. That is the characterisation
    the brief asked for, and it is strictly sharper than the conjecture.
  * **(b) The lower bound.** `clique_forces_colors`: a seam is injective on a
    clique, so any list of segment values covering the clique is at least as
    long as it. The colour count is forced by the invariant's shape.
  * **(c) A coordination floor.** Two connections, and they are different.
    `clique_path_forces_coordination` routes a clique through
    `Cost.coordination_forced` when the clique is the endpoint sequence of one
    trajectory — honest note: `Cost.ClashBlocks` only needs *consecutive* edges,
    so the clique hypothesis is stronger than that route consumes. The surplus
    is exactly what the *concurrent* bound spends:
    `clique_forces_joint_crossings` charges `k-1` crossings jointly to `k`
    streams with no ordering between them, under every valid seam. And
    `the_clique_floor_is_invisible_to_the_block_calculus` proves the two bounds
    are not the same bound: on the at-most-one ceiling every `ClashBlocks`
    decomposition is empty (the ops are inflations), so `coordination_forced`
    yields `0`, while the clique yields `k-1`.
  * **The consequence for the menu.** `atMostOne_seam_row_refuted_at_every_finite_segment`:
    "at most one element of `Nat`" admits **no seam into any finite segment
    type** — cliques of every size, so fibers of every count. The seam row is
    therefore not merely expensive there, it is absent, and
    `the_element_type_decides_the_seam_row` puts that beside `Cost.pinInv` —
    the *same* ceiling over `Bool` — where a two-fiber seam exists. The seam
    row's availability turns on the size of the element type, which is a fact
    about the clash graph and nothing else.

## Non-claims

  * ⟨UNDONE⟩ **Escrow synthesis.** `Exits.lean`'s ⟨UNDONE⟩ names two searches;
    only the seam one is answered here.
  * ⟨UNDONE⟩ **Minimum colourings.** Inherited from `SeamColoring.lean` and not
    repaired: `greedySeamFor` returns *a* proper colouring. §4 gives a lower
    bound on the number of colours; nothing here proves an upper one is
    attained, so "fewest coordination points" remains unproved.
  * ⟨scope⟩ **Totality is relative to a covering pool.** §3's dichotomy needs
    `hV : ∀ s : S, s ∈ V`. §4 shows this is not slack that a cleverer argument
    removes: on `atMostOne` no finite pool covers, and no finite seam exists.
  * ⟨scope⟩ **Classical logic.** `Classical.byContradiction` is used twice
    (`complete_clash_graph_forces_injective_seam`,
    `uniqueOn_singletons_clash_iff`), and `atMostOne_floor_is_not_vacuous`
    supplies a `DecidableEq` by `Classical.typeDecidableEq`. Same footing as
    `SeamColoring.lean`'s own uses; `clique_forces_joint_crossings`, the §4
    headline, needs neither.
-/
import Uwueave.Exits
import Uwueave.SeamColoring

namespace Uwueave.MenuTotality

open Uwueave Uwueave.Catalog Uwueave.Segmented
open Uwueave.SeamColoring (Clashes not_clashes_self ProperColoring SeamStableOnPool
  SegmentedIConfluentOn greedySeamFor greedySeamFor_properColoring synthesizeSeam? jointCost)
open Uwueave.Exits (Exit MenuEntry ExitMenu)

universe u v w

/-! ## §1. The floor is free data — proved, not asserted.

`Exits.lean:106-110` says `Exit.seam`'s `floor` is free data and calls it "a
hole in the type, not in the proofs". Both halves are theorems here: the
availability predicate is literally independent of the number, and an
applicable row can therefore quote one that is false of the workload. -/

/-- **`Applies` cannot see the floor.** The two propositions are the same
proposition — `Iff.rfl` — so *no* floor-dependent statement whatsoever follows
from a seam row's availability. This is the precise content of "free data". -/
theorem seam_applies_ignores_the_floor {S : Type} [MergeState S] (I : Invariant S)
    (Seg : Type) (σ : S → Seg) (n m : Nat) :
    (Exit.seam (S := S) Seg σ n).Applies I ↔ (Exit.seam (S := S) Seg σ m).Applies I :=
  Iff.rfl

/-- **…and the hole is inhabited by a lie.** The pin ceiling's `false`-seam is
genuinely available (`Cost.seamFalse_segmented`), and a row quoting floor `5`
for it is just as available — while the workload it would be quoted against
costs `0` crossings (`Cost.pinTrue_free_under_seamFalse`). So an applicable
menu row can print a number that is false of the workload, and §5 is why that
stops being possible for a `CertifiedSeam`. -/
theorem applies_certifies_no_floor :
    (Exit.seam (S := Cost.PinSet) Bool (fun s => s false) 5).Applies Cost.pinInv
    ∧ ¬ ((Exit.seam (S := Cost.PinSet) Bool (fun s => s false) 5).price
          ≤ Cost.crossings (fun s : Cost.PinSet => s false) Cost.pinStep
              Cost.emptyPin [true]) := by
  refine ⟨Cost.seamFalse_segmented, ?_⟩
  rw [Exits.price_seam, Cost.pinTrue_free_under_seamFalse]
  omega

/-! ## §2. The seam row becomes decidable.

`Exits.lean`'s menu takes an `Applies` term. Over a covering finite pool,
`SeamColoring.segmented_iff_properColoring`'s pool-relative half makes that term
*computable*: both clauses of `SegmentedIConfluentOn` range over a list. -/

/-- Segmented I-confluence over a pool is decidable — the instance
`SeamColoring.lean` did not need and this file does. -/
instance instDecidableSegmentedOn {S Seg : Type} [MergeState S] (V : List S)
    (σ : S → Seg) (I : Invariant S) [DecidablePred I] [DecidableEq Seg] :
    Decidable (SegmentedIConfluentOn V σ I) := by
  unfold SegmentedIConfluentOn; infer_instance

/-- **A seam row's availability is decidable over a covering pool.** The two
directions are `SeamColoring.segmented_of_segmentedOn` (which spends the
coverage hypothesis) and `SeamColoring.segmentedOn_of_segmented` (which is
free). Not an `instance`, because the coverage proof is data a caller supplies. -/
def decidableSeamApplies {S Seg : Type} [MergeState S] {I : Invariant S}
    [DecidablePred I] [DecidableEq Seg] {V : List S} (hV : ∀ s : S, s ∈ V)
    (σ : S → Seg) (n : Nat) : Decidable ((Exit.seam (S := S) Seg σ n).Applies I) :=
  decidable_of_iff (SegmentedIConfluentOn V σ I)
    ⟨fun h => SeamColoring.segmented_of_segmentedOn hV h,
     fun h => SeamColoring.segmentedOn_of_segmented h V⟩

/-- **The ceiling's seam row, discharged by computation.** `Cost.lean` proves
this by hand in thirty-five lines of case analysis on the pin lattice
(`Cost.seamFalse_segmented`); over the four-state pool it is a `decide`. Same
proposition — `Exits.ceilingMenu` lists exactly this row. -/
theorem pin_seam_row_decided :
    (Exit.seam (S := Cost.PinSet) Bool (fun s => s false) 0).Applies Cost.pinInv :=
  SeamColoring.segmented_of_segmentedOn SeamColoring.pinStates_complete (by decide)

/-! ## §3. Synthesis — the menu stops being handed its seam.

`Exits.lean:89-97` asks for `synth`. Here it is, built from
`SeamColoring.synthesizeSeam?`, together with the two theorems that say it is
not one of the two trivial inhabitants that ⟨UNDONE⟩ note rules out. -/

/-- **`synth`, at the signature `Exits.lean:91` writes out.** An `Option` of a
segment type together with a projection carrying its own `SegmentedIConfluent`
proof. Total in the sense that matters: no failure branch can return a
non-seam. -/
def synth {S : Type} [DecidableEq S] [MergeState S] (I : Invariant S)
    [DecidablePred I] (V : List S) (hV : ∀ s : S, s ∈ V) :
    Option (Σ Seg : Type, { σ : S → Seg // SegmentedIConfluent σ I }) :=
  (synthesizeSeam? I V hV).map (fun p => ⟨Nat, p⟩)

/-- The synthesised seam, wrapped as a menu row. The quoted floor is `0` — the
only number derivable without a workload, and honest precisely because `0 ≤ n`
for every `n`; §5 is where a carried workload buys a bigger one. -/
def seamEntry {S : Type} [DecidableEq S] [MergeState S] {I : Invariant S}
    [DecidablePred I] (V : List S)
    (h : SegmentedIConfluent (greedySeamFor I V) I) : MenuEntry I where
  exit := .seam Nat (greedySeamFor I V) 0
  applies := h
  consequence :=
    "coordinate only where the synthesised colouring changes: this projection \
     was computed by greedily colouring the clash graph over the pool and is \
     certified SegmentedIConfluent by \
     SeamColoring.segmented_iff_properColoring. The quoted floor 0 is the \
     vacuous one — see CertifiedSeam for a forced number"

/-- The seam row the menu **finds** rather than is handed. Mirrors
`SeamColoring.synthesizeSeam?`: the colouring is synthesised, the residual
stability clause is decided over the pool, and a `none` is an honest report. -/
def seamRow? {S : Type} [DecidableEq S] [MergeState S] (I : Invariant S)
    [DecidablePred I] (V : List S) (hV : ∀ s : S, s ∈ V) : Option (MenuEntry I) :=
  if h : SeamStableOnPool V I (greedySeamFor I V) then
    some (seamEntry V ((SeamColoring.segmented_iff_properColoring hV).mpr
      ⟨greedySeamFor_properColoring I V, SeamColoring.seamStableOn_of_pool hV h⟩))
  else
    none

/-- **The seam row's totality, and where a failure can live.** Over a covering
pool the synthesiser either returns a row — whose exit is the synthesised seam,
carrying its proof — or returns nothing, and in that case the colouring clause
still holds (`greedySeamFor_properColoring`, unconditionally) and the failure is
**exactly** a failure of fiber stability. So the ⟨UNDONE⟩ "an absent row means
nobody proved it" weakens for this row to something checkable: an absent seam
row means a decided stability failure of the *greedy* colouring over the pool.

⚠ Read the `none` branch at its own scope. It says the greedy colouring is not
fiber-stable; it does **not** say no seam exists — `greedySeamFor` is one
colouring of many (`SeamColoring.pin_synthesized_reversed_is_seamFalse` is the
other one on the four-state pool), and minimum/alternative colourings are that
file's ⟨UNDONE⟩, inherited here. Full exhaustiveness for the row would need a
search over colourings, and there is none. -/
theorem seam_row_dichotomy {S : Type} [DecidableEq S] [MergeState S]
    (I : Invariant S) [DecidablePred I] (V : List S) (hV : ∀ s : S, s ∈ V) :
    (∃ e : MenuEntry I, seamRow? I V hV = some e
        ∧ e.exit = Exit.seam Nat (greedySeamFor I V) 0)
    ∨ (seamRow? I V hV = none
        ∧ ProperColoring V (greedySeamFor I V) I
        ∧ ¬ SeamStableOnPool V I (greedySeamFor I V)) := by
  by_cases h : SeamStableOnPool V I (greedySeamFor I V)
  · have hs : seamRow? I V hV
        = some (seamEntry V ((SeamColoring.segmented_iff_properColoring hV).mpr
            ⟨greedySeamFor_properColoring I V, SeamColoring.seamStableOn_of_pool hV h⟩)) := by
      simp only [seamRow?, dif_pos h]
    exact Or.inl ⟨_, hs, rfl⟩
  · refine Or.inr ⟨?_, greedySeamFor_properColoring I V, h⟩
    simp only [seamRow?, dif_neg h]

/-- The same fact as a biconditional on the row's presence. -/
theorem seamRow_isSome_iff {S : Type} [DecidableEq S] [MergeState S]
    (I : Invariant S) [DecidablePred I] (V : List S) (hV : ∀ s : S, s ∈ V) :
    (seamRow? I V hV).isSome = true ↔ SeamStableOnPool V I (greedySeamFor I V) := by
  by_cases h : SeamStableOnPool V I (greedySeamFor I V)
  · simp [seamRow?, h]
  · simp [seamRow?, h]

/-- **`synth` is not `fun _ => none`** — on the uniqueness ceiling it returns a
seam. (`SeamColoring.pin_synthesizeSeam_isSome` is the computation; this is it
under the name `Exits.lean` asks for.) -/
theorem synth_pin_isSome :
    (synth Cost.pinInv SeamColoring.pinStates SeamColoring.pinStates_complete).isSome
      = true := by
  simp only [synth, Option.isSome_map]
  exact SeamColoring.pin_synthesizeSeam_isSome

/-- **…and it is not the identity seam either.** The synthesised projection puts
two *distinct* states in one fiber, which `fun s => s` provably cannot. This is
the non-triviality `Exits.lean:95-97` says is "exactly why the interesting
statement is about non-triviality and why nothing here proves it". -/
theorem pin_synth_is_non_trivial :
    Cost.emptyPin ≠ SeamColoring.pinF
    ∧ greedySeamFor Cost.pinInv SeamColoring.pinStates Cost.emptyPin
        = greedySeamFor Cost.pinInv SeamColoring.pinStates SeamColoring.pinF := by
  decide

/-- **The non-triviality that costs money.** On the one-op stream `[false]` the
synthesised seam charges nothing and the identity seam — which is
`Exit.fullCoordination` wearing the seam constructor
(`Exits.fullCoordination_has_a_seam`) — charges one. So the synthesised row is
strictly cheaper than the row that is always available, on a workload where
both are available. -/
theorem pin_synth_beats_full_coordination :
    Cost.crossings (greedySeamFor Cost.pinInv SeamColoring.pinStates)
        Cost.pinStep Cost.emptyPin [false] = 0
    ∧ Cost.crossings (fun s : Cost.PinSet => s) Cost.pinStep Cost.emptyPin [false]
        = 1 := by
  decide

/-! ## §4. The clique bound.

`SeamColoring.lean:87-89` lists this as ⟨UNDONE⟩. The graph vocabulary is that
file's; the bound, the ceiling characterisation and the coordination floor are
new here. -/

/-- **A clique in the clash graph**: a list of states, pairwise clashing.
`List.Pairwise` rather than a set, because everything below counts it. -/
def Clique {S : Type u} [MergeState S] (I : Invariant S) (K : List S) : Prop :=
  K.Pairwise (Clashes I)

/-- Clashing states are distinct — the merge is idempotent
(`SeamColoring.not_clashes_self`). -/
theorem clashes_ne {S : Type u} [MergeState S] {I : Invariant S} {x y : S}
    (h : Clashes I x y) : x ≠ y := by
  intro hEq
  subst hEq
  exact not_clashes_self I x h

/-- A clique has no repeats, so its length is its size. -/
theorem clique_nodup {S : Type u} [MergeState S] {I : Invariant S} {K : List S}
    (h : Clique I K) : K.Nodup :=
  h.imp (fun hab => clashes_ne hab)

/-- **A seam is injective on a clique.** Every edge is separated
(`SeamColoring.properColoring_of_segmented` is the same fact for one edge), so
the colours along a clique are pairwise distinct — `k` states, `k` fibers. -/
theorem clique_colors_nodup {S : Type u} {Seg : Type v} [MergeState S]
    {I : Invariant S} {σ : S → Seg} {K : List S}
    (hseg : SegmentedIConfluent σ I) (hK : Clique I K) : (K.map σ).Nodup := by
  show List.Pairwise (· ≠ ·) (K.map σ)
  rw [List.pairwise_map]
  exact hK.imp (fun hab hEq => hab.2.2 (hseg _ _ hEq hab.1 hab.2.1).1)

/-- Pigeonhole for lists: a repeat-free list embeds in no shorter list. Lean
core has the `erase` lemmas but not this consequence, and there is no mathlib
here. -/
theorem nodup_length_le_of_subset {α : Type u} [DecidableEq α] :
    ∀ (l C : List α), l.Nodup → (∀ a ∈ l, a ∈ C) → l.length ≤ C.length := by
  intro l
  induction l with
  | nil => intro C _ _; exact Nat.zero_le _
  | cons a l ih =>
      intro C hnd hsub
      have ha : a ∈ C := hsub a List.mem_cons_self
      have hsplit := List.nodup_cons.mp hnd
      have hsub' : ∀ b ∈ l, b ∈ C.erase a := by
        intro b hb
        have hba : b ≠ a := fun h => hsplit.1 (h ▸ hb)
        exact (List.mem_erase_of_ne hba).mpr (hsub b (List.mem_cons_of_mem a hb))
      have hle := ih (C.erase a) hsplit.2 hsub'
      have hlen : (C.erase a).length = C.length - 1 := List.length_erase_of_mem ha
      have hpos : 0 < C.length := List.length_pos_of_mem ha
      show l.length + 1 ≤ C.length
      omega

/-- **(b) THE LOWER BOUND ON COLOURS.** If a `k`-clique's colours all lie in a
list `C` of segment values, then `k ≤ C.length`. So the number of seam classes
an invariant needs is bounded below by the largest clique in its clash graph —
a number read off the **invariant's shape**, before any search. Contrast
`SeamColoring.greedySeamFor`, which finds *a* colouring and proves nothing about
how few colours suffice. -/
theorem clique_forces_colors {S : Type u} {Seg : Type v} [MergeState S]
    [DecidableEq Seg] {I : Invariant S} {σ : S → Seg} {K : List S} {C : List Seg}
    (hseg : SegmentedIConfluent σ I) (hK : Clique I K) (hC : ∀ x ∈ K, σ x ∈ C) :
    K.length ≤ C.length := by
  have hsub : ∀ c ∈ K.map σ, c ∈ C := by
    intro c hc
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hc
    exact hC x hx
  have h := nodup_length_le_of_subset (K.map σ) C (clique_colors_nodup hseg hK) hsub
  rw [List.length_map] at h
  exact h

/-- **A complete clash graph leaves only the identity seam.** If every two
distinct legal states clash, a seam is injective on legal states — its fibers
are singletons, which is `Exit.fullCoordination` and nothing else. So the seam
row degenerates exactly when the graph is complete. -/
theorem complete_clash_graph_forces_injective_seam {S : Type u} {Seg : Type v}
    [MergeState S] {I : Invariant S} {σ : S → Seg}
    (hcomp : ∀ x y : S, I x → I y → x ≠ y → Clashes I x y)
    (hseg : SegmentedIConfluent σ I) :
    ∀ x y : S, I x → I y → σ x = σ y → x = y := by
  intro x y hx hy hσ
  exact Classical.byContradiction fun hne =>
    (hcomp x y hx hy hne).2.2 (hseg x y hσ hx hy).1

/-! ### §4.1 (a) The ceiling's clash graph, characterised.

The conjecture was "ceiling clashes form a clique". The exact statement is
per-key, and both the positive half and the refutation of the global reading are
below. -/

/-- A singleton indicator contains itself. -/
theorem addDelta_self {α : Type} [DecidableEq α] (e : α) :
    Delta.addDelta e e = true := by
  simp [Delta.addDelta]

/-- Membership in the merge of two singletons. -/
theorem mem_singleton_merge {α : Type} [DecidableEq α] {e e' a : α}
    (h : (Delta.addDelta e ⊔ Delta.addDelta e') a = true) : a = e ∨ a = e' := by
  have h' : (decide (a = e) || decide (a = e')) = true := h
  rcases (Bool.or_eq_true _ _).mp h' with h'' | h''
  · exact Or.inl (of_decide_eq_true h'')
  · exact Or.inr (of_decide_eq_true h'')

/-- **(a), exactly.** Over the ceiling `Ceiling.UniqueOn sel`, two singleton
replicas clash **iff** they hold distinct elements that agree on the selector
key. So the singleton subgraph of a ceiling is a disjoint union of complete
graphs, one per key — not one clique, and not an arbitrary graph either. -/
theorem uniqueOn_singletons_clash_iff {α K : Type} [DecidableEq α] (sel : α → K)
    (e e' : α) :
    Clashes (Ceiling.UniqueOn sel) (Delta.addDelta e) (Delta.addDelta e')
      ↔ (e ≠ e' ∧ sel e = sel e') := by
  constructor
  · rintro ⟨-, -, hbad⟩
    refine ⟨?_, ?_⟩
    · intro hEq
      subst hEq
      exact hbad (by rw [merge_idem]; exact Ceiling.addDelta_uniqueOn e sel)
    · exact Classical.byContradiction fun hkey => hbad (by
        intro a b ha hb hab
        rcases mem_singleton_merge ha with rfl | rfl <;>
          rcases mem_singleton_merge hb with rfl | rfl
        · rfl
        · exact absurd hab hkey
        · exact absurd hab.symm hkey
        · rfl)
  · rintro ⟨hne, hkey⟩
    exact ⟨Ceiling.addDelta_uniqueOn e sel, Ceiling.addDelta_uniqueOn e' sel,
      fun hbad => Ceiling.merge_breaks_uniqueOn hkey hne
        (addDelta_self e) (addDelta_self e') hbad⟩

/-- **The positive half, for any invariant entailing the ceiling.** A list of
pairwise-distinct elements sharing a key gives a clique of singleton replicas.
This is `Ceiling.merge_breaks_uniqueOn` read `k` ways at once. -/
theorem ceiling_clique_of_key {α K : Type} [DecidableEq α] {sel : α → K}
    {I : Invariant (GSet α)} (himp : ∀ s, I s → Ceiling.UniqueOn sel s)
    (hleg : ∀ a : α, I (Delta.addDelta a)) (es : List α)
    (hes : es.Pairwise (fun a b => a ≠ b ∧ sel a = sel b)) :
    Clique I (es.map Delta.addDelta) := by
  rw [Clique, List.pairwise_map]
  exact hes.imp (fun {a} {b} h => ⟨hleg a, hleg b, fun hbad =>
    Ceiling.merge_breaks_uniqueOn h.2 h.1 (addDelta_self a) (addDelta_self b)
      (himp _ hbad)⟩)

/-! ### §4.2 The at-most-one ceiling over `Nat` — cliques of every size. -/

/-- `Ceiling.ceiling_atMostOne`'s invariant, verbatim: at most one element. -/
def atMostOne : Invariant (GSet Nat) :=
  fun s => ∀ m n : Nat, s m = true → s n = true → m = n

/-- Nothing held. -/
def emptySet : GSet Nat := fun _ => false

/-- A singleton is inside the ceiling. -/
theorem atMostOne_singleton_legal (n : Nat) : atMostOne (Delta.addDelta n) :=
  fun _ _ hm hk => Ceiling.addDelta_unique hm hk

/-- Distinct singletons clash — the ceiling at the constant selector. -/
theorem atMostOne_singletons_clash {m n : Nat} (h : m ≠ n) :
    Clashes atMostOne (Delta.addDelta m) (Delta.addDelta n) :=
  ⟨atMostOne_singleton_legal m, atMostOne_singleton_legal n,
   fun hbad => Ceiling.merge_breaks_uniqueOn (sel := fun _ : Nat => ()) rfl h
     (addDelta_self m) (addDelta_self n)
     (Ceiling.atMostOne_entails_uniqueOn _ hbad)⟩

/-- ⚠ **The conjecture as stated is FALSE, and here is the witness.** The empty
set is legal, is distinct from a singleton, and does **not** clash with it —
merging nothing into one element leaves one element. So the clash graph of a
uniqueness ceiling is not complete, and "ceiling clashes form a clique" is only
true of the singleton subgraph at a fixed key. -/
theorem ceiling_graph_is_not_complete :
    atMostOne emptySet
    ∧ atMostOne (Delta.addDelta 0)
    ∧ emptySet ≠ Delta.addDelta 0
    ∧ ¬ Clashes atMostOne emptySet (Delta.addDelta 0) := by
  refine ⟨fun m n hm _ => absurd hm (by simp [emptySet]), atMostOne_singleton_legal 0,
    ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp [emptySet, Delta.addDelta] at this
  · rintro ⟨-, -, hbad⟩
    refine hbad ?_
    intro m n hm hn
    have hm' : (emptySet m || Delta.addDelta 0 m) = true := hm
    have hn' : (emptySet n || Delta.addDelta 0 n) = true := hn
    simp [emptySet, Delta.addDelta] at hm' hn'
    rw [hm', hn']

/-- ⚠ **The second witness: the cliques really are disjoint.** Two singletons at
*different* keys do not clash — so a ceiling with a non-constant selector has a
clash graph that is a genuine disjoint union, not one big clique with some
edges missing. -/
theorem ceiling_different_keys_do_not_clash :
    ¬ Clashes (Ceiling.UniqueOn (Prod.fst : Nat × Nat → Nat))
        (Delta.addDelta (0, 0)) (Delta.addDelta (1, 1)) := fun h =>
  absurd ((uniqueOn_singletons_clash_iff _ _ _).mp h).2 (by decide)

/-- The first `k` singletons. -/
def singletons (k : Nat) : List (GSet Nat) := (List.range k).map Delta.addDelta

theorem singletons_length (k : Nat) : (singletons k).length = k := by
  simp [singletons]

/-- **A clique of every size.** The at-most-one ceiling over an infinite element
type has cliques of size `k` for every `k` — which by `clique_forces_colors`
means every valid seam needs at least `k` fibers, for every `k`. -/
theorem singletons_clique (k : Nat) : Clique atMostOne (singletons k) := by
  rw [Clique, singletons, List.pairwise_map]
  exact List.nodup_range.imp (fun h => atMostOne_singletons_clash h)

/-- **Every seam for the at-most-one ceiling has infinitely many fibers.** No
list of segment values covers the legal states: take a clique one longer than
the list. -/
theorem atMostOne_seam_values_are_infinite {Seg : Type v} [DecidableEq Seg]
    {σ : GSet Nat → Seg} (hseg : SegmentedIConfluent σ atMostOne) (C : List Seg)
    (hC : ∀ s : GSet Nat, atMostOne s → σ s ∈ C) : False := by
  have hval : ∀ x ∈ singletons (C.length + 1), σ x ∈ C := by
    intro x hx
    simp only [singletons, List.mem_map] at hx
    obtain ⟨n, -, rfl⟩ := hx
    exact hC _ (atMostOne_singleton_legal n)
  have h := clique_forces_colors hseg (singletons_clique (C.length + 1)) hval
  rw [singletons_length] at h
  omega

/-- **⚑ The menu consequence: the seam row is REFUTED at every finite segment
type.** "At most one element of `Nat`" admits no seam whose segment type is
finite — for any floor, in any finite `Seg`. This is a refutation in the shape
`Exits.lean` §6 uses for `balance_total_not_a_seam` and `pin_escrow_starves`,
but universally quantified over the projection rather than aimed at one
candidate: nothing anybody writes can be a finite seam here. -/
theorem atMostOne_seam_row_refuted_at_every_finite_segment {Seg : Type}
    [DecidableEq Seg] (C : List Seg) (hC : ∀ g : Seg, g ∈ C) (σ : GSet Nat → Seg)
    (n : Nat) : ¬ (Exit.seam (S := GSet Nat) Seg σ n).Applies atMostOne :=
  fun hseg => atMostOne_seam_values_are_infinite hseg C (fun s _ => hC (σ s))

/-- **⚑ The element type decides the seam row.** The *same* ceiling — at most one
element of a grow-only set — takes a two-fiber seam over `Bool`
(`Cost.pinInv`, and `Exits.ceilingMenu` prints the row) and admits no finite
seam at all over `Nat`. Nothing about the invariant's *shape* differs; what
differs is the size of the largest clique in its clash graph. That is the
discrimination `Exits.the_menus_discriminate` performs between clashes, now
performed between two instances of one clash. -/
theorem the_element_type_decides_the_seam_row :
    (Exit.seam (S := Cost.PinSet) Bool (fun s => s false) 0).Applies Cost.pinInv
    ∧ ∀ (σ : GSet Nat → Bool) (n : Nat),
        ¬ (Exit.seam (S := GSet Nat) Bool σ n).Applies atMostOne :=
  ⟨pin_seam_row_decided,
   fun σ n => atMostOne_seam_row_refuted_at_every_finite_segment [false, true]
     (fun g => by cases g <;> simp) σ n⟩

/-! ### §4.3 (c) From a clique to a coordination floor. -/

/-- Every stream crossing at least once costs at least the stream count. -/
theorem length_le_jointCost_of_all_pos {S : Type u} {Seg : Type v} {Op : Type w}
    [DecidableEq Seg] {σ : S → Seg} {step : S → Op → S} {s : S} :
    ∀ (ws : List (List Op)), (∀ w ∈ ws, 1 ≤ Cost.crossings σ step s w) →
      ws.length ≤ jointCost σ step s ws := by
  intro ws
  induction ws with
  | nil => intro _; exact Nat.le_refl 0
  | cons w ws ih =>
      intro hall
      have h1 := hall w List.mem_cons_self
      have h2 := ih (fun v hv => hall v (List.mem_cons_of_mem w hv))
      have hj : jointCost σ step s (w :: ws)
          = Cost.crossings σ step s w + jointCost σ step s ws := by
        simp [jointCost]
      show ws.length + 1 ≤ jointCost σ step s (w :: ws)
      omega

/-- **⚑ (c) THE CONCURRENT FLOOR — a `k`-clique costs `k-1` crossings.** If `k`
streams run from a common start and their endpoints are pairwise clashing, then
under **every** valid seam they pay at least `k-1` crossings between them. At
most one of them can stay in the start fiber; every other one must leave it,
because two streams sitting in one fiber would have their endpoints certified
mergeable by the seam, and the clique says they are not.

`SeamColoring.clash_edge_forces_crossing` is the case `k = 2`; this is the
`⟨UNDONE⟩` generalisation named in that file's non-claims. No ordering between
the streams appears anywhere — which is the whole difference from
`Cost.ClashBlocks`, and the reason the bound survives where the block calculus
reports nothing (see `the_clique_floor_is_invisible_to_the_block_calculus`). -/
theorem clique_forces_joint_crossings {S : Type u} {Seg : Type v} {Op : Type w}
    [MergeState S] [DecidableEq Seg] {σ : S → Seg} {I : Invariant S}
    {step : S → Op → S} {s : S} (hseg : SegmentedIConfluent σ I) :
    ∀ (ws : List (List Op)), Clique I (ws.map (Cost.run step s)) →
      ws.length ≤ jointCost σ step s ws + 1 := by
  intro ws
  induction ws with
  | nil => intro _; exact Nat.zero_le _
  | cons w ws ih =>
      intro hK
      rw [List.map_cons] at hK
      have hcons := List.pairwise_cons.mp hK
      have hj : jointCost σ step s (w :: ws)
          = Cost.crossings σ step s w + jointCost σ step s ws := by
        simp [jointCost]
      by_cases hz : Cost.crossings σ step s w = 0
      · have hall : ∀ v ∈ ws, 1 ≤ Cost.crossings σ step s v := by
          intro v hv
          rcases Nat.eq_zero_or_pos (Cost.crossings σ step s v) with h0 | hp
          · exfalso
            have e1 := Cost.sigma_const_of_crossings_eq_zero hz
            have e2 := Cost.sigma_const_of_crossings_eq_zero h0
            have hc : Clashes I (Cost.run step s w) (Cost.run step s v) :=
              hcons.1 _ (List.mem_map.mpr ⟨v, hv, rfl⟩)
            exact hc.2.2 (hseg _ _ (e1.trans e2.symm) hc.1 hc.2.1).1
          · exact hp
        have h2 := length_le_jointCost_of_all_pos ws hall
        show ws.length + 1 ≤ jointCost σ step s (w :: ws) + 1
        omega
      · have h2 := ih hcons.2
        have h1 : 1 ≤ Cost.crossings σ step s w := Nat.pos_of_ne_zero hz
        show ws.length + 1 ≤ jointCost σ step s (w :: ws) + 1
        omega

/-- The floor in subtracted form, for quoting as a price. -/
theorem clique_joint_floor {S : Type u} {Seg : Type v} {Op : Type w}
    [MergeState S] [DecidableEq Seg] {σ : S → Seg} {I : Invariant S}
    {step : S → Op → S} {s : S} (hseg : SegmentedIConfluent σ I)
    (ws : List (List Op)) (hK : Clique I (ws.map (Cost.run step s))) :
    ws.length - 1 ≤ jointCost σ step s ws := by
  have h := clique_forces_joint_crossings hseg ws hK
  omega

/-! #### The sequential route, and why it is a different bound. -/

/-- The successive endpoints of a block decomposition. -/
def endpoints {S : Type u} {Op : Type w} (step : S → Op → S) :
    S → List (List Op) → List S
  | s, [] => [s]
  | s, b :: bs => s :: endpoints step (Cost.run step s b) bs

theorem head_mem_endpoints {S : Type u} {Op : Type w} (step : S → Op → S) (s : S)
    (bs : List (List Op)) : s ∈ endpoints step s bs := by
  cases bs with
  | nil => exact List.mem_cons_self
  | cons b bs => exact List.mem_cons_self

/-- **A clique of endpoints is a clash decomposition.** So a clique that happens
to be laid out along one trajectory feeds `Cost.coordination_forced` directly.
⚠ `Cost.ClashBlocks` only asks for *consecutive* endpoints to clash, so the
clique hypothesis is strictly stronger than this route consumes — the surplus is
exactly what `clique_forces_joint_crossings` spends, where there is no
trajectory to be consecutive along. -/
theorem clashBlocks_of_clique_endpoints {S : Type u} {Op : Type w} [MergeState S]
    {I : Invariant S} {step : S → Op → S} :
    ∀ (s : S) (bs : List (List Op)), Clique I (endpoints step s bs) →
      Cost.ClashBlocks I step s bs := by
  intro s bs
  induction bs generalizing s with
  | nil => intro _; exact trivial
  | cons b bs ih =>
      intro hK
      have hcons := List.pairwise_cons.mp hK
      have hc : Clashes I s (Cost.run step s b) :=
        hcons.1 _ (head_mem_endpoints step (Cost.run step s b) bs)
      exact ⟨hc.1, hc.2.1, hc.2.2, ih _ hcons.2⟩

/-- **The clique bound, routed through `Cost.coordination_forced`.** A clique
laid along one trajectory forces `bs.length` crossings on that stream under
every seam in every universe. This is the connection asked for in (c): a
graph-theoretic hypothesis, the tree's own spec-forced floor as the conclusion. -/
theorem clique_path_forces_coordination {S : Type u} {Op : Type w} [MergeState S]
    {I : Invariant S} {step : S → Op → S} {s : S} {bs : List (List Op)}
    (hK : Clique I (endpoints step s bs)) :
    ∀ {Seg : Type v} [DecidableEq Seg] (σ : S → Seg),
      SegmentedIConfluent σ I → bs.length ≤ Cost.crossings σ step s bs.flatten :=
  Cost.coordination_forced (clashBlocks_of_clique_endpoints s bs hK)

/-! ### §4.4 `k` replicas on the at-most-one ceiling. -/

/-- Adding one element — the local step of a grow-only set. -/
def addStep (s : GSet Nat) (n : Nat) : GSet Nat := s ⊔ Delta.addDelta n

theorem run_addStep_singleton (n : Nat) :
    Cost.run addStep emptySet [n] = Delta.addDelta n := by
  show emptySet ⊔ Delta.addDelta n = Delta.addDelta n
  funext m
  show (false || Delta.addDelta n m) = Delta.addDelta n m
  exact Bool.false_or _

theorem addStep_endpoints_clash {m n : Nat} (h : m ≠ n) :
    Clashes atMostOne (Cost.run addStep emptySet [m]) (Cost.run addStep emptySet [n]) := by
  rw [run_addStep_singleton, run_addStep_singleton]
  exact atMostOne_singletons_clash h

/-- `k` replicas, each adding its own element, from a common empty start. -/
def replicaStreams (k : Nat) : List (List Nat) := (List.range k).map (fun n => [n])

theorem replicaStreams_length (k : Nat) : (replicaStreams k).length = k := by
  simp [replicaStreams]

theorem replicaStreams_clique (k : Nat) :
    Clique atMostOne ((replicaStreams k).map (Cost.run addStep emptySet)) := by
  rw [Clique, replicaStreams, List.map_map, List.pairwise_map]
  exact List.nodup_range.imp (fun h => addStep_endpoints_clash h)

/-- **⚑ A coordination floor that grows with the replica count.** `k` replicas
each adding one distinct element to a grow-only set under "at most one element"
pay at least `k-1` seam crossings between them — under every valid seam, with no
schedule, no ordering and no communication assumed. The number comes from the
clash graph's clique, i.e. from the invariant's shape. -/
theorem atMostOne_replica_floor (k : Nat) {Seg : Type v} [DecidableEq Seg]
    (σ : GSet Nat → Seg) (hseg : SegmentedIConfluent σ atMostOne) :
    k - 1 ≤ jointCost σ addStep emptySet (replicaStreams k) := by
  have h := clique_joint_floor hseg (replicaStreams k) (replicaStreams_clique k)
  rw [replicaStreams_length] at h
  exact h

/-- ⚠ **…and the quantifier is inhabited**, so the floor above is not a bound on
an empty family: the identity seam is a seam for every invariant
(`Exits.identity_seam_segmented`), and `Classical.decEq` supplies the decidable
equality `Cost.crossings` asks of a segment type. (By §4.2 no *finite* segment
type appears in this family — the inhabitant is necessarily infinite.) -/
theorem atMostOne_floor_is_not_vacuous :
    ∃ (Seg : Type) (_ : DecidableEq Seg) (σ : GSet Nat → Seg),
      SegmentedIConfluent σ atMostOne :=
  ⟨GSet Nat, Classical.typeDecidableEq _, fun s => s,
   Exits.identity_seam_segmented atMostOne⟩

theorem addStep_inflationary : Cost.Inflationary addStep := by
  intro s n
  show s ⊔ (s ⊔ Delta.addDelta n) = s ⊔ Delta.addDelta n
  rw [← merge_assoc, merge_idem]

/-- **⚑ The two floors are not the same floor.** Adding elements is an inflation,
so by `Cost.clashBlocks_nil_of_inflationary` the *only* clash decomposition of
these workloads is the empty one and `Cost.coordination_forced` yields the
constraint `0 ≤ crossings` — no constraint. The clique yields `k-1` on the same
carrier, the same step, the same start. A graph-theoretic fact therefore
produces a coordination floor that the block calculus provably cannot see, and
`Cost.lean`'s §5 calibration note ("a positive floor is evidence of a
non-inflationary op") is now visibly a statement about the *sequential* floor
only. -/
theorem the_clique_floor_is_invisible_to_the_block_calculus (k : Nat) :
    (∀ bs : List (List Nat), Cost.ClashBlocks atMostOne addStep emptySet bs →
        bs.length = 0)
    ∧ ∀ {Seg : Type} [DecidableEq Seg] (σ : GSet Nat → Seg),
        SegmentedIConfluent σ atMostOne →
        k - 1 ≤ jointCost σ addStep emptySet (replicaStreams k) := by
  refine ⟨fun bs h => ?_, fun σ hseg => atMostOne_replica_floor k σ hseg⟩
  rw [Cost.clashBlocks_nil_of_inflationary addStep_inflationary h]
  rfl

/-! ## §5. The certified seam row — the floor stops being free data.

§1 proved that `Exit.seam`'s number carries no obligation. A `CertifiedSeam`
carries the obligation as *data*: a clique of stream endpoints, from which the
floor is computed rather than quoted, and under which the floor is a genuine
lower bound for **every** valid seam. -/

/-- **A seam row that has earned its number.** The projection with its
segmentation proof, plus a concurrent workload whose endpoints pairwise clash.
The floor is not a field — it is `streams.length - 1`, computed from the
clique. -/
structure CertifiedSeam {S : Type} [MergeState S] (I : Invariant S) : Type 1 where
  /-- The segment type. -/
  Seg : Type
  /-- Decidable equality on it — what `Cost.crossings` counts with. -/
  decEq : DecidableEq Seg
  /-- The projection. -/
  σ : S → Seg
  /-- …which is a seam. -/
  segmented : SegmentedIConfluent σ I
  /-- The op alphabet of the workload the floor is quoted against. -/
  Op : Type
  /-- The local transition. -/
  step : S → Op → S
  /-- The common start. -/
  start : S
  /-- The concurrent streams. -/
  streams : List (List Op)
  /-- **The certificate**: their endpoints pairwise clash. -/
  clique : Clique I (streams.map (Cost.run step start))

/-- The floor, **computed** from the clique rather than supplied. -/
def CertifiedSeam.floor {S : Type} [MergeState S] {I : Invariant S}
    (c : CertifiedSeam I) : Nat := c.streams.length - 1

/-- The certified seam as one of `Exits.lean`'s eight exits. -/
def CertifiedSeam.toExit {S : Type} [MergeState S] {I : Invariant S}
    (c : CertifiedSeam I) : Exit S := .seam c.Seg c.σ c.floor

theorem CertifiedSeam.applies {S : Type} [MergeState S] {I : Invariant S}
    (c : CertifiedSeam I) : c.toExit.Applies I := c.segmented

theorem CertifiedSeam.price_eq_floor {S : Type} [MergeState S] {I : Invariant S}
    (c : CertifiedSeam I) : c.toExit.price = c.floor := rfl

/-- **⚑ THE FLOOR IS FORCED.** The quoted number is a lower bound on the joint
crossing count of the carried workload under **every** valid seam for `I` — not
merely under the one the row offers. This is the obligation
`Exits.seam_price_is_forced` discharges per menu for the sequential floor,
now carried by the row's own type and available in the concurrent currency. -/
theorem CertifiedSeam.floor_is_forced {S : Type} [MergeState S] {I : Invariant S}
    (c : CertifiedSeam I) {Seg' : Type v} [DecidableEq Seg'] (τ : S → Seg')
    (hτ : SegmentedIConfluent τ I) :
    c.toExit.price ≤ jointCost τ c.step c.start c.streams :=
  clique_joint_floor hτ c.streams c.clique

/-- The row, ready for an `Exits.ExitMenu`. -/
def CertifiedSeam.toEntry {S : Type} [MergeState S] {I : Invariant S}
    (c : CertifiedSeam I) : MenuEntry I where
  exit := c.toExit
  applies := c.applies
  consequence :=
    "coordinate only where this projection changes. The quoted floor is not \
     free data: it is one less than the number of pairwise-clashing stream \
     endpoints the row carries, and CertifiedSeam.floor_is_forced proves it is \
     a lower bound on the joint crossing count under every valid seam, not just \
     this one"

/-! ### §5.1 The uniqueness ceiling, certified. -/

/-- The pin ceiling's seam row with a **forced** floor: two streams, endpoints
`{true}` and `{false}`, which clash (`SeamColoring.pin_stream_endpoints_clash`).
Floor `1`. -/
def ceilingCertificate : CertifiedSeam Cost.pinInv where
  Seg := Bool
  decEq := inferInstance
  σ := fun s => s false
  segmented := Cost.seamFalse_segmented
  Op := Bool
  step := Cost.pinStep
  start := Cost.emptyPin
  streams := [[true], [false]]
  clique := by
    simp only [Clique, List.map_cons, List.map_nil]
    refine List.Pairwise.cons ?_ (List.Pairwise.cons (by simp) List.Pairwise.nil)
    intro v hv
    have hv' : v = Cost.run Cost.pinStep Cost.emptyPin [false] := by
      simpa using hv
    subst hv'
    exact SeamColoring.pin_stream_endpoints_clash

/-- **The certified ceiling row prices at `1`, and the `1` is forced.**
`Exits.ceilingMenu`'s seam row quotes `0` — correct as the *per-stream*
sequential floor (`Exits.ceiling_seam_floor_is_zero`, whose third conjunct is
`Cost.no_seam_frees_both` and already flags the undercount). The undercount is
now a number: jointly, under every valid seam, the two streams pay at least one
crossing. Same currency, `Cost.crossings`, summed over the streams a concurrent
workload actually runs. -/
theorem ceiling_certificate_floor_is_forced :
    ceilingCertificate.floor = 1
    ∧ ceilingCertificate.toExit.price = 1
    ∧ ∀ {Seg : Type} [DecidableEq Seg] (τ : Cost.PinSet → Seg),
        SegmentedIConfluent τ Cost.pinInv →
        1 ≤ jointCost τ Cost.pinStep Cost.emptyPin [[true], [false]] := by
  refine ⟨rfl, rfl, fun τ hτ => ?_⟩
  exact ceilingCertificate.floor_is_forced τ hτ

/-- **The menu, rebuilt with the certified row.** Same clash as
`Exits.ceilingMenu` — same replicas, same refutation — with the seam row
carrying a forced floor instead of a free `0`. -/
def certifiedCeilingMenu : ExitMenu Cost.pinInv where
  x := Exits.pinT
  y := Exits.pinF
  hx := Exits.pinT_legal
  hy := Exits.pinF_legal
  hbad := Exits.pin_clash
  workload := 2
  discriminating := [ceilingCertificate.toEntry]

/-- **The number moved, and the menu is still a menu.** The certified menu's
price list leads with the forced `1` where `Exits.ceilingMenu`'s leads with the
free `0`; both end with the two unconditional rows (fork `0`, full coordination
`2`). Non-emptiness and soundness are `Exits.menu_nonempty` / `Exits.menu_sound`
applied here — the certification changed the number, not the discipline. -/
theorem certified_menu_prices :
    certifiedCeilingMenu.prices = [1, 0, 2]
    ∧ Exits.ceilingMenu.prices = [0, 0, 0, 2]
    ∧ certifiedCeilingMenu.entries ≠ []
    ∧ ¬ IConfluent Cost.pinInv :=
  ⟨rfl, rfl, Exits.menu_nonempty certifiedCeilingMenu,
   (Exits.menu_sound certifiedCeilingMenu).2⟩

/-! ## §6. What became true — the contact zone, collected.

Four statements, one per limit the two files named. Nothing here is new
mathematics; it is the audit trail for the module docstring's claims. -/

/-- **The four verdicts, as one term.**

  1. `Exit.seam`'s floor is free data (§1) — and a `CertifiedSeam`'s is forced
     under every valid seam (§5).
  2. `synth` exists, returns `some` on a real clash, and what it returns is
     non-trivial: it identifies two distinct states (§3).
  3. The seam row's availability is decidable over a covering pool, and the
     ceiling's row falls to `decide` (§2).
  4. A clique in the clash graph forces a coordination floor no re-choice of
     seam escapes (§4). -/
theorem what_became_true :
    (∀ (I : Invariant Cost.PinSet) (σ : Cost.PinSet → Bool) (n m : Nat),
        (Exit.seam (S := Cost.PinSet) Bool σ n).Applies I
          ↔ (Exit.seam (S := Cost.PinSet) Bool σ m).Applies I)
    ∧ ceilingCertificate.toExit.price = 1
    ∧ (synth Cost.pinInv SeamColoring.pinStates SeamColoring.pinStates_complete).isSome
        = true
    ∧ (Cost.emptyPin ≠ SeamColoring.pinF
        ∧ greedySeamFor Cost.pinInv SeamColoring.pinStates Cost.emptyPin
            = greedySeamFor Cost.pinInv SeamColoring.pinStates SeamColoring.pinF)
    ∧ (Exit.seam (S := Cost.PinSet) Bool (fun s => s false) 0).Applies Cost.pinInv
    ∧ (∀ (σ : GSet Nat → Bool) (n : Nat),
        ¬ (Exit.seam (S := GSet Nat) Bool σ n).Applies atMostOne) :=
  ⟨fun I σ n m => seam_applies_ignores_the_floor I Bool σ n m,
   rfl, synth_pin_isSome, pin_synth_is_non_trivial,
   the_element_type_decides_the_seam_row.1, the_element_type_decides_the_seam_row.2⟩

end Uwueave.MenuTotality

