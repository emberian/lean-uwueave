/-
# Uwueave.Gluing — guarded holes, and the gluing theorem another repo named and never built.

## The archaeology, told honestly

`breadstuffs/metatheory/docs/GUARDED-HOLES-METATHEORY.md` names
**`guardGluing_iff_iconfluent`** four times — "the *one new theorem with teeth*", "genuinely new
content", the item that "touches the reflector-failure ≅ dual-H¹ novelty" — and never states it. What
that repo shipped instead is `Dregg2/Exec/GuardedHole.lean`: the study's own *weak reading*, where a
hole is a slot plus a `Pred` guard, `fillGuarded` is a guarded `put`, and the two theorems are
`holeFill_binds_in_circuit` (a successful fill commits exactly its write and discharges its guard) and
`holeFill_rejects_guard_violation` (fail-closed). Those are good theorems about **one** replica. The
gluing theorem is about **two**, and it was left on the table rather than refuted.

It was left there for a reason that reads clearly in §8 of that document: dregg's kernel had already
committed to "**determination is eager, witness is lazy**" — a contribution's shape, its δ, and its
authority are fixed when it joins the structure, and only its *value* may arrive later. Under that
commitment a hole is a dataflow slot inside a single all-or-nothing turn (`ConditionalTurn`'s
`Slots : Nat → Bool`, whose two laws are `Slots.fill_get` and `Slots.fill_mono` — filling installs,
and never unfills; there is no law relating two replicas' slot environments). There is no
*partial cone*: `Metatheory/Categorical.lean`'s `IsWideJointTurn` is a cone with a leg **for every**
index (`legs : ∀ i, J ⟶ P i`, `agree : ∀ i i'`), so a cone with a missing leg is not a term of that
type. "Two parties independently fill the same hole and we glue the results" is therefore not a
configuration that kernel can build, and the theorem about it had nothing to range over. The study's
§5d states the intended content in prose — "multiparty guard accumulation glues coordination-free iff
every accumulated guard is I-confluent" — and stops.

uwueave carries none of those commitments. Its state *is* a join-semilattice (`Confluence.MergeState`),
divergent replicas are the normal case rather than an excluded one, and the join is already the
canonical way two independently-advanced states become one. So the theorem can be stated here, in this
library's vocabulary, and it is stated below — with the quantifiers arranged so that neither direction
is vacuous, and with three witnesses beside it, one of which shows the iff is **not** a renaming of
`IConfluent`.

## What is here

* §1 **Divergence** — the corrected framing. Coordination prices *incomparable* fills, not growing
  ones: `comparable_glues` says a pair where one fill merely grew past the other glues for **any**
  guard whatsoever, and `clash_divergent` says every clash pair is therefore genuinely divergent. This
  is why `Glues` may assume divergence for free.
* §2 **The guarded hole** — `GuardedHole` = a fill space `fits` plus a guard `guard`, with
  `Admissible` fail-closed (a fill is admitted only on a *proof* that the filled state satisfies the
  guard; there is no "assume ok" branch). `Spanning` is the non-degeneracy hypothesis, and §5 proves it
  is load-bearing rather than decoration.
* §3 **The glue** — `glue_eq_merged_fill`: gluing two independently-filled replicas *is* filling the
  merged replica with the merged patch. This is the sheaf shape, and it is what makes the glue live in
  the same hole (`glue_is_admissible_fill`).
* §4 **`guardGluing_iff_iconfluent`** — the theorem, plus `clashFill_of_not_iconfluent`, which turns a
  failure into an actual four-state repro via `escalation_witness`.
* §5 **Three witnesses** — glueable, non-glueable, and (the important one) `stampedHole`: a hole whose
  guard is *provably not* I-confluent and which *provably glues*, because its fill space is not
  spanning. `Glues` and `IConfluent` come apart, and the hypothesis in the iff is exactly what closes
  the gap.
* §6 **Fill-commutation** — for glueable holes, fill-then-sync = sync-then-fill and both are
  admissible; n-ary via `Delta.joinAll`, order-blind via `Delta.joinAll_perm`.
* §7 **The verdict** — `HoleVerdict`, carried the way `Spec.Verdict` is carried: a proof, or a
  clash-fill repro. Demotion to `Spec.Verdict` needs `Spanning`, and `stampedHole` is why.
* §8 **The seam** — `GluesWithin h σ` and `guardGluingSeam_iff_segmented`: a guard segmented over `σ`
  gives a **partially glueable hole**, one that does not glue globally yet glues inside every fiber.
  The original study, whose kernel had one all-or-nothing verdict per turn, never conceived of this.
* §9 **One-shot vs gluing** — shown *orthogonal*, and sharper than orthogonal: the at-most-one-fill
  discipline is a uniqueness invariant, which is on the far side of the confluence wall
  (`Catalog.gset_atMostOne_not_iconfluent`), while a hole that glues places no bound at all on fill
  multiplicity.
* §10 **Non-claims**, labelled ⟨TERMINAL⟩ / ⟨UNDONE⟩.

Literature: Bailis et al. VLDB'15 (I-confluence); Whittaker–Hellerstein VLDB'19 (segmentation);
Almeida–Shoker–Baquero (delta mutators, the shape a fill takes here).
-/
import Uwueave.Spec
import Uwueave.Delta

namespace Uwueave.Gluing

open Uwueave Uwueave.Catalog Uwueave.Segmented Uwueave.Delta

universe u v

variable {S : Type u} [MergeState S]

/-! ## §1. Divergence — what coordination is actually pricing.

The naive reading of "two replicas disagree" is "their states differ". That reading over-charges: if
one replica's state merely *grew past* the other's, the join is already the larger one and there is
nothing to decide. What costs coordination is **incomparability** — two states neither of which
subsumes the other. These three facts make that precise and are the reason `Glues` below can assume
divergence without weakening the theorem. -/

/-- Two states are **comparable** when one already subsumes the other: a sync between them is a
one-way catch-up, not a reconciliation. -/
def Comparable (a b : S) : Prop := a ⊑ b ∨ b ⊑ a

/-- **Divergent** = not comparable. Each replica knows something the other does not, so their join is
a state *neither* of them has ever seen — which is the only situation in which a guard can be
surprised. -/
def Divergent (a b : S) : Prop := ¬ Comparable a b

theorem divergent_iff {a b : S} : Divergent a b ↔ (¬ a ⊑ b ∧ ¬ b ⊑ a) := by
  constructor
  · intro h
    exact ⟨fun h₁ => h (Or.inl h₁), fun h₂ => h (Or.inr h₂)⟩
  · intro ⟨h₁, h₂⟩ hc
    cases hc with
    | inl h => exact h₁ h
    | inr h => exact h₂ h

theorem comparable_or_divergent (a b : S) : Comparable a b ∨ Divergent a b :=
  Classical.em _

/-- **A growing fill is free.** If `a` and `b` are comparable then their join is one of them, so
*every* invariant whatsoever survives the merge — no confluence hypothesis, no guard structure, no
coordination. This is the corrected framing in one line: coordination is never the price of a replica
catching up. -/
theorem comparable_glues {I : Invariant S} {a b : S}
    (hc : Comparable a b) (ha : I a) (hb : I b) : I (a ⊔ b) := by
  cases hc with
  | inl h =>
    have h' : a ⊔ b = b := h
    rw [h']; exact hb
  | inr h =>
    have h' : b ⊔ a = a := h
    rw [merge_comm a b, h']; exact ha

/-- **Every clash is a genuine divergence.** The contrapositive of `comparable_glues`: a pair of legal
states whose merge is illegal cannot be comparable. So restricting a gluing obligation to divergent
pairs discards no counterexample — which is exactly why the iff in §4 survives the restriction. -/
theorem clash_divergent {I : Invariant S} {a b : S}
    (ha : I a) (hb : I b) (hbad : ¬ I (a ⊔ b)) : Divergent a b :=
  fun hc => hbad (comparable_glues hc ha hb)

/-! ## §2. The guarded hole.

**Why fills are delta-shaped.** A fill is modelled as a patch `d : S`, and the filled state as
`s ⊔ d`. Two reasons, both in-tree:

* It is `Delta.DeltaMutator`'s presentation — `ships : s ⊔ delta s = op s` — so a fill composed with
  the library's delta machinery needs no translation layer (§6 makes the bridge a theorem,
  `mutator_glue`).
* It costs no generality. `monotone_fill_is_delta_shaped` below: any fill operation that only *grows*
  a replica is already of the form `s ⊔ d`, with `d := f s`. Since a fill that could shrink a replica
  is not a CRDT operation at all (`Delta.le_op`, `Delta.ofInflationary`), quantifying over patches
  quantifies over every fill this setting has.

The alternative model — a hole as a *pair of states to join* — is exactly the `d := a` special case,
and it loses the distinction between *what the replica already knew* and *what the fill contributed*.
That distinction is the whole content of §5's `stampedHole`, where the fill space is restricted and
the guard's confluence stops being the whole story. -/

/-- **A guarded hole**: a position expecting a fill.

* `fits` — the fill space: which patches count as filling *this* hole. A hole is not a free slot; a
  fill of a "publish" hole publishes.
* `guard` — the invariant the *filled state* must satisfy.

Fail-closed by construction: `Admissible` below demands a proof of `guard`, and nothing in this file
ever admits a fill on the absence of a refutation. -/
structure GuardedHole (S : Type u) [MergeState S] where
  /-- Which patches fill this hole. -/
  fits : S → Prop
  /-- The guard the filled state must satisfy. -/
  guard : Invariant S

/-- **An admissible fill**: a patch that fits the hole, whose filled state satisfies the guard. Both
conjuncts are proofs — a fill is admitted on evidence or not at all. -/
def GuardedHole.Admissible (h : GuardedHole S) (s d : S) : Prop :=
  h.fits d ∧ h.guard (s ⊔ d)

/-- The fill space is **join-closed** when the merge of two fitting patches still fits — the condition
under which a glue is itself a fill of the same hole (`glue_is_admissible_fill`). -/
def JoinClosed (h : GuardedHole S) : Prop :=
  ∀ d₁ d₂ : S, h.fits d₁ → h.fits d₂ → h.fits (d₁ ⊔ d₂)

/-- **Spanning**: every state is reachable as a filled state of this hole. The non-degeneracy the iff
needs, and *not* decoration — `stampedHole` (§5) is a non-spanning hole whose guard is not I-confluent
and which glues anyway, so dropping this hypothesis makes the theorem false. -/
def Spanning (h : GuardedHole S) : Prop :=
  ∀ a : S, ∃ x d : S, h.fits d ∧ x ⊔ d = a

/-- A hole that accepts any patch is spanning: fill `a` with `a` itself. -/
theorem spanning_of_total (h : GuardedHole S) (ht : ∀ d, h.fits d) : Spanning h :=
  fun a => ⟨a, a, ht a, merge_idem a⟩

/-- The useful criterion: a hole is spanning as soon as it admits an arbitrarily *small* fill — one
the replica already subsumes. Operationally, "this hole can be filled redundantly". In a lattice with
a bottom, fitting `⊥` suffices. -/
theorem spanning_of_small_fill (h : GuardedHole S)
    (hs : ∀ a : S, ∃ d, h.fits d ∧ d ⊑ a) : Spanning h := by
  intro a
  obtain ⟨d, hf, hd⟩ := hs a
  refine ⟨a, d, hf, ?_⟩
  have hd' : d ⊔ a = a := hd
  rw [merge_comm a d]
  exact hd'

/-- Every monotone fill is already delta-shaped — the justification for the model, in one line. -/
theorem monotone_fill_is_delta_shaped (f : S → S) (hf : ∀ s, s ⊑ f s) (s : S) :
    f s = s ⊔ f s :=
  (hf s).symm

/-! ## §3. The glue. -/

/-- **The glue of two independently-filled replicas is the merged replica filled by the merged
patch.** Pure lattice, and it is the fact that makes this a *gluing* condition rather than a bare join
of two states: the glued object sits in the same hole, over the merged base, with a patch that is the
merge of the two contributions. -/
theorem glue_eq_merged_fill (x d₁ y d₂ : S) :
    (x ⊔ d₁) ⊔ (y ⊔ d₂) = (x ⊔ y) ⊔ (d₁ ⊔ d₂) := by
  calc (x ⊔ d₁) ⊔ (y ⊔ d₂) = x ⊔ (d₁ ⊔ (y ⊔ d₂)) := merge_assoc x d₁ (y ⊔ d₂)
    _ = x ⊔ ((d₁ ⊔ y) ⊔ d₂) := by rw [merge_assoc d₁ y d₂]
    _ = x ⊔ ((y ⊔ d₁) ⊔ d₂) := by rw [merge_comm d₁ y]
    _ = x ⊔ (y ⊔ (d₁ ⊔ d₂)) := by rw [merge_assoc y d₁ d₂]
    _ = (x ⊔ y) ⊔ (d₁ ⊔ d₂) := (merge_assoc x y (d₁ ⊔ d₂)).symm

/-- Re-applying the *same* fill is a no-op. Duplicate delivery of a fill is therefore not what a
one-shot discipline is for (§9); cf. `Delta.joinAll_dup`, `Delta.joinAll_redeliver`. -/
theorem refill_idempotent (s d : S) : (s ⊔ d) ⊔ d = s ⊔ d := by
  rw [merge_assoc, merge_idem]

/-! ## §4. The theorem. -/

/-- **`Glues`** — the hole glues: for every pair of *divergent* replica states filling it with
individually-admissible fills, the glue satisfies the guard.

Read the quantifiers. `x`/`y` are the two replicas' pre-fill states — arbitrary and unrelated, because
replicas partition. `d₁`/`d₂` are their fills, each required to fit *this* hole. Both filled states
must be admissible. `Divergent` restricts the obligation to the pairs that can surprise a guard;
`comparable_glues` is why that restriction is free. -/
def Glues (h : GuardedHole S) : Prop :=
  ∀ x d₁ y d₂ : S, h.Admissible x d₁ → h.Admissible y d₂ →
    Divergent (x ⊔ d₁) (y ⊔ d₂) →
    h.guard ((x ⊔ d₁) ⊔ (y ⊔ d₂))

/-- **`guardGluing_iff_iconfluent` — the theorem the guarded-holes study named and never built.**

A spanning guarded hole glues for every pair of divergent admissible fills **iff** its guard is
I-confluent.

Neither direction is a repackaging:

* **←** is the easy one and still not trivial: I-confluence discharges the obligation *without* using
  divergence, fill-fitting, or the hole's structure at all — which is precisely the observation that a
  confluent guard makes a hole's fill space irrelevant.
* **→** is where the content is. `Glues` is a *weaker* hypothesis than `IConfluent`: it speaks only
  about states of the form `x ⊔ d` with `d` fitting, and only about divergent pairs. Recovering full
  I-confluence needs both repairs — `comparable_glues` for the pairs `Glues` never mentions, and
  `Spanning` to reach the states its fill space might not.
* And `Spanning` is **not** removable: `stampedHole_glues` + `excl_not_iconfluent` (§5) is a hole whose
  guard clashes and which glues regardless. `Glues` and `IConfluent` are genuinely different
  predicates that this hypothesis, and only this hypothesis, identifies. -/
theorem guardGluing_iff_iconfluent (h : GuardedHole S) (hsp : Spanning h) :
    Glues h ↔ IConfluent h.guard := by
  constructor
  · intro hglue a b ha hb
    rcases comparable_or_divergent a b with hc | hd
    · exact comparable_glues hc ha hb
    · obtain ⟨x, d₁, hf₁, he₁⟩ := hsp a
      obtain ⟨y, d₂, hf₂, he₂⟩ := hsp b
      have hg := hglue x d₁ y d₂
        ⟨hf₁, by rw [he₁]; exact ha⟩
        ⟨hf₂, by rw [he₂]; exact hb⟩
        (by rw [he₁, he₂]; exact hd)
      rw [he₁, he₂] at hg
      exact hg
  · intro hic x d₁ y d₂ ha₁ ha₂ _
    exact hic _ _ ha₁.2 ha₂.2

/-- **Failure is a four-state repro.** When the guard is not I-confluent, `escalation_witness` hands
back a clash pair; `clash_divergent` certifies it is genuinely divergent (so it is a real instance of
the gluing obligation, not one the `Divergent` restriction excuses); `Spanning` presents each clashing
state as an actual admissible fill. The output is the scenario to replay: two replicas, two fills,
each locally legal, whose glue the guard rejects. -/
theorem clashFill_of_not_iconfluent (h : GuardedHole S) (hsp : Spanning h)
    (hnc : ¬ IConfluent h.guard) :
    ∃ x d₁ y d₂ : S, h.Admissible x d₁ ∧ h.Admissible y d₂ ∧
      Divergent (x ⊔ d₁) (y ⊔ d₂) ∧ ¬ h.guard ((x ⊔ d₁) ⊔ (y ⊔ d₂)) := by
  obtain ⟨a, b, ha, hb, hbad⟩ := escalation_witness h.guard hnc
  obtain ⟨x, d₁, hf₁, he₁⟩ := hsp a
  obtain ⟨y, d₂, hf₂, he₂⟩ := hsp b
  refine ⟨x, d₁, y, d₂, ⟨hf₁, ?_⟩, ⟨hf₂, ?_⟩, ?_, ?_⟩
  · rw [he₁]; exact ha
  · rw [he₂]; exact hb
  · rw [he₁, he₂]; exact clash_divergent ha hb hbad
  · rw [he₁, he₂]; exact hbad

/-- **The glue is a fill of the same hole.** With a join-closed fill space, the glue of two admissible
fills is itself an admissible fill — of the merged replica, by the merged patch. This is the sheaf
reading: the local sections restrict-and-agree into a global one that lives in the same position. -/
theorem glue_is_admissible_fill (h : GuardedHole S) (hjc : JoinClosed h) (hg : Glues h)
    {x d₁ y d₂ : S} (ha₁ : h.Admissible x d₁) (ha₂ : h.Admissible y d₂)
    (hdiv : Divergent (x ⊔ d₁) (y ⊔ d₂)) :
    h.Admissible (x ⊔ y) (d₁ ⊔ d₂) := by
  refine ⟨hjc _ _ ha₁.1 ha₂.1, ?_⟩
  rw [← glue_eq_merged_fill]
  exact hg x d₁ y d₂ ha₁ ha₂ hdiv

/-! ## §5. Three witnesses — satisfiable, refutable, and the one that shows the iff has content.

A gluing theorem with no glueable hole is vacuous on one side; with no non-glueable hole it is vacuous
on the other. Both are exhibited. The third witness is the important one: it separates `Glues` from
`IConfluent`, so the iff is a theorem about two notions rather than a renaming of one. -/

/-- A grow-only set given by a member list — concrete replica states for the witnesses. -/
def gsetOf (l : List Nat) : GSet Nat := fun n => l.contains n

/-! ### (i) A glueable hole. -/

/-- **The anchor hole.** Every fill fits; the guard is "tag `0` is present", the tier-1 monotone
invariant. -/
def anchorHole : GuardedHole (GSet Nat) where
  fits := fun _ => True
  guard := fun s => s 0 = true

theorem anchorHole_spanning : Spanning anchorHole :=
  spanning_of_total _ (fun _ => trivial)

/-- **Satisfiable**: the anchor hole glues, via the theorem, from `Catalog.gset_mem_iconfluent`. -/
theorem anchorHole_glues : Glues anchorHole :=
  (guardGluing_iff_iconfluent anchorHole anchorHole_spanning).mpr (gset_mem_iconfluent 0)

/-! ### (ii) A non-glueable hole. -/

/-- The exclusion guard: tags `0` and `1` are never both present. A capacity/uniqueness-shaped guard —
the non-monotone fragment the study's §5d says forces serialisation. -/
def Excl : Invariant (GSet Nat) := fun s => s 0 = false ∨ s 1 = false

theorem excl_not_iconfluent : ¬ IConfluent Excl := by
  intro h
  have hm := h (gsetOf [0]) (gsetOf [1]) (Or.inr rfl) (Or.inl rfl)
  cases hm with
  | inl hbad => exact absurd hbad (by decide)
  | inr hbad => exact absurd hbad (by decide)

/-- **The exclusive hole.** Every fill fits; the guard is `Excl`. -/
def exclusiveHole : GuardedHole (GSet Nat) where
  fits := fun _ => True
  guard := Excl

theorem exclusiveHole_spanning : Spanning exclusiveHole :=
  spanning_of_total _ (fun _ => trivial)

/-- **Refutable**: the exclusive hole does not glue. -/
theorem exclusiveHole_not_glues : ¬ Glues exclusiveHole := fun hg =>
  excl_not_iconfluent ((guardGluing_iff_iconfluent exclusiveHole exclusiveHole_spanning).mp hg)

/-- …and the concrete clash-fill, spelled out rather than extracted: replica `{0}` and replica `{1}`
each fill the hole with the same innocuous patch `{2}`; both filled states are legal; they are
genuinely divergent; the glue holds `0` and `1` together and the guard rejects it. This is the repro a
test replays. -/
theorem exclusiveHole_clashFill :
    exclusiveHole.Admissible (gsetOf [0]) (gsetOf [2])
    ∧ exclusiveHole.Admissible (gsetOf [1]) (gsetOf [2])
    ∧ Divergent (gsetOf [0] ⊔ gsetOf [2]) (gsetOf [1] ⊔ gsetOf [2])
    ∧ ¬ exclusiveHole.guard ((gsetOf [0] ⊔ gsetOf [2]) ⊔ (gsetOf [1] ⊔ gsetOf [2])) := by
  refine ⟨⟨trivial, Or.inr rfl⟩, ⟨trivial, Or.inl rfl⟩, ?_, ?_⟩
  · intro hc
    cases hc with
    | inl h =>
      have h' : (gsetOf [0] ⊔ gsetOf [2]) ⊔ (gsetOf [1] ⊔ gsetOf [2])
          = gsetOf [1] ⊔ gsetOf [2] := h
      exact absurd (congrFun h' 0) (by decide)
    | inr h =>
      have h' : (gsetOf [1] ⊔ gsetOf [2]) ⊔ (gsetOf [0] ⊔ gsetOf [2])
          = gsetOf [0] ⊔ gsetOf [2] := h
      exact absurd (congrFun h' 1) (by decide)
  · intro hbad
    cases hbad with
    | inl hz => exact absurd hz (by decide)
    | inr hz => exact absurd hz (by decide)

/-! ### (iii) The separating witness — `Glues` is not `IConfluent` renamed.

`stampedHole` carries the *same* clashing guard as `exclusiveHole`. The only difference is its fill
space: every fill of this hole stamps tag `1`. That restriction changes the verdict, because a fill
that stamps `1` can only be admissible if `0` is absent — and absence of `0` is monotone, so the glue
is safe. The guard clashes; the hole glues.

This is the whole reason the iff is a theorem about two things: `Glues` quantifies over the states a
*hole* can produce, `IConfluent` over all states, and only `Spanning` makes those coincide. -/

/-- **The stamped hole.** Fills must stamp tag `1`; the guard is the clashing `Excl`. -/
def stampedHole : GuardedHole (GSet Nat) where
  fits := fun d => d 1 = true
  guard := Excl

/-- The stamped hole is **not** spanning: no filled state can omit tag `1`, so the empty state is
unreachable. -/
theorem stampedHole_not_spanning : ¬ Spanning stampedHole := by
  intro hsp
  obtain ⟨x, d, hf, he⟩ := hsp (fun _ => false)
  have h1 := congrFun he 1
  rw [gset_mem_merge] at h1
  have hf' : d 1 = true := hf
  rw [hf'] at h1
  simp at h1

/-- **And it glues anyway.** Every admissible fill of this hole forces `0` absent — the guard's other
disjunct is closed off by the stamp — and "`0` absent" is preserved by union. So the hole glues while
its guard is refuted (`excl_not_iconfluent`). `Spanning` in `guardGluing_iff_iconfluent` is
load-bearing, and this theorem is the proof. -/
theorem stampedHole_glues : Glues stampedHole := by
  intro x d₁ y d₂ ha₁ ha₂ _
  have hf₁ : d₁ 1 = true := ha₁.1
  have hf₂ : d₂ 1 = true := ha₂.1
  have e₁ : (x ⊔ d₁) 1 = true := by rw [gset_mem_merge, hf₁]; simp
  have e₂ : (y ⊔ d₂) 1 = true := by rw [gset_mem_merge, hf₂]; simp
  have hg₁ : Excl (x ⊔ d₁) := ha₁.2
  have hg₂ : Excl (y ⊔ d₂) := ha₂.2
  have z₁ : (x ⊔ d₁) 0 = false := by
    cases hg₁ with
    | inl hz => exact hz
    | inr hz => rw [e₁] at hz; exact absurd hz (by decide)
  have z₂ : (y ⊔ d₂) 0 = false := by
    cases hg₂ with
    | inl hz => exact hz
    | inr hz => rw [e₂] at hz; exact absurd hz (by decide)
  have hglue : Excl ((x ⊔ d₁) ⊔ (y ⊔ d₂)) :=
    Or.inl (by rw [gset_mem_merge, z₁, z₂]; rfl)
  exact hglue

/-- `stampedHole_glues` is **not vacuous**: the hole really does have divergent admissible fill pairs.
Two replicas already stamped, one holding tag `2` and the other tag `3`, each re-stamping: both filled
states are legal, and neither subsumes the other. -/
theorem stampedHole_nonvacuous :
    stampedHole.Admissible (gsetOf [1, 2]) (gsetOf [1])
    ∧ stampedHole.Admissible (gsetOf [1, 3]) (gsetOf [1])
    ∧ Divergent (gsetOf [1, 2] ⊔ gsetOf [1]) (gsetOf [1, 3] ⊔ gsetOf [1]) := by
  refine ⟨⟨rfl, Or.inl rfl⟩, ⟨rfl, Or.inl rfl⟩, ?_⟩
  intro hc
  cases hc with
  | inl h =>
    have h' : (gsetOf [1, 2] ⊔ gsetOf [1]) ⊔ (gsetOf [1, 3] ⊔ gsetOf [1])
        = gsetOf [1, 3] ⊔ gsetOf [1] := h
    exact absurd (congrFun h' 2) (by decide)
  | inr h =>
    have h' : (gsetOf [1, 3] ⊔ gsetOf [1]) ⊔ (gsetOf [1, 2] ⊔ gsetOf [1])
        = gsetOf [1, 2] ⊔ gsetOf [1] := h
    exact absurd (congrFun h' 3) (by decide)

/-- The separation, as one statement: **one guard, two holes, opposite verdicts.** `Glues` is not
`IConfluent` under another name. -/
theorem glues_is_not_iconfluent_renamed :
    ¬ IConfluent Excl ∧ Glues stampedHole ∧ ¬ Glues exclusiveHole ∧ ¬ Spanning stampedHole :=
  ⟨excl_not_iconfluent, stampedHole_glues, exclusiveHole_not_glues, stampedHole_not_spanning⟩

/-! ## §6. Consequence (a) — fill order across replicas is unobservable. -/

/-- **Fill-commutation.** For a glueable, join-closed, spanning hole: filling on each replica and then
syncing lands on the same state as syncing and then filling with the merged patch — *and* that state
is an admissible fill of the hole. Neither replica can observe which order happened, and the guard
cannot either. -/
theorem fill_commutes (h : GuardedHole S) (hjc : JoinClosed h) (hsp : Spanning h) (hg : Glues h)
    {x d₁ y d₂ : S} (ha₁ : h.Admissible x d₁) (ha₂ : h.Admissible y d₂) :
    (x ⊔ d₁) ⊔ (y ⊔ d₂) = (x ⊔ y) ⊔ (d₁ ⊔ d₂)
    ∧ h.Admissible (x ⊔ y) (d₁ ⊔ d₂) := by
  have hic := (guardGluing_iff_iconfluent h hsp).mp hg
  refine ⟨glue_eq_merged_fill x d₁ y d₂, hjc _ _ ha₁.1 ha₂.1, ?_⟩
  rw [← glue_eq_merged_fill]
  exact hic _ _ ha₁.2 ha₂.2

/-- An I-confluent invariant survives a whole delivery history, not just one merge — the induction
`Delta.joinAll` was built for. -/
theorem iconfluent_joinAll {I : Invariant S} (hI : IConfluent I) :
    ∀ (l : List S) (base : S), I base → (∀ d ∈ l, I d) → I (joinAll base l)
  | [], _, hb, _ => hb
  | d :: l, base, hb, hd =>
    iconfluent_joinAll hI l (base ⊔ d) (hI base d hb (hd d (List.Mem.head l)))
      (fun e he => hd e (List.Mem.tail d he))

/-- **The n-ary glue, and its order-blindness.** `n` replicas each fill the same glueable hole; the
glue of all of them is admissible, and — by `Delta.joinAll_perm` — the state does not depend on the
order the contributions arrive in. Not merely that the two arrangements agree as states, but that the
guard's verdict is the same at both. -/
theorem glue_all_unobservable (h : GuardedHole S) (hsp : Spanning h) (hg : Glues h)
    (a : S) {l l' : List S} (hperm : l.Perm l')
    (ha : h.guard a) (hl : ∀ b ∈ l, h.guard b) :
    joinAll a l = joinAll a l' ∧ h.guard (joinAll a l) ∧ h.guard (joinAll a l') := by
  have hic := (guardGluing_iff_iconfluent h hsp).mp hg
  have heq : joinAll a l = joinAll a l' := joinAll_perm hperm a
  refine ⟨heq, iconfluent_joinAll hic l a ha hl, ?_⟩
  rw [← heq]
  exact iconfluent_joinAll hic l a ha hl

/-- …and multiplicity-blindness, the other half: a re-delivered fill changes neither the state
(`Delta.joinAll_redeliver`) nor the verdict. At-least-once delivery of fills is exactly as good as
exactly-once, guard included. -/
theorem glue_all_redeliver (h : GuardedHole S) (hsp : Spanning h) (hg : Glues h)
    (a : S) {d : S} {l : List S} (hd : d ∈ l)
    (ha : h.guard a) (hl : ∀ b ∈ l, h.guard b) :
    joinAll a (d :: l) = joinAll a l ∧ h.guard (joinAll a (d :: l)) := by
  have heq := joinAll_redeliver hd a
  refine ⟨heq, ?_⟩
  rw [heq]
  exact iconfluent_joinAll ((guardGluing_iff_iconfluent h hsp).mp hg) l a ha hl

/-- A `Delta.DeltaMutator` whose patches fit the hole is a **fill operation** for it. -/
def MutatorFits (h : GuardedHole S) (m : DeltaMutator S) : Prop := ∀ s, h.fits (m.delta s)

/-- **The delta-mutator bridge.** Two replicas each run a fill *operation* — a `DeltaMutator`, the
library's own presentation of a CRDT update — and the gluing theorem applies to the resulting states
directly, through `ships`. The delta-shaped model of a fill is not a private convention of this file;
it is the one `Delta.lean` already uses. -/
theorem mutator_glue (h : GuardedHole S) (hg : Glues h)
    {m₁ m₂ : DeltaMutator S} (hf₁ : MutatorFits h m₁) (hf₂ : MutatorFits h m₂)
    {x y : S} (hg₁ : h.guard (m₁.op x)) (hg₂ : h.guard (m₂.op y))
    (hdiv : Divergent (m₁.op x) (m₂.op y)) :
    h.guard (m₁.op x ⊔ m₂.op y) := by
  have e₁ : x ⊔ m₁.delta x = m₁.op x := m₁.ships x
  have e₂ : y ⊔ m₂.delta y = m₂.op y := m₂.ships y
  rw [← e₁, ← e₂]
  exact hg x (m₁.delta x) y (m₂.delta y)
    ⟨hf₁ x, by rw [e₁]; exact hg₁⟩
    ⟨hf₂ y, by rw [e₂]; exact hg₂⟩
    (by rw [e₁, e₂]; exact hdiv)

/-! ## §7. Consequence (b) — the verdict, carried the way `Spec.Verdict` is carried. -/

/-- **The guarded-hole verdict.** Either a proof that the hole glues, or a *clash-fill repro*: two
replicas, two fitting fills, both locally admissible, genuinely divergent, whose glue the guard
rejects. There is no third constructor and no un-evidenced answer — the same discipline as
`Spec.Verdict`, one level up (the evidence names the fills, not just the states). -/
inductive HoleVerdict (h : GuardedHole S) : Type u where
  /-- The hole glues, with the proof. -/
  | glues (hg : Glues h)
  /-- The hole does not glue, with the four-state repro. -/
  | clashFill (x d₁ y d₂ : S)
      (ha₁ : h.Admissible x d₁) (ha₂ : h.Admissible y d₂)
      (hdiv : Divergent (x ⊔ d₁) (y ⊔ d₂))
      (hbad : ¬ h.guard ((x ⊔ d₁) ⊔ (y ⊔ d₂))) : HoleVerdict h

namespace HoleVerdict

/-- **Demotion to the invariant verdict** — and it needs `Spanning`. A clash-fill is a `Verdict.clash`
on the filled states outright; a `glues` becomes `Verdict.free` only through the theorem, which is
where the hypothesis is spent. `stampedHole` is a `glues` verdict that **cannot** be demoted, and that
is correct: its guard is not free, its hole merely never exposes the clash. -/
def toVerdict {h : GuardedHole S} (hsp : Spanning h) : HoleVerdict h → Spec.Verdict h.guard
  | .glues hg => .free ((guardGluing_iff_iconfluent h hsp).mp hg)
  | .clashFill x d₁ y d₂ ha₁ ha₂ _ hbad => .clash (x ⊔ d₁) (y ⊔ d₂) ha₁.2 ha₂.2 hbad

/-- Erase the evidence, keep the answer — for reporting (cf. `Spec.Verdict.isFree`). -/
def isGlued {h : GuardedHole S} : HoleVerdict h → Bool
  | .glues _ => true
  | .clashFill .. => false

end HoleVerdict

/-- **Every spanning guarded hole has a verdict.** There is no third answer and no "unknown": either
the gluing proof exists, or `clashFill_of_not_iconfluent` produces the repro. -/
theorem holeVerdict_total (h : GuardedHole S) (hsp : Spanning h) : Nonempty (HoleVerdict h) := by
  rcases Classical.em (IConfluent h.guard) with hic | hnc
  · exact ⟨.glues ((guardGluing_iff_iconfluent h hsp).mpr hic)⟩
  · obtain ⟨x, d₁, y, d₂, ha₁, ha₂, hdiv, hbad⟩ := clashFill_of_not_iconfluent h hsp hnc
    exact ⟨.clashFill x d₁ y d₂ ha₁ ha₂ hdiv hbad⟩

/-- The anchor hole's verdict, as a value. -/
def anchorVerdict : HoleVerdict anchorHole := .glues anchorHole_glues

/-- The exclusive hole's verdict, as a value — carrying the §5 repro. -/
def exclusiveVerdict : HoleVerdict exclusiveHole :=
  .clashFill (gsetOf [0]) (gsetOf [2]) (gsetOf [1]) (gsetOf [2])
    exclusiveHole_clashFill.1 exclusiveHole_clashFill.2.1
    exclusiveHole_clashFill.2.2.1 exclusiveHole_clashFill.2.2.2

/-- The stamped hole's verdict: **glued**, though its guard is refuted. The verdict is about the hole,
not the guard — which is the point of having a hole-level verdict at all, and it is exactly the
verdict `Spec.Verdict` cannot express. -/
def stampedVerdict : HoleVerdict stampedHole := .glues stampedHole_glues

/-! ## §8. Consequence (c) — the seam: partially glueable holes.

The study's kernel had one all-or-nothing verdict per turn, so "this hole glues, but only within a
fiber" was not a sentence it could say. Here it is a theorem shape. -/

/-- **`GluesWithin h σ`** — the hole glues *inside a fiber* of `σ`: same-seam divergent admissible
fills glue admissibly **and the glue stays in the seam**. The second conjunct is load-bearing for the
same reason it is in `Segmented.SegmentedIConfluent` — without it a single sync could teleport
replicas across a boundary and the free-running guarantee inside the fiber would evaporate. -/
def GluesWithin {Seg : Type v} (h : GuardedHole S) (σ : S → Seg) : Prop :=
  ∀ x d₁ y d₂ : S, h.Admissible x d₁ → h.Admissible y d₂ →
    σ (x ⊔ d₁) = σ (y ⊔ d₂) →
    Divergent (x ⊔ d₁) (y ⊔ d₂) →
    h.guard ((x ⊔ d₁) ⊔ (y ⊔ d₂)) ∧ σ ((x ⊔ d₁) ⊔ (y ⊔ d₂)) = σ (x ⊔ d₁)

/-- Inside a fiber, a growing fill is still free — and it cannot leave the fiber either. The seam
version of `comparable_glues`, and the reason the seam iff survives the same restriction. -/
theorem comparable_glues_seam {Seg : Type v} {I : Invariant S} {σ : S → Seg} {a b : S}
    (hc : Comparable a b) (hσ : σ a = σ b) (ha : I a) (hb : I b) :
    I (a ⊔ b) ∧ σ (a ⊔ b) = σ a := by
  cases hc with
  | inl h =>
    have h' : a ⊔ b = b := h
    rw [h']
    exact ⟨hb, hσ.symm⟩
  | inr h =>
    have h' : b ⊔ a = a := h
    rw [merge_comm a b, h']
    exact ⟨ha, rfl⟩

/-- **The seam version of the theorem.** A spanning guarded hole glues within the fibers of `σ` iff
its guard is segmented-I-confluent over `σ` (Whittaker–Hellerstein's refinement, `Segmented.lean`).
Same proof shape as `guardGluing_iff_iconfluent`, with `comparable_glues_seam` covering the pairs the
divergence restriction never mentions.

The object this makes expressible is a **partially glueable hole**: one whose global verdict is a
clash and whose fibered verdict is free, so fills run coordination-free until the seam moves. -/
theorem guardGluingSeam_iff_segmented {Seg : Type v} (h : GuardedHole S) (σ : S → Seg)
    (hsp : Spanning h) :
    GluesWithin h σ ↔ SegmentedIConfluent σ h.guard := by
  constructor
  · intro hglue a b hσ ha hb
    rcases comparable_or_divergent a b with hc | hd
    · exact comparable_glues_seam hc hσ ha hb
    · obtain ⟨x, d₁, hf₁, he₁⟩ := hsp a
      obtain ⟨y, d₂, hf₂, he₂⟩ := hsp b
      have hres := hglue x d₁ y d₂
        ⟨hf₁, by rw [he₁]; exact ha⟩
        ⟨hf₂, by rw [he₂]; exact hb⟩
        (by rw [he₁, he₂]; exact hσ)
        (by rw [he₁, he₂]; exact hd)
      rw [he₁, he₂] at hres
      exact hres
  · intro hseg x d₁ y d₂ ha₁ ha₂ hσ _
    exact hseg _ _ hσ ha₁.2 ha₂.2

/-- **The partially glueable hole**, concrete: a budgeted quota (`Segmented.BudgetInv`) as the guard
of a total hole. -/
def budgetHole : GuardedHole QuotaState where
  fits := fun _ => True
  guard := BudgetInv 10

theorem budgetHole_spanning : Spanning budgetHole :=
  spanning_of_total _ (fun _ => trivial)

/-- **Both verdicts, one hole.** It does not glue — two legal allocations glue into an over-budget
one — yet it glues within every fiber of the allocation. Spends never coordinate; re-allocation is the
only coordination point. This is the sentence the original study's all-or-nothing kernel could not
form. -/
theorem budgetHole_partially_glues :
    ¬ Glues budgetHole ∧ GluesWithin budgetHole (Prod.fst : QuotaState → (Bool → Nat)) :=
  ⟨fun hg => budget_not_iconfluent
      ((guardGluing_iff_iconfluent budgetHole budgetHole_spanning).mp hg),
   (guardGluingSeam_iff_segmented budgetHole Prod.fst budgetHole_spanning).mpr
      (budget_segmented 10)⟩

/-- Two same-allocation replicas whose spends diverge: quota 5/5, one having spent 3/1 and the other
1/3. -/
def quotaX : QuotaState := ((fun _ => 5), (fun b => if b then 3 else 1))

/-- The other replica of the same fiber. -/
def quotaY : QuotaState := ((fun _ => 5), (fun b => if b then 1 else 3))

/-- **The seam half is not vacuous**: the budget hole really does have divergent, same-allocation,
individually-admissible fill pairs — so `GluesWithin budgetHole Prod.fst` is a statement about
scenarios that occur, not an empty quantification. (These are the spends that run free; only a
re-allocation leaves the fiber.) -/
theorem budgetHole_seam_nonvacuous :
    budgetHole.Admissible quotaX quotaX
    ∧ budgetHole.Admissible quotaY quotaY
    ∧ (quotaX ⊔ quotaX).1 = (quotaY ⊔ quotaY).1
    ∧ Divergent (quotaX ⊔ quotaX) (quotaY ⊔ quotaY) := by
  refine ⟨⟨trivial, by refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide⟩,
          ⟨trivial, by refine ⟨⟨?_, ?_⟩, ?_⟩ <;> decide⟩, rfl, ?_⟩
  intro hc
  cases hc with
  | inl h =>
    have h' : (quotaX ⊔ quotaX) ⊔ (quotaY ⊔ quotaY) = quotaY ⊔ quotaY := h
    exact absurd (congrFun (congrArg Prod.snd h') true) (by decide)
  | inr h =>
    have h' : (quotaY ⊔ quotaY) ⊔ (quotaX ⊔ quotaX) = quotaX ⊔ quotaX := h
    exact absurd (congrFun (congrArg Prod.snd h') false) (by decide)

/-! ## §9. Consequence (d) — one-shot and gluing are orthogonal, and sharply so.

The breadstuffs weak reading's law is one-shot: a hole is filled *once*, at *one* replica
(`Await.OneShot`, `commit_resumes_once`; `Slots.fill` installs, `Slots.fill_mono` never unfills). That
is a discipline about **multiplicity at one site**. Gluing is a condition about **fills at different
sites**. The two do not imply each other, and the reason is structural rather than accidental. -/

/-- The at-most-one-fill discipline, read as a guard on the set of installed fills. -/
def AtMostOneFill : Invariant (GSet Nat) := fun s => ∀ m n, s m = true → s n = true → m = n

/-- A hole guarded by the one-shot discipline itself. -/
def oneShotHole : GuardedHole (GSet Nat) where
  fits := fun _ => True
  guard := AtMostOneFill

theorem oneShotHole_spanning : Spanning oneShotHole :=
  spanning_of_total _ (fun _ => trivial)

/-- **One-shot never glues.** "At most one fill is installed" is a uniqueness invariant, and every
uniqueness invariant is on the far side of the confluence wall
(`Catalog.gset_atMostOne_not_iconfluent`): two replicas each installing their own single fill merge to
two. So the one-shot discipline is not something gluing can deliver — it is precisely the coordination
a glueable hole avoids needing. -/
theorem oneShotHole_never_glues : ¬ Glues oneShotHole := fun hg =>
  gset_atMostOne_not_iconfluent
    ((guardGluing_iff_iconfluent oneShotHole oneShotHole_spanning).mp hg)

/-- **A local double fill is an instance of a glue** (take `x = y`): two distinct fills at *one*
replica land at `s ⊔ (d₁ ⊔ d₂)`, and for a glueable hole the guard admits it. So gluing offers no
protection whatsoever against double filling at a site — it *licenses* it. -/
theorem local_double_fill (h : GuardedHole S) (hg : Glues h) {s d₁ d₂ : S}
    (ha₁ : h.Admissible s d₁) (ha₂ : h.Admissible s d₂)
    (hdiv : Divergent (s ⊔ d₁) (s ⊔ d₂)) :
    h.guard (s ⊔ (d₁ ⊔ d₂)) := by
  have hres := hg s d₁ s d₂ ha₁ ha₂ hdiv
  rwa [glue_eq_merged_fill, merge_idem] at hres

/-- The glueable hole concretely admits two *distinct* fills at one replica, and their double-filled
state is admissible — routed through `local_double_fill`, so the mechanism is the general one and not
a coincidence of the example. -/
theorem anchorHole_admits_double_fill :
    anchorHole.Admissible (gsetOf [0]) (gsetOf [2])
    ∧ anchorHole.Admissible (gsetOf [0]) (gsetOf [3])
    ∧ Divergent (gsetOf [0] ⊔ gsetOf [2]) (gsetOf [0] ⊔ gsetOf [3])
    ∧ anchorHole.guard (gsetOf [0] ⊔ (gsetOf [2] ⊔ gsetOf [3])) := by
  have ha₁ : anchorHole.Admissible (gsetOf [0]) (gsetOf [2]) := ⟨trivial, rfl⟩
  have ha₂ : anchorHole.Admissible (gsetOf [0]) (gsetOf [3]) := ⟨trivial, rfl⟩
  have hdiv : Divergent (gsetOf [0] ⊔ gsetOf [2]) (gsetOf [0] ⊔ gsetOf [3]) := by
    intro hc
    cases hc with
    | inl h =>
      have h' : (gsetOf [0] ⊔ gsetOf [2]) ⊔ (gsetOf [0] ⊔ gsetOf [3])
          = gsetOf [0] ⊔ gsetOf [3] := h
      exact absurd (congrFun h' 2) (by decide)
    | inr h =>
      have h' : (gsetOf [0] ⊔ gsetOf [3]) ⊔ (gsetOf [0] ⊔ gsetOf [2])
          = gsetOf [0] ⊔ gsetOf [2] := h
      exact absurd (congrFun h' 3) (by decide)
  exact ⟨ha₁, ha₂, hdiv, local_double_fill anchorHole anchorHole_glues ha₁ ha₂ hdiv⟩

/-- **Orthogonality, as one statement.** The discipline that bounds fill multiplicity at a site never
glues; the hole that glues bounds nothing about fill multiplicity. Neither predicate is a weakening of
the other, and re-delivery of a single fill (`refill_idempotent`) is outside both — which is why
"one-shot" in a replicated setting means *at most one distinct fill*, never *at most one delivery*. -/
theorem oneshot_orthogonal_to_gluing :
    ¬ Glues oneShotHole
    ∧ Glues anchorHole
    ∧ anchorHole.guard (gsetOf [0] ⊔ (gsetOf [2] ⊔ gsetOf [3])) :=
  ⟨oneShotHole_never_glues, anchorHole_glues, anchorHole_admits_double_fill.2.2.2⟩

/-! ## §10. Non-claims.

**⟨TERMINAL⟩ — theorems of this model, not work left undone.**

* *"Coordination-free" is cited, not proved here.* `IConfluent` is a lattice judgement. The modal
  reading — "**no** implementation can stay coordination-free and convergent" — is Bailis et al.'s
  Theorem 3.1, quantifying over systems, and lives in the paper. `Confluence.lean` draws this boundary
  and this file inherits it unchanged: what a `¬ Glues` result formally provides is the clash-fill
  repro.
* *A fill is a patch, not a resource.* This is a join-semilattice with no bottom, no linearity, no
  δ-bearing quantity. The study's `resourceGuardedFill` — a Boolean guard gating a *linear* fill in an
  indexed-monoidal fibre — is not weakly stated here; it is inexpressible in this vocabulary and needs
  a different structure, not more lemmas.
* *`Spanning` is a hypothesis and stays one.* `stampedHole_glues` + `excl_not_iconfluent` prove the
  iff false without it. That is a theorem about the model, not a gap.
* *`Divergent` is classical.* `comparable_or_divergent` is `Classical.em`, as is
  `escalation_witness`. `Classical.choice` is Lean's, not an added axiom.

**⟨UNDONE⟩ — real work, not done here.**

* *Hole identity.* A hole here is a position in the lattice, not a named slot: two holes in one
  document are two `GuardedHole` values with no shared index. The keyed family `K → GuardedHole S`
  with per-key verdicts — the hole-level analogue of `Confluence.pi_iconfluent` and
  `Spec.Verdict.keyedClash` — is straightforward and absent.
* *Escrowed one-shot.* §9 shows the one-shot guard never glues globally. Whether it is *segmented*
  one-shot — at most one fill per fiber, coordinating only at seam changes — is exactly the question
  `GluesWithin` was built to ask, and it is not asked here.
* *Byzantine / dual-H¹.* The study links non-gluing to a sheaf obstruction. Nothing here computes
  cohomology. `Divergent` plus `clash_divergent` is 1-cocycle-shaped data and no more; calling it an
  H¹ result would be a renaming of the kind §5 exists to rule out.
* *Fill provenance.* `Glues` says the glue is admissible; it says nothing about *whose* fill is
  observed in it. That is the question `MVRegister`/`ORMap` answer for values, and it is untouched for
  fills.
-/

end Uwueave.Gluing
