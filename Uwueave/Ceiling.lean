/-
# Uwueave.Ceiling — the uniqueness ceiling, proved once.

Four refutations in this library are one mathematical fact wearing four
costumes (GROKREVIEW §2.3 called it):

  * `Catalog.gset_atMostOne_not_iconfluent` — at most one **element** in the set;
  * `Sequence.wf_unique_anchor_not_iconfluent` — at most one **anchor per id**;
  * `Authority.wf_unique_not_iconfluent` — at most one **(parent, scope) per grant id**;
  * `Automata.determinism_not_iconfluent` — at most one **target per (state, letter)**.

Each says: over a grow-only set of structured elements, the set must be
*function-shaped* along some selector — at most one element per selector key.
And each dies the same death: two replicas independently observe two *distinct*
elements that *agree on the key*; the union holds both; the function shape is
gone. The fact that the elements, keys and side conditions differ per file is
costume, not content.

This module states the trap once:

  * `UniqueOn sel` — the ceiling invariant shape: at most one present element
    per `sel`-key.
  * `merge_breaks_uniqueOn` — the **generic witness constructor**: hand it two
    distinct elements agreeing on the selector key, one present in each
    replica, and it produces the violation at the merge.
  * `uniqueness_ceiling_clash` / `uniqueness_ceiling` — any invariant that
    *entails* `UniqueOn sel` is refuted by any such pair of legal replicas:
    the clash triple (`escalation_witness`'s shape, but constructive), and the
    `¬ IConfluent` verdict.

Then the four refutations return as one-line instances —
`ceiling_atMostOne`, `ceiling_uniqueAnchor`, `ceiling_uniqueGrant`,
`ceiling_determinism` — each restating its original *verbatim* and citing the
original's own witnesses. The originals stay in their home files, where they
carry the narrative and the `Audit.lean` pins; this module's contribution is
the proof that they were never four theorems.

## What is deliberately NOT an instance

`Authority.sole_admin_not_iconfluent` and `Catalog.or_breaks_iconfluence`
(mutual exclusion) are *spiritually* the same trap — a ceiling on a grow-only
set — but not this selector shape: they cap the number of occupied **keys**
("at most one admin id", "at most one lock holder"), while tolerating several
elements at one key (two grants to the same admin id with different scopes
violate nothing). Two distinct same-key elements therefore do not refute them,
which is exactly the witness `merge_breaks_uniqueOn` constructs — so forcing
them under this lemma would be a lie of shape. They keep their own refutations.
-/
import Uwueave.Sequence
import Uwueave.Authority
import Uwueave.Automata

namespace Uwueave.Ceiling

open Uwueave Uwueave.Catalog

/-! ## §1. The ceiling shape, and the generic witness constructor -/

/-- **The ceiling invariant shape**: the grow-only set is *function-shaped*
along the selector `sel` — any two present elements agreeing on their
`sel`-key are equal, i.e. at most one element per key. Instances: `sel` =
constant (at most one element anywhere), `sel` = id-projection (at most one
payload per id), `sel` = (state, letter) (at most one DFA target per slot). -/
def UniqueOn {α K : Type} (sel : α → K) : Invariant (GSet α) :=
  fun s => ∀ e e' : α, s e = true → s e' = true → sel e = sel e' → e = e'

/-- **The generic witness constructor.** Given two *distinct* elements that
*agree on the selector key*, one present in each replica, the merge violates
`UniqueOn sel`: the union holds both elements, their keys are equal, and the
function shape would force the elements equal — contradiction. Every concrete
ceiling clash in this library is this term applied to its own pair. -/
theorem merge_breaks_uniqueOn {α K : Type} {sel : α → K} {e e' : α}
    (hkey : sel e = sel e') (hne : e ≠ e') {x y : GSet α}
    (hex : x e = true) (hey : y e' = true) : ¬ UniqueOn sel (x ⊔ y) :=
  fun huniq =>
    hne (huniq e e'
      (show (x e || y e) = true by simp [hex])
      (show (x e' || y e') = true by simp [hey]) hkey)

/-- **The clash, packaged constructively** — the triple of
`escalation_witness`, with no classical detour: if `I` entails the ceiling
shape `UniqueOn sel`, then any two `I`-legal replicas exhibiting two distinct
same-key elements are a clash pair — each side legal, the merge illegal. -/
theorem uniqueness_ceiling_clash {α K : Type} (sel : α → K)
    {I : Invariant (GSet α)} (himp : ∀ s, I s → UniqueOn sel s)
    {e e' : α} (hkey : sel e = sel e') (hne : e ≠ e') {x y : GSet α}
    (hx : I x) (hy : I y) (hex : x e = true) (hey : y e' = true) :
    I x ∧ I y ∧ ¬ I (x ⊔ y) :=
  ⟨hx, hy, fun hbad => merge_breaks_uniqueOn hkey hne hex hey (himp _ hbad)⟩

/-- **The uniqueness ceiling.** Any invariant entailing "at most one element
per selector key" over a grow-only set is **not I-confluent**, as soon as the
trap is inhabited: two legal replicas holding two distinct same-key elements.
This is the one theorem behind `ceiling_atMostOne`, `ceiling_uniqueAnchor`,
`ceiling_uniqueGrant` and `ceiling_determinism` below. -/
theorem uniqueness_ceiling {α K : Type} (sel : α → K)
    {I : Invariant (GSet α)} (himp : ∀ s, I s → UniqueOn sel s)
    {e e' : α} (hkey : sel e = sel e') (hne : e ≠ e') {x y : GSet α}
    (hx : I x) (hy : I y) (hex : x e = true) (hey : y e' = true) :
    ¬ IConfluent I :=
  fun hconf =>
    (uniqueness_ceiling_clash sel himp hkey hne hx hy hex hey).2.2
      (hconf x y hx hy)

/-! ## §2. Singleton replicas are always inside the ceiling

The legal replicas the corollaries feed the constructor are one-element
indicators (`Delta.addDelta`), and a one-element set is function-shaped along
*every* selector. -/

/-- A singleton holds one element: any two present elements are equal. -/
theorem addDelta_unique {α : Type} [DecidableEq α] {a e e' : α}
    (he : Delta.addDelta a e = true) (he' : Delta.addDelta a e' = true) :
    e = e' := by
  simp only [Delta.addDelta, decide_eq_true_eq] at he he'
  rw [he, he']

/-- A singleton replica satisfies `UniqueOn sel` for every selector. -/
theorem addDelta_uniqueOn {α K : Type} [DecidableEq α] (a : α) (sel : α → K) :
    UniqueOn sel (Delta.addDelta a) :=
  fun _ _ he he' _ => addDelta_unique he he'

/-- A singleton holds at most one element — `addDelta_unique` in the exact
phrasing `Catalog.gset_atMostOne_not_iconfluent`'s invariant asks for. -/
theorem addDelta_atMostOne {α : Type} [DecidableEq α] (a : α) :
    ∀ m n : α, Delta.addDelta a m = true → Delta.addDelta a n = true → m = n :=
  fun _ _ hm hn => addDelta_unique hm hn

/-- A singleton transition table is deterministic — `addDelta_unique` in the
phrasing `Automata.Deterministic` asks for. -/
theorem addDelta_deterministic (e : Nat × Nat × Nat) :
    Automata.Deterministic (Delta.addDelta e) :=
  fun _ _ _ _ h₁ h₂ => congrArg (fun g => g.2.2) (addDelta_unique h₁ h₂)

/-! ## §3. The four costumes entail the one shape

One bridge lemma per file: its uniqueness hypothesis IS `UniqueOn` at the
right selector. -/

/-- "At most one element" is `UniqueOn` at the *constant* selector: every
element shares the one key, so per-key uniqueness collapses to global
uniqueness. -/
theorem atMostOne_entails_uniqueOn {α : Type} (s : GSet α)
    (h : ∀ m n : α, s m = true → s n = true → m = n) :
    UniqueOn (fun _ => ()) s :=
  fun e e' he he' _ => h e e' he he'

/-- `Sequence.UniqueAnchor` — one anchor per inserted id — is `UniqueOn` at
the id selector `Prod.fst` on insertion pairs `(id, anchor)`. -/
theorem uniqueAnchor_entails_uniqueOn {s : Sequence.SeqState}
    (h : Sequence.UniqueAnchor s) : UniqueOn Prod.fst s := by
  intro e e' he he' hk
  obtain ⟨i, a⟩ := e
  obtain ⟨i', a'⟩ := e'
  have hi : i = i' := hk
  subst hi
  have ha : a = a' := h i a a' he he'
  subst ha
  rfl

/-- `Authority.UniqueGrant` — one (parent, scope) per grant id — is `UniqueOn`
at the id selector `Prod.fst` on grant triples `(id, parent, scope)`. -/
theorem uniqueGrant_entails_uniqueOn {s : Authority.GrantSet}
    (h : Authority.UniqueGrant s) : UniqueOn Prod.fst s := by
  intro e e' he he' hk
  obtain ⟨i, p, σ⟩ := e
  obtain ⟨i', p', σ'⟩ := e'
  have hi : i = i' := hk
  subst hi
  obtain ⟨hp, hσ⟩ := h i p σ p' σ' he he'
  subst hp
  subst hσ
  rfl

/-- `Automata.Deterministic` — one target per (state, letter) slot — is
`UniqueOn` at the slot selector on transition triples `(state, letter,
target)`. -/
theorem deterministic_entails_uniqueOn {δ : Automata.Transitions}
    (h : Automata.Deterministic δ) : UniqueOn (fun e => (e.1, e.2.1)) δ := by
  intro e e' he he' hk
  obtain ⟨q, a, t⟩ := e
  obtain ⟨q', a', t'⟩ := e'
  have hq : q = q' := congrArg Prod.fst hk
  have ha : a = a' := congrArg Prod.snd hk
  subst hq
  subst ha
  have ht : t = t' := h q a t t' he he'
  subst ht
  rfl

/-! ## §4. The four refutations, as one-line instances

Each corollary restates its original **verbatim** — same state space, same
invariant — and is one application of `uniqueness_ceiling`, at the original's
own witness pair. The originals in their home files are untouched; compare the
statements side by side and the costume dissolves. -/

/-- `Catalog.gset_atMostOne_not_iconfluent`, re-derived: "at most one element"
is the ceiling at the constant selector; the clash pair is the singletons
`{0}` and `{1}` (as `Delta.addDelta` indicators — same sets as the original's
`n == 0` / `n == 1`). -/
theorem ceiling_atMostOne :
    ¬ IConfluent (S := GSet Nat)
      (fun s => ∀ m n, s m = true → s n = true → m = n) :=
  uniqueness_ceiling (fun _ => ()) atMostOne_entails_uniqueOn
    (e := 0) (e' := 1) rfl (by decide)
    (addDelta_atMostOne 0) (addDelta_atMostOne 1) (by decide) (by decide)

/-- `Sequence.wf_unique_anchor_not_iconfluent`, re-derived: per-id anchor
uniqueness is the ceiling at the id selector; the clash pair is the original's
`dupX` / `dupY`, whose same-id elements `(2, 1)` and `(2, 0)` disagree on the
anchor. (`WF 5` rides along inside `I` and is simply discarded by the
entailment — the ceiling conjunct alone dies at the merge.) -/
theorem ceiling_uniqueAnchor :
    ¬ IConfluent (S := Sequence.SeqState)
      (fun s => Sequence.WF 5 s ∧ Sequence.UniqueAnchor s) :=
  uniqueness_ceiling Prod.fst (fun _ h => uniqueAnchor_entails_uniqueOn h.2)
    (e := (2, 1)) (e' := (2, 0)) rfl (by decide)
    ⟨Sequence.dupX_wf, Sequence.dupX_unique⟩
    ⟨Sequence.dupY_wf, Sequence.dupY_unique⟩ (by decide) (by decide)

/-- `Authority.wf_unique_not_iconfluent`, re-derived: per-id grant uniqueness
is the ceiling at the id selector; the clash pair is the original's `dupA` /
`dupB`, whose same-id elements `(2, 1, 3)` and `(2, 0, 4)` disagree on
(parent, scope). (`WF 9` rides along inside `I`, discarded by the
entailment.) -/
theorem ceiling_uniqueGrant :
    ¬ IConfluent (S := Authority.GrantSet)
      (fun s => Authority.WF 9 s ∧ Authority.UniqueGrant s) :=
  uniqueness_ceiling Prod.fst (fun _ h => uniqueGrant_entails_uniqueOn h.2)
    (e := (2, 1, 3)) (e' := (2, 0, 4)) rfl (by decide)
    ⟨Authority.dupA_wf, Authority.dupA_unique⟩
    ⟨Authority.dupB_wf, Authority.dupB_unique⟩ (by decide) (by decide)

/-- `Automata.determinism_not_iconfluent`, re-derived: DFA determinism is the
ceiling at the (state, letter) selector; the clash pair is the original's own
`Delta.addDelta (0, 0, 0)` / `Delta.addDelta (0, 0, 1)` — same slot, targets
`0` versus `1`. -/
theorem ceiling_determinism :
    ¬ IConfluent (S := Automata.Transitions) Automata.Deterministic :=
  uniqueness_ceiling (fun e => (e.1, e.2.1))
    (fun _ => deterministic_entails_uniqueOn)
    (e := (0, 0, 0)) (e' := (0, 0, 1)) rfl (by decide)
    (addDelta_deterministic (0, 0, 0)) (addDelta_deterministic (0, 0, 1))
    (by decide) (by decide)

end Uwueave.Ceiling
