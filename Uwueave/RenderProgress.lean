/-
# Uwueave.RenderProgress — truth, progress and affordance, told apart; and the
absence slogan corrected by a witness rather than by a hedge.

`RenderSix.lean` closed the sixth-cell gap and, in closing it, wrote one clause
that mixes two different questions:

> `pending_escapable : ∀ s, peval s = pending → ∃ t, F s t ∧ peval t ≠ pending`

An external review (codex) read the supplied proof and found what it actually
does: `RenderSix.statusOf_pending_escapable` builds the escaping future by
**adding an arbitrary inhabitant at an owed source**. That is valid for the
abstract relation and establishes nothing about a real delivery pool or about
any scheduler. So the clause is neither the epistemic honesty condition nor a
deployment-liveness condition, and this file splits it into the three things it
was standing in for.

⚠ **And the clause is weaker than even that reading suggests.** §1 exhibits
`sealAll` — certify every source you are still owed — and proves
`statusOf_pending_escapable_by_sealing`: `pending_escapable` is discharged for
**every** value type, with **no** `Inhabited`, **no** `DecidableEq`, and **no
candidate arriving at all**. The escape witness is the state in which the
surface *gives up on every peer*. A clause a spinner satisfies by giving up is
not a liveness clause. (This also retires `RenderSix.lean`'s ⟨TERMINAL⟩ boundary
item *"`pending_escapable` needs an inhabitant of the value type"* — it does
not; `sealAll` needs nothing.)

## The three contracts (§1–§4)

  * **`PendingSound`** — epistemic truth NOW. No candidate, evidence not closed.
    Mentions no future at all, and is refuted at a **single state**:
    `spinnerRender_is_not_pendingSound` needs no "spins forever" argument, only
    the fact that `emptyClosedW` is closed. This is codex's *a spinner on
    definitively-absent evidence is wrong immediately*.
  * **`PendingProgress`** — a TEMPORAL theorem under environmental premises: a
    fair schedule (`Liveness.FairOn`), issued deltas that really are deliveries
    (`IsDelivery`), and a required source that really responds (`Responsive`).
    The conclusion is about the state a **scheduler actually reaches**, and it
    is proved through `Liveness.fair_converges` — the existing fair-delivery
    machinery, not a new one.
  * **`PendingActionable`** — the UI AFFORDANCE. A discharge action, an actor,
    and an **authorization proof** (`Authority.Active`). The button is offered
    relative to live delegated authority, and `a_revoked_actor_gets_no_button`
    shows the authorization field is load-bearing rather than decorative.

The two separations codex's sentence asks for are theorems here:

  * `escapability_does_not_imply_epistemic_truth` — `unrelatedEscape` satisfies
    `pending_escapable` at every state and still spins on definitively-absent
    evidence;
  * `a_truthful_spinner_may_wait_forever` — `statusOf` is `PendingSound`, says
    `pending` at `emptyOpenW`, and **every** fair schedule over an empty issued
    pool leaves it `pending`. A peer that never returns is not an epistemic lie.

## §5 — the absence slogan, corrected by witnesses

`RenderSix.absence_is_the_more_defensible_badge` was written up as *"absence is
the more defensible badge"*. The precise theorem is **"closed emptiness is
merge-closed in this evidence algebra; unrestricted singleton determinacy is
not"**, and §5 proves the correction with three exact badges that ARE merge-safe:

  * `anyCandidate_true_iconfluent` — a grow-only existential's `true` is
    merge-safe **unilaterally**: one replica's `true` survives a merge with an
    arbitrary peer, no agreement needed;
  * `statusOf_exact_agree_merges` — two replicas holding the **same** canonical
    exact value do not fork;
  * `lww_exact_is_merge_safe` — in a selection lattice an exact result stays
    exact by construction (`Catalog.selection_iconfluent`, instantiated).

⚠ And the correction cuts the other way too: `absence_is_not_unilaterally_merge_
closed` shows `absent` needs **both** replicas to assert it, while the
existential badge needs **one**. So on the merge axis absence is not even the
strongest badge available. What fails is the promise *"there is exactly one
ARBITRARY candidate value"* — a uniqueness ceiling, the same shape as
`Catalog.gset_atMostOne_not_iconfluent`.

## §6 — scoped absence

`AbsentOn A e` is "no answer, within scope `A`". The verdict is two-sided:
composition **holds** to the union scope (`absentOn_union`) and reaches
unscoped absence **only** under an explicit coverage premise
(`absentOn_covering_is_global`); without it,
`scoped_absence_does_not_reach_global` exhibits two epochs each definitively
empty whose union leaves the global status `pending`.

## §7 — the semantic widget

Codex: the loading-forever bug can be constrained more than salience can.
`SemanticWidget` is the intermediate contract — `finality`, `plurality`,
`pendingAction`, `candidates` — and `HonestWidget` pins two cells:
`absent → finality = terminal`, `pending → finality = open'`. From those two
clauses:

  * `no_honest_widget_loads_at_absent` — a dishonest `loading` is **excluded**;
  * `constant_widget_is_not_honest` — and, unlike salience, a **constant**
    assignment is excluded outright, because one value cannot be both terminal
    and open. That is strictly more than the salience limit gives.

## Honest boundary

⟨TERMINAL⟩ identifies a theorem of the model. Any tracked work below is
named at the substantive caveat it belongs to.

  * **Salience survives, at the last hop.** ⟨TERMINAL⟩
    `salience_is_still_not_enforceable_after_the_widget`: `HonestWidget`
    constrains the *semantic* layer; the map `SemanticWidget α → β` that paints
    pixels may still be constant, and six widgets can still be one grey pixel.
    No interface reaches past its own output type, and this one does not either.
  * **`PendingProgress`'s premises are environmental, and they are premises.**
    ⟨TERMINAL⟩ `Responsive` says the issued pool holds a contribution from an
    owed, uncertified source; `FairOn` says the schedule covers the replica.
    Neither is discharged here, because neither is a fact about a renderer —
    that is the whole content of the split, and `a_truthful_spinner_may_wait_
    forever` is the theorem that they can genuinely fail.
  * **Fairness is `Liveness.lean`'s finite covering.** ⟨TERMINAL at this model⟩
    Not a coinductive stream, no clocks, no probability. `Liveness.lean` §7's
    scope seal is inherited verbatim; "eventually" here means "after the finite
    schedule that covers this replica".
  * **`PendingActionable` proves the offer exists, not that pressing it is
    wise.** ⟨TERMINAL⟩ The discharge witness is `sealAll` — give up on every
    peer — which is honest (`absent` is then true of the evidence) and lossy (a
    peer that would have answered is now certified silent). Which discharge a
    surface should offer is a product decision the type does not make. Its
    `DischargeOffer` nevertheless closes `HonestRender`'s structural affordance
    boundary: actor, live authorization, permitted effect, and discharge proof
    all travel together.
  * **The inherited three-cell limit now has a total adapter.**
    ⟨HISTORICAL LIMIT, DISCHARGED BY `StatusEffects`⟩ This file still deepens
    the `pending` cell against `RenderSix.SoundEvaluator6`; it does not silently
    strengthen that compatibility contract. `StatusEffects.TotalSoundEvaluator6`
    supplies complete semantic rows for all six cells,
    `statusOf_totalSound6` proves them for the sanctioned evaluator, and
    `toSoundEvaluator6` preserves every consumer of the original contract. The
    old/new separation is witnessed by `closedForkAsOpen_old_sound` and
    `closedForkAsOpen_not_total`.
  * **Noncomputability is inherited.** ⟨TERMINAL at this carrier⟩ `statusOf` and
    everything built on it quantify over an unbounded value type;
    `Classical.choice` is inside the audit floor.
-/
import Uwueave.RenderSix
import Uwueave.Liveness
import Uwueave.Authority

namespace Uwueave.RenderProgress

open Uwueave Uwueave.Catalog
open Uwueave.ResultStatus (Status statusOf)
open Uwueave.RenderSix (values_of_statusOf_exact values_of_statusOf_absent
  values_of_statusOf_pending)

/-! ## §1. The give-up escape — why `pending_escapable` is not a liveness clause.

`RenderSix.statusOf_pending_escapable` takes an `a₀ : β` and constructs the
escape by having a value arrive. `sealAll` shows the clause is far cheaper than
that: certify every source still owed and the status becomes `absent`, with the
candidate set **untouched** and no hypothesis on `β` whatsoever.

So `pending_escapable` is satisfied by the move "give up on every peer". A
renderer discharges it without any peer ever answering, which is exactly why it
cannot be the liveness condition — and why it cannot be the truth condition
either, since it says nothing about the state where the badge is shown. -/

/-- **The give-up state**: certify every source still owed. Candidates are
untouched — nothing is delivered, nothing is deleted; the only thing that moves
is the closure claim. -/
def sealAll {β : Type} (e : Evidence.ResultEvidence β) : Evidence.ResultEvidence β :=
  (Evidence.candidates e, Evidence.obligations e,
    Evidence.certificates e ⊔ Evidence.obligations e)

/-- Giving up deletes no evidence: the candidate set is equal before and after. -/
theorem sealAll_keeps_candidates {β : Type} (e : Evidence.ResultEvidence β) :
    Evidence.candidates (sealAll e) = Evidence.candidates e := rfl

/-- …and therefore the value axis is equal too. -/
theorem sealAll_keeps_values {β : Type} (e : Evidence.ResultEvidence β) :
    Evidence.values (sealAll e) = Evidence.values e :=
  Evidence.values_congr (sealAll_keeps_candidates e)

/-- The give-up state is closed: every obligation now carries a certificate. -/
theorem closed_sealAll {β : Type} (e : Evidence.ResultEvidence β) :
    Evidence.Closed (sealAll e) := by
  intro o ho
  have ho' : Evidence.obligations e o = true := ho
  show (Evidence.certificates e o || Evidence.obligations e o) = true
  rw [ho']
  exact Bool.or_true _

/-- Giving up is a **permitted** move: it is a sealed future. It goes up the
lattice (certificates only grow), admits no new candidate (there are none), and
adds no source to the roster. -/
theorem sealed_sealAll {β : Type} (e : Evidence.ResultEvidence β) :
    Evidence.SealedFuture e (sealAll e) := by
  refine ⟨⟨Evidence.leq_of_components (leq_refl _) (leq_refl _) (le_merge_left _ _), ?_⟩,
    fun _ h => h⟩
  intro p h1 h2
  exact Bool.noConfusion (h1.symm.trans h2)

/-- At an empty candidate set the give-up state reports definitive absence. -/
theorem statusOf_sealAll_absent {β : Type} {e : Evidence.ResultEvidence β}
    (h : ∀ a, Evidence.values e a = false) : statusOf (sealAll e) = Status.absent := by
  refine ResultStatus.statusOf_absent (fun a => ?_) (closed_sealAll e)
  rw [sealAll_keeps_values e]
  exact h a

theorem absent_ne_pending {β : Type} :
    (Status.absent : Status β) ≠ Status.pending :=
  ResultStatus.status_ne_of_tag (by simp [ResultStatus.statusTag])

theorem provisional_ne_pending {β : Type} (a : β) :
    (Status.provisional a : Status β) ≠ Status.pending :=
  ResultStatus.status_ne_of_tag (by simp [ResultStatus.statusTag])

/-- ⚠ **`pending_escapable` IS DISCHARGED BY GIVING UP.** For every value type —
no `Inhabited`, no `DecidableEq`, no arrival — a `pending` status has a
permitted future that is not `pending`: seal the roster and the badge becomes
`absent`.

Compare `RenderSix.statusOf_pending_escapable`, which asks for an `a₀ : β`
because "the only thing that stops a spinner is a value arriving". A value
arriving is *one* way; declaring the wait over is another, and the clause cannot
tell them apart. That is the defect the rest of this file repairs. -/
theorem statusOf_pending_escapable_by_sealing {β : Type}
    {e : Evidence.ResultEvidence β} (h : statusOf e = Status.pending) :
    ∃ t, Evidence.SealedFuture e t ∧ statusOf t ≠ Status.pending := by
  refine ⟨sealAll e, sealed_sealAll e, ?_⟩
  rw [statusOf_sealAll_absent (values_of_statusOf_pending h).1]
  exact absent_ne_pending

/-- ⚠ **THE CLAUSE, PRICED.** Four facts side by side: the escape exists at every
value type; the witness is the give-up state; that state is closed; and its
candidate set is **equal** to the one the spinner was shown at. Nothing was
delivered, and the clause is satisfied. -/
theorem the_old_clause_is_discharged_by_giving_up (β : Type) :
    (∀ e : Evidence.ResultEvidence β, statusOf e = Status.pending →
        ∃ t, Evidence.SealedFuture e t ∧ statusOf t ≠ Status.pending)
      ∧ (∀ e : Evidence.ResultEvidence β, Evidence.Closed (sealAll e))
      ∧ (∀ e : Evidence.ResultEvidence β,
          Evidence.candidates (sealAll e) = Evidence.candidates e)
      ∧ (∀ e : Evidence.ResultEvidence β, Evidence.SealedFuture e (sealAll e)) :=
  ⟨fun _ h => statusOf_pending_escapable_by_sealing h, closed_sealAll,
   sealAll_keeps_candidates, sealed_sealAll⟩

/-! ## §2. `PendingSound` — epistemic truth NOW.

The first of the three. It quantifies over **no** future: a `pending` badge is
honest at the state where it is shown exactly when there is no candidate and the
evidence is not closed. `Settled` is the abstract stand-in for
`Evidence.Closed`, so the contract states at any carrier and is discharged at
the deployed one.

The point of the shape is where a violation is caught: at a **single state**,
with no reasoning about futures at all. -/

/-- **The epistemic honesty condition for a spinner.** No candidate is known,
and the evidence is not settled. Truth *now*, at the state the badge is shown —
this is what a `pending` badge asserts, and nothing more. -/
structure PendingSound {S β : Type} (answer : S → GSet β) (Settled : S → Prop)
    (peval : S → Status β) : Prop where
  /-- A `pending` badge is shown only where nothing has been observed. -/
  pending_empty : ∀ s, peval s = Status.pending → ∀ a, answer s a = false
  /-- A `pending` badge is shown only where the evidence is **not** settled. This
  is the clause that fires on "loading forever on an empty result", and it fires
  at the state itself. -/
  pending_unsettled : ∀ s, peval s = Status.pending → ¬ Settled s

/-- **The sanctioned renderer is epistemically sound.** `statusOf`'s `pending`
inversion is exactly the two clauses. -/
theorem statusOf_pendingSound {β : Type} :
    PendingSound (S := Evidence.ResultEvidence β) Evidence.values Evidence.Closed statusOf where
  pending_empty := fun _ h => (values_of_statusOf_pending h).1
  pending_unsettled := fun _ h => (values_of_statusOf_pending h).2

/-- ⚠ **THE SPINNER IS REFUTED AT ONE STATE.** `RenderSix.spinnerRender_is_not_
sound6` needs `spinnerRender_spins_forever` — a statement about **every** sealed
future of `emptyClosedW`. `PendingSound` needs only that `emptyClosedW` is
closed. Same bug, no future reasoning: the lie is about the state, so the
refutation should be too. -/
theorem spinnerRender_is_not_pendingSound :
    ¬ PendingSound (S := Evidence.ResultEvidence Holes.Val) Evidence.values
        Evidence.Closed RenderSix.spinnerRender := by
  intro hs
  exact hs.pending_unsettled ResultStatus.emptyClosedW RenderSix.spinnerRender_emptyClosedW
    ResultStatus.closed_emptyClosedW

/-! ### `pending_escapable` does not imply `PendingSound`

Codex: *conversely a spinner on definitively-absent evidence is wrong
immediately even if some unrelated future exists.* Here is that renderer. It
reads one certificate and nothing else, so it spins at `emptyClosedW` — where
the answer is definitively absent — and yet it satisfies `pending_escapable` at
**every** state, because certifying `bob` is always a permitted future. -/

/-- A renderer that badges on one unrelated certificate: `absent` once `bob` is
certified, `pending` otherwise. It reads neither the candidates nor the closure
of the evidence it is shown at. -/
def unrelatedEscape (e : Evidence.ResultEvidence Holes.Val) : Status Holes.Val :=
  match Evidence.certificates e Evidence.bob with
  | true => Status.absent
  | false => Status.pending

/-- Certifying one source is always a sealed future. -/
theorem sealed_certify {β : Type} (e : Evidence.ResultEvidence β) (o : Evidence.Source) :
    Evidence.SealedFuture e (Evidence.certify e o) := by
  refine ⟨⟨Evidence.certify_grows e o, ?_⟩, fun _ h => h⟩
  intro p h1 h2
  exact Bool.noConfusion (h1.symm.trans h2)

/-- **…and it satisfies the old clause everywhere.** Whatever state it is shown
at, certifying `bob` is permitted and turns its badge to `absent`. -/
theorem unrelatedEscape_escapable (e : Evidence.ResultEvidence Holes.Val)
    (_h : unrelatedEscape e = Status.pending) :
    ∃ t, Evidence.SealedFuture e t ∧ unrelatedEscape t ≠ Status.pending := by
  refine ⟨Evidence.certify e Evidence.bob, sealed_certify e Evidence.bob, ?_⟩
  have hc : Evidence.certificates (Evidence.certify e Evidence.bob) Evidence.bob = true := by
    show (Evidence.certificates e Evidence.bob || decide (Evidence.bob = Evidence.bob)) = true
    exact Bool.or_true _
  have habs : unrelatedEscape (Evidence.certify e Evidence.bob) = Status.absent := by
    unfold unrelatedEscape
    rw [hc]
  rw [habs]
  exact absent_ne_pending

/-- ⚠ **…and it is an epistemic lie.** At `emptyClosedW` — no candidate, roster
closed, `statusOf` says `absent` — it shows a spinner. `PendingSound` catches
it; `pending_escapable` does not, because an unrelated future exists. -/
theorem unrelatedEscape_is_not_pendingSound :
    ¬ PendingSound (S := Evidence.ResultEvidence Holes.Val) Evidence.values
        Evidence.Closed unrelatedEscape := by
  intro hs
  refine hs.pending_unsettled ResultStatus.emptyClosedW ?_ ResultStatus.closed_emptyClosedW
  have hb : Evidence.certificates ResultStatus.emptyClosedW Evidence.bob = false := by decide
  unfold unrelatedEscape
  rw [hb]

/-- ⚠ **THE FIRST SEPARATION.** `pending_escapable` holds of `unrelatedEscape` at
every state; `PendingSound` fails of it at a named one, where the evidence is
closed and `statusOf` reports definitive absence. So the clause
`RenderSix.SoundEvaluator6` carries is **not** the honesty condition — a
renderer can satisfy it and still spin on an answer that will never come. -/
theorem escapability_does_not_imply_epistemic_truth :
    (∀ e : Evidence.ResultEvidence Holes.Val, unrelatedEscape e = Status.pending →
        ∃ t, Evidence.SealedFuture e t ∧ unrelatedEscape t ≠ Status.pending)
      ∧ ¬ PendingSound (S := Evidence.ResultEvidence Holes.Val) Evidence.values
          Evidence.Closed unrelatedEscape
      ∧ unrelatedEscape ResultStatus.emptyClosedW = Status.pending
      ∧ Evidence.Closed ResultStatus.emptyClosedW
      ∧ statusOf ResultStatus.emptyClosedW = Status.absent := by
  refine ⟨unrelatedEscape_escapable, unrelatedEscape_is_not_pendingSound, ?_,
    ResultStatus.closed_emptyClosedW, ResultStatus.statusOf_emptyClosedW⟩
  have hb : Evidence.certificates ResultStatus.emptyClosedW Evidence.bob = false := by decide
  unfold unrelatedEscape
  rw [hb]

/-! ## §3. `PendingProgress` — the temporal theorem, under environmental premises.

The second of the three, and the one the old clause was pretending to be. It
does not quantify over "some permitted future"; it quantifies over the state a
**scheduler reaches**, and it rides `Liveness.lean`'s fair-delivery machinery
rather than inventing one.

Three premises, all environmental and none a fact about the renderer:

  * `Liveness.FairOn replicas issued sched` — the schedule covers the replica;
  * `IsDelivery e δ` for each issued delta — what is shipped is a *delivery*
    from a source `e` already owes and has not certified, not roster growth;
  * `Responsive e issued` — some required source really does contribute.

The conclusion has two halves: the reached state is a **permitted** (sealed)
future of `e`, and its status is not `pending`. -/

/-- **What a shipped delta may be.** Candidates only from sources `e` already
owes and has not certified, and no obligation `e` did not already carry. This is
`Evidence.Admits` as a property of the *payload* rather than of a step. -/
def IsDelivery {β : Type} (e δ : Evidence.ResultEvidence β) : Prop :=
  (∀ p : β × Evidence.Source, Evidence.candidates δ p = true →
      Evidence.obligations e p.2 = true ∧ Evidence.certificates e p.2 = false)
    ∧ (∀ o, Evidence.obligations δ o = true → Evidence.obligations e o = true)

/-- **The required sources can respond**: the issued pool really holds a
contribution attributed to a source that is owed and uncertified at `e`. This is
the premise `RenderSix.statusOf_pending_escapable` supplies by *fiat* — it
invents `a₀` — and that is the substitution codex caught. -/
def Responsive {β : Type} (e : Evidence.ResultEvidence β)
    (issued : List (Evidence.ResultEvidence β)) : Prop :=
  ∃ δ, δ ∈ issued ∧ ∃ (a : β) (o : Evidence.Source),
    Evidence.candidates δ (a, o) = true
      ∧ Evidence.obligations e o = true ∧ Evidence.certificates e o = false

/-- A candidate in a fold of deliveries came from the base or from one delta. -/
theorem candidates_joinAll_cases {β : Type} :
    ∀ (l : List (Evidence.ResultEvidence β)) (e : Evidence.ResultEvidence β)
      (p : β × Evidence.Source),
      Evidence.candidates (Delta.joinAll e l) p = true →
        Evidence.candidates e p = true ∨ ∃ δ, δ ∈ l ∧ Evidence.candidates δ p = true
  | [], _, _, h => Or.inl h
  | d :: l, e, p, h => by
      rcases candidates_joinAll_cases l (e ⊔ d) p h with h1 | ⟨δ, hδ, hc⟩
      · rcases (Bool.or_eq_true _ _).mp
          (show (Evidence.candidates e p || Evidence.candidates d p) = true from h1) with h2 | h2
        · exact Or.inl h2
        · exact Or.inr ⟨d, List.Mem.head l, h2⟩
      · exact Or.inr ⟨δ, List.Mem.tail d hδ, hc⟩

/-- An obligation in a fold of deliveries came from the base or from one delta. -/
theorem obligations_joinAll_cases {β : Type} :
    ∀ (l : List (Evidence.ResultEvidence β)) (e : Evidence.ResultEvidence β)
      (o : Evidence.Source),
      Evidence.obligations (Delta.joinAll e l) o = true →
        Evidence.obligations e o = true ∨ ∃ δ, δ ∈ l ∧ Evidence.obligations δ o = true
  | [], _, _, h => Or.inl h
  | d :: l, e, o, h => by
      rcases obligations_joinAll_cases l (e ⊔ d) o h with h1 | ⟨δ, hδ, hc⟩
      · rcases (Bool.or_eq_true _ _).mp
          (show (Evidence.obligations e o || Evidence.obligations d o) = true from h1) with h2 | h2
        · exact Or.inl h2
        · exact Or.inr ⟨d, List.Mem.head l, h2⟩
      · exact Or.inr ⟨δ, List.Mem.tail d hδ, hc⟩

/-- **A fold of deliveries stays inside the permitted future.** Delivering
issued deltas that are genuine deliveries lands in a sealed future of the state
they were shipped to — no source appears that was not already owed. -/
theorem sealed_joinAll_of_deliveries {β : Type} (e : Evidence.ResultEvidence β)
    (l : List (Evidence.ResultEvidence β)) (h : ∀ δ ∈ l, IsDelivery e δ) :
    Evidence.SealedFuture e (Delta.joinAll e l) := by
  refine ⟨⟨Delta.le_joinAll e l, ?_⟩, ?_⟩
  · intro p h1 h2
    rcases candidates_joinAll_cases l e p h2 with hc | ⟨δ, hδ, hc⟩
    · exact absurd (h1.symm.trans hc) Bool.noConfusion
    · exact (h δ hδ).1 p hc
  · intro o ho
    rcases obligations_joinAll_cases l e o ho with h1 | ⟨δ, hδ, h1⟩
    · exact h1
    · exact (h δ hδ).2 o h1

/-- ⚠ **THE PROGRESS THEOREM.** Under a fair schedule of genuine deliveries from
a responsive pool, the replica reaches a **permitted** future of `e` whose status
is not `pending`.

Read the difference from `pending_escapable`: the state here is
`Liveness.runDeliveries … r`, the state a *scheduler produced*, and the reason it
leaves `pending` is that a delta someone actually issued was actually delivered.
No inhabitant is invented and no roster is sealed. -/
theorem pending_progress_under_fair_delivery {β ι : Type} [DecidableEq ι]
    (e : Evidence.ResultEvidence β) (issued : List (Evidence.ResultEvidence β))
    (sched : List (ι × Evidence.ResultEvidence β)) (replicas : List ι) {r : ι}
    (hr : r ∈ replicas)
    (hfair : Liveness.FairOn replicas issued sched)
    (hdel : ∀ δ ∈ issued, IsDelivery e δ)
    (hresp : Responsive e issued) :
    Evidence.SealedFuture e (Liveness.runDeliveries (fun _ => e) sched r)
      ∧ statusOf (Liveness.runDeliveries (fun _ => e) sched r) ≠ Status.pending := by
  rw [Liveness.fair_converges e issued sched replicas hfair r hr]
  refine ⟨sealed_joinAll_of_deliveries e issued hdel, ?_⟩
  obtain ⟨δ, hδ, a, o, hc, _, _⟩ := hresp
  intro hp
  have hval : Evidence.values (Delta.joinAll e issued) a = true :=
    (Evidence.mem_values _ a).mpr
      ⟨o, Evidence.candidates_grow (Delta.mem_le_joinAll hδ e) hc⟩
  rw [(values_of_statusOf_pending hp).1 a] at hval
  exact Bool.noConfusion hval

/-- **The deployment-liveness contract**, bundled: a `pending` badge, a fair
schedule, genuine deliveries and a responsive pool leave `pending` at a
permitted future the scheduler reached. -/
def PendingProgress {β ι : Type} [DecidableEq ι]
    (peval : Evidence.ResultEvidence β → Status β) : Prop :=
  ∀ (e : Evidence.ResultEvidence β) (issued : List (Evidence.ResultEvidence β))
    (sched : List (ι × Evidence.ResultEvidence β)) (replicas : List ι) (r : ι),
    peval e = Status.pending → r ∈ replicas →
    Liveness.FairOn replicas issued sched →
    (∀ δ ∈ issued, IsDelivery e δ) → Responsive e issued →
    Evidence.SealedFuture e (Liveness.runDeliveries (fun _ => e) sched r)
      ∧ peval (Liveness.runDeliveries (fun _ => e) sched r) ≠ Status.pending

/-- **The sanctioned renderer makes progress.** -/
theorem statusOf_pendingProgress {β ι : Type} [DecidableEq ι] :
    PendingProgress (β := β) (ι := ι) statusOf :=
  fun e issued sched replicas _r _ hr hfair hdel hresp =>
    pending_progress_under_fair_delivery e issued sched replicas hr hfair hdel hresp

/-! ### `PendingProgress` is not about an empty class: a scheduled run

`bob` is owed and uncertified at `emptyOpenW`. One delta carries his `47`; a
one-round fair schedule delivers it to both replicas; the reached state **is**
`ResultStatus.bobSpokeW`, and its status is `provisional 47`. -/

/-- The delta `bob` ships: his candidate `47`, and nothing else. -/
def deliverBob47 : Evidence.ResultEvidence Holes.Val :=
  (ResultStatus.cand47bob, fun _ => false, fun _ => false)

/-- Delivering `bob`'s delta into `emptyOpenW` **is** `bobSpokeW` — the evidence
`ResultStatus.lean` already names as the sealed future in which `bob` speaks. -/
theorem emptyOpenW_merge_deliverBob47 :
    ResultStatus.emptyOpenW ⊔ deliverBob47 = ResultStatus.bobSpokeW := by
  refine Prod.ext (funext fun p => ?_) (Prod.ext (funext fun o => ?_) (funext fun o => ?_))
  · show (ResultStatus.candNone p || ResultStatus.cand47bob p) = ResultStatus.cand47bob p
    rfl
  · show (Evidence.srcsAB o || false) = Evidence.srcsAB o
    exact Bool.or_false _
  · show (Evidence.srcsA o || false) = Evidence.srcsA o
    exact Bool.or_false _

/-- `bob`'s delta is a genuine delivery at `emptyOpenW`: his candidate is
attributed to a source that is owed and uncertified, and it adds no obligation. -/
theorem deliverBob47_isDelivery : IsDelivery ResultStatus.emptyOpenW deliverBob47 := by
  constructor
  · rintro ⟨a, o⟩ h
    have hp : (a, o) = (47, Evidence.bob) := of_decide_eq_true h
    have ho : o = Evidence.bob := congrArg Prod.snd hp
    subst ho
    show Evidence.obligations ResultStatus.emptyOpenW Evidence.bob = true
      ∧ Evidence.certificates ResultStatus.emptyOpenW Evidence.bob = false
    exact ⟨by decide, by decide⟩
  · intro o h
    exact Bool.noConfusion h

/-- …and the pool is responsive. -/
theorem deliverBob47_responsive : Responsive ResultStatus.emptyOpenW [deliverBob47] :=
  ⟨deliverBob47, List.Mem.head _, 47, Evidence.bob, by decide, by decide, by decide⟩

/-- The one-round fair schedule: `bob`'s delta to both replicas. -/
def bobSched : List (Bool × Evidence.ResultEvidence Holes.Val) :=
  [(false, deliverBob47), (true, deliverBob47)]

theorem bobSched_fair :
    Liveness.FairOn (S := Evidence.ResultEvidence Holes.Val) [false, true]
      [deliverBob47] bobSched := by
  intro r hr δ
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl
  · show δ ∈ [deliverBob47] ↔ δ ∈ Liveness.received false bobSched
    rw [show Liveness.received (S := Evidence.ResultEvidence Holes.Val) false bobSched
      = [deliverBob47] from by simp [Liveness.received, bobSched]]
  · show δ ∈ [deliverBob47] ↔ δ ∈ Liveness.received true bobSched
    rw [show Liveness.received (S := Evidence.ResultEvidence Holes.Val) true bobSched
      = [deliverBob47] from by simp [Liveness.received, bobSched]]

/-- ⚠ **PROGRESS, ON A SCHEDULE.** The spinner at `emptyOpenW` is left by a fair
one-round delivery of a pool `bob` actually contributed to: both replicas reach
`bobSpokeW`, the status is `provisional 47`, and the state reached is a permitted
future. This is the theorem `pending_escapable` was standing in for, with the
environment supplied rather than assumed away. -/
theorem the_spinner_at_emptyOpenW_is_left_by_a_fair_schedule :
    Liveness.runDeliveries (fun _ => ResultStatus.emptyOpenW) bobSched false
        = ResultStatus.bobSpokeW
      ∧ Liveness.runDeliveries (fun _ => ResultStatus.emptyOpenW) bobSched true
        = ResultStatus.bobSpokeW
      ∧ statusOf ResultStatus.bobSpokeW = Status.provisional 47
      ∧ Evidence.SealedFuture ResultStatus.emptyOpenW ResultStatus.bobSpokeW
      ∧ statusOf (Liveness.runDeliveries (fun _ => ResultStatus.emptyOpenW) bobSched false)
          ≠ Status.pending := by
  have hconv := Liveness.fair_converges (S := Evidence.ResultEvidence Holes.Val)
    ResultStatus.emptyOpenW [deliverBob47] bobSched [false, true] bobSched_fair
  have hjoin : Delta.joinAll ResultStatus.emptyOpenW [deliverBob47] = ResultStatus.bobSpokeW :=
    emptyOpenW_merge_deliverBob47
  have hf := hconv false (by simp)
  have ht := hconv true (by simp)
  rw [hjoin] at hf ht
  refine ⟨hf, ht, RenderSix.statusOf_bobSpokeW, ResultStatus.emptyOpenW_seals_to_bobSpokeW, ?_⟩
  rw [hf, RenderSix.statusOf_bobSpokeW]
  exact provisional_ne_pending 47

/-! ### The second separation — a truthful spinner may wait forever

Codex: *a truthful UI may remain pending forever because a required peer never
returns — that is not an epistemic lie.* With an empty issued pool the
responsiveness premise fails, every fair schedule delivers nothing, and the
replica sits at `emptyOpenW` reporting `pending` — while `statusOf` remains
`PendingSound` and, by §1, still satisfies `pending_escapable`. -/

/-- **An unresponsive environment leaves a `PendingSound` spinner pending under
every fair schedule.** Fairness is satisfied vacuously by an empty pool, so
`Liveness.fair_converges` lands the replica exactly where it started. -/
theorem unresponsive_environment_keeps_pending {ι : Type} [DecidableEq ι]
    (sched : List (ι × Evidence.ResultEvidence Holes.Val)) (replicas : List ι) {r : ι}
    (hr : r ∈ replicas)
    (hfair : Liveness.FairOn (S := Evidence.ResultEvidence Holes.Val) replicas [] sched) :
    statusOf (Liveness.runDeliveries (fun _ => ResultStatus.emptyOpenW) sched r)
      = Status.pending := by
  rw [Liveness.fair_converges ResultStatus.emptyOpenW [] sched replicas hfair r hr]
  exact ResultStatus.statusOf_emptyOpenW

/-- ⚠ **THE SECOND SEPARATION — WAITING FOREVER IS NOT AN EPISTEMIC LIE.** All
four at once: `statusOf` is `PendingSound`; it satisfies the old clause (§1); it
says `pending` at `emptyOpenW`; and **every** fair schedule over an empty pool
leaves it `pending`.

So neither `PendingSound` nor `pending_escapable` bounds the wait, and neither
should: the failure is the peer's, not the renderer's. Only `PendingProgress`
speaks to it, and only under premises this witness shows can genuinely fail. -/
theorem a_truthful_spinner_may_wait_forever :
    PendingSound (S := Evidence.ResultEvidence Holes.Val) Evidence.values
        Evidence.Closed statusOf
      ∧ (∀ e : Evidence.ResultEvidence Holes.Val, statusOf e = Status.pending →
          ∃ t, Evidence.SealedFuture e t ∧ statusOf t ≠ Status.pending)
      ∧ statusOf ResultStatus.emptyOpenW = Status.pending
      ∧ (∀ (ι : Type) [DecidableEq ι] (sched : List (ι × Evidence.ResultEvidence Holes.Val))
          (replicas : List ι) (r : ι), r ∈ replicas →
          Liveness.FairOn (S := Evidence.ResultEvidence Holes.Val) replicas [] sched →
          statusOf (Liveness.runDeliveries (fun _ => ResultStatus.emptyOpenW) sched r)
            = Status.pending)
      ∧ ¬ Responsive ResultStatus.emptyOpenW [] := by
  refine ⟨statusOf_pendingSound, fun _ h => statusOf_pending_escapable_by_sealing h,
    ResultStatus.statusOf_emptyOpenW,
    fun _ _ sched replicas r hr hfair => unresponsive_environment_keeps_pending
      sched replicas hr hfair, ?_⟩
  rintro ⟨δ, hδ, _⟩
  exact absurd hδ (List.not_mem_nil)

/-! ## §4. `PendingActionable` — the UI affordance, with an authorization proof.

The third of the three. A spinner is *actionable* when the surface can offer a
discharge: a state the action produces, an actor who may press it, and a proof
that the actor's authority is live. `Authority.Active` is that proof — the
macaroon/biscuit chain of `Authority.lean`, unmodified — so the affordance is
tied to delegated authority rather than asserted.

The offer this file inhabits is the honest one available with no peer
cooperation at all: `sealAll`, "stop waiting on everyone". That is why §1's
give-up move belongs *here* rather than in the liveness clause — it is a real
button, and it needs a real actor. -/

/-- **A discharge offer at `e`**: what pressing the button produces, who may
press it, and why they may. -/
structure DischargeOffer {β : Type} (e : Evidence.ResultEvidence β) : Type where
  /-- The state the action produces. -/
  after : Evidence.ResultEvidence β
  /-- The grant the presser holds. -/
  actor : Authority.Grant
  /-- The delegation state the authority is read against. -/
  grants : Authority.GrantSet
  /-- The revocations in force. -/
  revoked : Authority.Revoked
  /-- **The authorization proof.** A live, unrevoked delegation chain to the
  root — `Authority.Active`, not a boolean anyone can set. -/
  authorized : Authority.Active grants revoked actor
  /-- The action stays inside the permitted future: it is a move the evidence
  algebra allows, not a rewrite of history. -/
  permitted : Evidence.SealedFuture e after
  /-- …and it actually ends the wait. -/
  discharges : statusOf after ≠ Status.pending

/-- **The affordance contract**: wherever the surface shows a spinner, a
discharge offer exists. -/
def PendingActionable {β : Type} (peval : Evidence.ResultEvidence β → Status β) : Prop :=
  ∀ e, peval e = Status.pending → Nonempty (DischargeOffer e)

/-- **The sanctioned renderer is actionable — relative to an actor.** Given any
live grant, every `pending` state carries the "stop waiting" offer: it produces
`sealAll e`, it is a permitted move (`sealed_sealAll`), and the badge it leaves
is `absent`.

The grant is a hypothesis because it has to be: an affordance with no authorized
actor is a button nobody may press, and the type says so. -/
theorem statusOf_pendingActionable {β : Type} {s : Authority.GrantSet}
    {rv : Authority.Revoked} {g : Authority.Grant} (hauth : Authority.Active s rv g) :
    PendingActionable (statusOf (α := β)) := fun e he =>
  ⟨{ after := sealAll e
     actor := g
     grants := s
     revoked := rv
     authorized := hauth
     permitted := sealed_sealAll e
     discharges := by
       rw [statusOf_sealAll_absent (values_of_statusOf_pending he).1]
       exact absent_ne_pending }⟩

/-- The affordance is inhabited at the deployed carrier: `Authority.lean`'s
two-link demo chain has a live delegate, and that delegate can discharge every
spinner `statusOf` shows. -/
theorem statusOf_pendingActionable_demo :
    PendingActionable (statusOf (α := Holes.Val)) :=
  statusOf_pendingActionable Authority.demo_delegate_active

/-- ⚠ **THE AUTHORIZATION FIELD IS LOAD-BEARING.** Revoke the *issuer* and the
delegate's chain dies (`Authority.demo_cascade_revoked`), so no discharge offer
at `emptyOpenW` can name that actor in that context — the structure cannot be
built. A surface that offers the button to a revoked actor is not expressible
here, which is the point of carrying the proof rather than a flag. -/
theorem a_revoked_actor_gets_no_button :
    ¬ ∃ o : DischargeOffer (β := Holes.Val) ResultStatus.emptyOpenW,
        o.grants = Authority.demoChain ∧ o.revoked = Authority.revokeIssuer
          ∧ o.actor = (2, 1, 4) := by
  rintro ⟨o, hg, hr, ha⟩
  have hact := o.authorized
  rw [hg, hr, ha] at hact
  exact Authority.demo_cascade_revoked hact

/-- ⚠ **THE THREE CONTRACTS, SIDE BY SIDE.** `statusOf` satisfies all three, and
each is refuted by a different witness, so none of them is the other wearing a
different name:

  * `PendingSound` — refuted by `spinnerRender` at one closed state;
  * `PendingProgress` — its premises can fail (`a_truthful_spinner_may_wait_
    forever`), and when they hold a scheduler really leaves `pending`;
  * `PendingActionable` — refuted for a revoked actor.

And the clause they replace, `pending_escapable`, is discharged by giving up
(§1), which is why it belonged to none of the three. -/
theorem the_three_contracts_are_distinct :
    PendingSound (S := Evidence.ResultEvidence Holes.Val) Evidence.values
        Evidence.Closed statusOf
      ∧ PendingProgress (β := Holes.Val) (ι := Bool) statusOf
      ∧ PendingActionable (statusOf (α := Holes.Val))
      ∧ ¬ PendingSound (S := Evidence.ResultEvidence Holes.Val) Evidence.values
          Evidence.Closed RenderSix.spinnerRender
      ∧ ¬ PendingSound (S := Evidence.ResultEvidence Holes.Val) Evidence.values
          Evidence.Closed unrelatedEscape
      ∧ ¬ ∃ o : DischargeOffer (β := Holes.Val) ResultStatus.emptyOpenW,
          o.grants = Authority.demoChain ∧ o.revoked = Authority.revokeIssuer
            ∧ o.actor = (2, 1, 4) :=
  ⟨statusOf_pendingSound, statusOf_pendingProgress, statusOf_pendingActionable_demo,
   spinnerRender_is_not_pendingSound, unrelatedEscape_is_not_pendingSound,
   a_revoked_actor_gets_no_button⟩

/-! ## §5. THE ABSENCE SLOGAN, CORRECTED BY A WITNESS.

`RenderSix.absence_is_the_more_defensible_badge` is a true theorem with an
overstated headline. The precise statement is:

> **closed emptiness is merge-closed in this evidence algebra; unrestricted
> singleton determinacy is not.**

The correction is not a hedge, because some exact values *are* merge-stable, and
this section exhibits three of them. -/

/-- The value axis distributes over merge: a value in the merge came from one
side. -/
theorem values_merge {β : Type} (e₁ e₂ : Evidence.ResultEvidence β) (a : β) :
    Evidence.values (e₁ ⊔ e₂) a = true
      ↔ Evidence.values e₁ a = true ∨ Evidence.values e₂ a = true := by
  constructor
  · intro h
    obtain ⟨o, ho⟩ := (Evidence.mem_values _ a).mp h
    rcases (Bool.or_eq_true _ _).mp
      (show (Evidence.candidates e₁ (a, o) || Evidence.candidates e₂ (a, o)) = true from ho)
      with h1 | h1
    · exact Or.inl ((Evidence.mem_values e₁ a).mpr ⟨o, h1⟩)
    · exact Or.inr ((Evidence.mem_values e₂ a).mpr ⟨o, h1⟩)
  · rintro (h | h)
    · obtain ⟨o, ho⟩ := (Evidence.mem_values e₁ a).mp h
      refine (Evidence.mem_values _ a).mpr ⟨o, ?_⟩
      show (Evidence.candidates e₁ (a, o) || Evidence.candidates e₂ (a, o)) = true
      rw [ho]
      rfl
    · obtain ⟨o, ho⟩ := (Evidence.mem_values e₂ a).mp h
      refine (Evidence.mem_values _ a).mpr ⟨o, ?_⟩
      show (Evidence.candidates e₁ (a, o) || Evidence.candidates e₂ (a, o)) = true
      rw [ho]
      exact Bool.or_true _

/-- ⚠ **AN EXACT BADGE THAT IS MERGE-SAFE — AND UNILATERALLY.** For a grow-only
existential, `anyCandidate p = true` is the **exact** answer to "did anyone say
`p`?", and one replica holding it is enough: merging with an arbitrary peer
cannot retract it.

This is `ResultStatus.anyCandidate_true_is_self_certifying`'s content on the
merge axis rather than the future axis, and it is the counterexample the slogan
needed: exactness is not what fails at merge. -/
theorem anyCandidate_true_merges {β : Type} (p : β → Bool)
    (e₁ e₂ : Evidence.ResultEvidence β) (h : ResultStatus.anyCandidate p e₁ = true) :
    ResultStatus.anyCandidate p (e₁ ⊔ e₂) = true := by
  obtain ⟨a, ha, hp⟩ := Holes.truth_eq_true.mp h
  exact Holes.truth_eq_true.mpr ⟨a, (values_merge e₁ e₂ a).mpr (Or.inl ha), hp⟩

/-- …stated as the library's coordination judgement. -/
theorem anyCandidate_true_iconfluent {β : Type} (p : β → Bool) :
    IConfluent (S := Evidence.ResultEvidence β)
      (fun e => ResultStatus.anyCandidate p e = true) :=
  fun x y hx _ => anyCandidate_true_merges p x y hx

/-- ⚠ **AGREEING EXACT VALUES DO NOT FORK.** Two replicas that each report
`exact v` — the **same** `v` — merge to `exact v`. The merge's candidate set is
the union of two sets both sealed to `v`, and closure is I-confluent. So the
`exact` badge survives sync whenever the replicas agree; what
`RenderSix.statusOf_merge_of_two_exacts` refutes is disagreement, not
exactness. -/
theorem statusOf_exact_agree_merges {β : Type} {e₁ e₂ : Evidence.ResultEvidence β} {v : β}
    (h1 : statusOf e₁ = Status.exact v) (h2 : statusOf e₂ = Status.exact v) :
    statusOf (e₁ ⊔ e₂) = Status.exact v := by
  obtain ⟨hm1, hs1, hc1⟩ := values_of_statusOf_exact h1
  obtain ⟨_, hs2, hc2⟩ := values_of_statusOf_exact h2
  refine ResultStatus.statusOf_exact ((values_merge e₁ e₂ v).mpr (Or.inl hm1)) (fun b hb => ?_)
    (Evidence.closed_iconfluent _ _ hc1 hc2)
  rcases (values_merge e₁ e₂ b).mp hb with h | h
  · exact hs1 b h
  · exact hs2 b h

/-- **An exact result in a selection lattice stays exact by construction.**
`Catalog.selection_iconfluent` instantiated: an LWW register's merge *selects*
one of its arguments, so "the value is exactly `v`" is I-confluent for every
`v` — no agreement argument needed, the lattice does it. -/
theorem lww_exact_is_merge_safe (v : Nat) :
    IConfluent (S := Catalog.LWW) (fun r => r.val = v) :=
  Catalog.lww_every_invariant_iconfluent _

/-- The merge of definitive absence with an exact replica. -/
theorem statusOf_emptyClosedW_merge_exactW :
    statusOf (ResultStatus.emptyClosedW ⊔ Evidence.exactW) = Status.exact 47 := by
  refine ResultStatus.statusOf_exact
    ((values_merge _ _ 47).mpr (Or.inr (Evidence.values_cand47 (e := Evidence.exactW) rfl).1))
    (fun b hb => ?_)
    (Evidence.closed_iconfluent _ _ ResultStatus.closed_emptyClosedW Evidence.closed_exactW)
  rcases (values_merge _ _ b).mp hb with h | h
  · rw [ResultStatus.values_candNone (e := ResultStatus.emptyClosedW) rfl b] at h
    exact Bool.noConfusion h
  · exact (Evidence.values_cand47 (e := Evidence.exactW) rfl).2 b h

/-- ⚠ **ABSENCE IS NOT UNILATERALLY MERGE-CLOSED.** `RenderSix.absent_iconfluent`
needs **both** replicas to report definitive absence. Merge one that does with
one that holds an exact answer and the absence is gone — correctly, because it
was never true globally.

Set against `anyCandidate_true_merges`, which needs **one** replica: on the merge
axis the existential's exact badge is *stronger* than absence, not weaker. The
slogan had the ordering backwards as well as the subject. -/
theorem absence_is_not_unilaterally_merge_closed :
    statusOf ResultStatus.emptyClosedW = Status.absent
      ∧ statusOf (ResultStatus.emptyClosedW ⊔ Evidence.exactW) = Status.exact 47
      ∧ statusOf (ResultStatus.emptyClosedW ⊔ Evidence.exactW) ≠ Status.absent := by
  refine ⟨ResultStatus.statusOf_emptyClosedW, statusOf_emptyClosedW_merge_exactW, ?_⟩
  rw [statusOf_emptyClosedW_merge_exactW]
  exact ResultStatus.status_ne_of_tag (by simp [ResultStatus.statusTag])

/-- ⚠ **THE CORRECTED SLOGAN, AS A WITNESS RATHER THAN A HEDGE.** Six clauses:

  * closed emptiness is merge-closed — **bilaterally** (`RenderSix.absent_
    iconfluent`);
  * a grow-only existential's exact `true` is merge-closed — **unilaterally**;
  * agreeing canonical exact values do not fork;
  * a selection lattice keeps exactness by construction;
  * what actually fails is **arbitrary** singleton determinacy: `exactW ⊔
    exact49W` is a closed fork;
  * and that failure is a **uniqueness ceiling** — the same shape as
    `Catalog.gset_atMostOne_not_iconfluent`, which is where every "at most one"
    on a grow-only structure lands.

So "absence is the more defensible badge" is replaced by: *closed emptiness is
merge-closed in this evidence algebra; unrestricted singleton determinacy is
not.* Both halves are theorems, and the exact badges above are why the first
sentence needed the qualifier. -/
theorem closed_emptiness_merges_arbitrary_determinacy_does_not :
    (∀ e₁ e₂ : Evidence.ResultEvidence Holes.Val, statusOf e₁ = Status.absent →
        statusOf e₂ = Status.absent → statusOf (e₁ ⊔ e₂) = Status.absent)
      ∧ (∀ (p : Holes.Val → Bool) (e₁ e₂ : Evidence.ResultEvidence Holes.Val),
          ResultStatus.anyCandidate p e₁ = true →
          ResultStatus.anyCandidate p (e₁ ⊔ e₂) = true)
      ∧ (∀ (e₁ e₂ : Evidence.ResultEvidence Holes.Val) (v : Holes.Val),
          statusOf e₁ = Status.exact v → statusOf e₂ = Status.exact v →
          statusOf (e₁ ⊔ e₂) = Status.exact v)
      ∧ (∀ v : Nat, IConfluent (S := Catalog.LWW) (fun r => r.val = v))
      ∧ statusOf (Evidence.exactW ⊔ RenderSix.exact49W) = Status.forkedClosed
      ∧ ¬ IConfluent (S := GSet Nat)
          (fun s => ∀ m n, s m = true → s n = true → m = n) :=
  ⟨fun _ _ h1 h2 => RenderSix.absent_iconfluent h1 h2,
   fun p e₁ e₂ h => anyCandidate_true_merges p e₁ e₂ h,
   fun _ _ _ h1 h2 => statusOf_exact_agree_merges h1 h2,
   lww_exact_is_merge_safe,
   RenderSix.statusOf_merge_of_two_exacts,
   Catalog.gset_atMostOne_not_iconfluent⟩

/-! ## §6. SCOPE — "no results in epoch A" is not "no results".

A `Source` is a peer, an epoch, a frontier point (`Evidence.lean` §1 says so).
So "no results in epoch A" is `AbsentOn A e`, and the composition question is
whether two scoped absences make an unscoped one.

The verdict is two-sided and both sides are proved: scoped absence **composes to
the union scope** unconditionally, and reaches unscoped absence **only** when the
scopes cover the obligations and the attributions. Without coverage there is a
witness whose global status is `pending`. -/

/-- **Definitive absence within a scope**: no candidate is attributed to any
source in `A`, and every source in `A` that is owed carries a certificate. -/
def AbsentOn {β : Type} (A : GSet Evidence.Source) (e : Evidence.ResultEvidence β) : Prop :=
  (∀ (a : β) (o : Evidence.Source), A o = true → Evidence.candidates e (a, o) = false)
    ∧ (∀ o, A o = true → Evidence.obligations e o = true → Evidence.certificates e o = true)

/-- **Scoped absence composes to the union scope.** Two epochs each definitively
empty are jointly definitively empty over both — this half of the composition is
sound, and it is the half people mean. -/
theorem absentOn_union {β : Type} {A B : GSet Evidence.Source}
    {e : Evidence.ResultEvidence β} (hA : AbsentOn A e) (hB : AbsentOn B e) :
    AbsentOn (A ⊔ B) e := by
  constructor
  · intro a o ho
    rcases (Bool.or_eq_true _ _).mp (show (A o || B o) = true from ho) with h | h
    · exact hA.1 a o h
    · exact hB.1 a o h
  · intro o ho hobl
    rcases (Bool.or_eq_true _ _).mp (show (A o || B o) = true from ho) with h | h
    · exact hA.2 o h hobl
    · exact hB.2 o h hobl

/-- **Scoped absence reaches unscoped absence exactly under coverage.** If the
scope contains every source still owed **and** every source any candidate is
attributed to, the scoped verdict is the global one. The two coverage premises
are the content: without them the scope is a window, not a verdict. -/
theorem absentOn_covering_is_global {β : Type} {A : GSet Evidence.Source}
    {e : Evidence.ResultEvidence β} (h : AbsentOn A e)
    (hcov : ∀ o, Evidence.obligations e o = true → A o = true)
    (hattr : ∀ (a : β) (o : Evidence.Source), Evidence.candidates e (a, o) = true → A o = true) :
    statusOf e = Status.absent := by
  refine ResultStatus.statusOf_absent (fun a => ?_) (fun o ho => h.2 o (hcov o ho) ho)
  cases hb : Evidence.values e a with
  | false => rfl
  | true =>
    obtain ⟨o, ho⟩ := (Evidence.mem_values e a).mp hb
    exact absurd ((h.1 a o (hattr a o ho)).symm.trans ho) Bool.noConfusion

/-- The scope "epoch alice". -/
def scopeAlice : GSet Evidence.Source := fun o => decide (o = Evidence.alice)

/-- The scope "epoch carol" — a source `emptyOpenW` never expected. -/
def scopeCarol : GSet Evidence.Source := fun o => decide (o = Evidence.carol)

theorem absentOn_scopeAlice : AbsentOn scopeAlice ResultStatus.emptyOpenW := by
  constructor
  · intro _ _ _
    rfl
  · intro o ho _
    rw [of_decide_eq_true ho]
    decide

theorem absentOn_scopeCarol : AbsentOn scopeCarol ResultStatus.emptyOpenW := by
  constructor
  · intro _ _ _
    rfl
  · intro o ho hobl
    rw [of_decide_eq_true ho] at hobl
    exact absurd hobl (by decide)

/-- ⚠ **THE SCOPED-ABSENCE VERDICT.** "No results in epoch alice" and "no results
in epoch carol" both hold at `emptyOpenW`; they compose to the union scope; and
the unscoped status is **`pending`**, not `absent` — because `bob` is owed and
neither scope covers him.

So the composition is *sound to the union scope* and *unsound to the global
one*, and the failing premise is named: coverage of the obligations. This is the
scope discipline `absentOn_covering_is_global` demands, refuted here for the
case where it is dropped. -/
theorem scoped_absence_does_not_reach_global :
    AbsentOn scopeAlice ResultStatus.emptyOpenW
      ∧ AbsentOn scopeCarol ResultStatus.emptyOpenW
      ∧ AbsentOn (scopeAlice ⊔ scopeCarol) ResultStatus.emptyOpenW
      ∧ statusOf ResultStatus.emptyOpenW = Status.pending
      ∧ statusOf ResultStatus.emptyOpenW ≠ Status.absent
      ∧ ¬ (∀ o, Evidence.obligations ResultStatus.emptyOpenW o = true →
            (scopeAlice ⊔ scopeCarol) o = true) := by
  refine ⟨absentOn_scopeAlice, absentOn_scopeCarol,
    absentOn_union absentOn_scopeAlice absentOn_scopeCarol,
    ResultStatus.statusOf_emptyOpenW, ?_, ?_⟩
  · rw [ResultStatus.statusOf_emptyOpenW]
    exact fun h => absent_ne_pending h.symm
  · intro h
    exact absurd (h Evidence.bob (by decide)) (by decide)

/-! ## §7. THE SEMANTIC WIDGET — what an interface can exclude that salience cannot.

`RenderSix.salience_is_not_enforceable6` is the honest limit of a renderer whose
output type is arbitrary: six handlers may all return the same `β`, so no
interface over `β` can force the spinner to look different from "no results".

Codex's correction is that the *loading-forever* bug can be constrained further,
because it is not a salience claim — it is a **semantic** one. Interpose a
contract the renderer must produce before it paints anything, pin `finality` at
the two zero-candidate cells, and a dishonest `loading = true` at `absent` stops
being expressible. The final visual map may still make both one grey pixel; it
may no longer *say* the result is still coming. -/

/-- Whether this cell can still change. Codex's `open` — the constructor carries
a prime because `open` is a Lean keyword. -/
inductive Finality where
  /-- The evidence is settled: no permitted future changes this cell. -/
  | terminal
  /-- The evidence is open: something is still owed. -/
  | open'
  deriving DecidableEq, Repr

/-- How many candidates the cell holds. -/
inductive Plurality where
  /-- No candidate. -/
  | zero
  /-- Exactly one. -/
  | one
  /-- Several — a fork. -/
  | many
  deriving DecidableEq, Repr

/-- A discharge a surface may offer at a cell. -/
inductive Action where
  /-- Wait for a source still owed to contribute. -/
  | awaitDelivery
  /-- Give up on the sources still owed (§1's `sealAll`, as a button). -/
  | stopWaiting
  /-- Pick among forked candidates (`ResultStatus.Policy`). -/
  | resolveFork
  deriving DecidableEq, Repr

/-- What the cell shows for candidates. -/
inductive CandidatePresentation (α : Type) where
  /-- Nothing to show. -/
  | nothing
  /-- One value. -/
  | single (a : α)
  /-- Several values. -/
  | several

/-- **The intermediate contract.** A renderer may not go straight from a status
to an arbitrary `β`; it must first produce this, and the two `HonestWidget`
clauses constrain it. -/
structure SemanticWidget (α : Type) where
  /-- Whether the cell can still change. -/
  finality : Finality
  /-- How many candidates it holds. -/
  plurality : Plurality
  /-- The discharge the surface offers here, if any. -/
  pendingAction : Option Action
  /-- What it shows for candidates. -/
  candidates : CandidatePresentation α

/-- The sanctioned widget assignment, one per status. -/
def widgetOf {α : Type} : Status α → SemanticWidget α
  | .exact a => ⟨.terminal, .one, none, .single a⟩
  | .provisional a => ⟨.open', .one, some .awaitDelivery, .single a⟩
  | .forkedClosed => ⟨.terminal, .many, some .resolveFork, .several⟩
  | .forkedOpen => ⟨.open', .many, some .awaitDelivery, .several⟩
  | .absent => ⟨.terminal, .zero, none, .nothing⟩
  | .pending => ⟨.open', .zero, some .stopWaiting, .nothing⟩

/-- **The interface obligation.** The two clauses codex names, plus the plurality
of the zero row and the absence of a button at a terminal cell. -/
structure HonestWidget {α : Type} (w : Status α → SemanticWidget α) : Prop where
  /-- `absent → finality = terminal`. -/
  absent_terminal : (w Status.absent).finality = Finality.terminal
  /-- `pending → finality = open`. -/
  pending_open : (w Status.pending).finality = Finality.open'
  /-- A definitively absent cell offers nothing to wait for. -/
  absent_no_button : (w Status.absent).pendingAction = none
  /-- Both zero-candidate cells hold no candidate. -/
  absent_zero : (w Status.absent).plurality = Plurality.zero
  /-- …including the spinner. -/
  pending_zero : (w Status.pending).plurality = Plurality.zero

/-- The sanctioned assignment satisfies the interface. -/
theorem widgetOf_honest {α : Type} : HonestWidget (widgetOf (α := α)) where
  absent_terminal := rfl
  pending_open := rfl
  absent_no_button := rfl
  absent_zero := rfl
  pending_zero := rfl

/-- **What "loading" means at the interface**: the widget claims the cell is
still open. Everything a spinner asserts is this bit. -/
def loading {α : Type} (w : SemanticWidget α) : Bool :=
  match w.finality with
  | .terminal => false
  | .open' => true

/-- ⚠ **A DISHONEST `loading` IS EXCLUDED.** No assignment satisfying the
interface can advertise `loading = true` at `absent`. This is the "loading
forever on an empty result" bug, refuted at the type rather than at a future. -/
theorem no_honest_widget_loads_at_absent {α : Type} {w : Status α → SemanticWidget α}
    (h : HonestWidget w) : loading (w Status.absent) = false := by
  unfold loading
  rw [h.absent_terminal]

/-- …and the spinner cell does load, so the bit is not constantly `false`. -/
theorem honest_widget_loads_at_pending {α : Type} {w : Status α → SemanticWidget α}
    (h : HonestWidget w) : loading (w Status.pending) = true := by
  unfold loading
  rw [h.pending_open]

/-- ⚠ **CONSTANT WIDGETS ARE EXCLUDED — AND THIS IS WHAT SALIENCE COULD NOT DO.**
`RenderSix.salience_is_not_enforceable6` says a consumer into an arbitrary `β`
may return the same value at all six statuses. A consumer into `SemanticWidget`
may not: one value cannot have `finality = terminal` and `finality = open'`. The
intermediate contract is strictly more than the salience limit gives. -/
theorem constant_widget_is_not_honest {α : Type} (v : SemanticWidget α) :
    ¬ HonestWidget (fun _ : Status α => v) := by
  intro h
  have h1 : v.finality = Finality.terminal := h.absent_terminal
  have h2 : v.finality = Finality.open' := h.pending_open
  rw [h1] at h2
  exact Finality.noConfusion h2

/-! ### The interface at the evidence carrier -/

/-- **A widget-sound surface**: it reads the evidence and its finality agrees
with `statusOf` at the two zero-candidate cells. -/
def WidgetSound {β : Type} (wf : Evidence.ResultEvidence β → SemanticWidget β) : Prop :=
  (∀ e, statusOf e = Status.absent → (wf e).finality = Finality.terminal)
    ∧ (∀ e, statusOf e = Status.pending → (wf e).finality = Finality.open')

/-- The sanctioned renderer, widgetized, is widget-sound. -/
theorem sanctioned_widget_is_sound {β : Type} :
    WidgetSound (fun e => widgetOf (statusOf (α := β) e)) := by
  constructor
  · intro e h
    show (widgetOf (statusOf e)).finality = Finality.terminal
    rw [h]
    rfl
  · intro e h
    show (widgetOf (statusOf e)).finality = Finality.open'
    rw [h]
    rfl

/-- ⚠ **THE SPINNER IS EXCLUDED BY THE INTERFACE, AT ONE STATE.** `spinnerRender`
badges `emptyClosedW` — definitively absent — as `pending`, so its widget claims
`open'` where the interface requires `terminal`. `RenderSix.spinnerRender_is_not_
sound6` needed a statement about every sealed future; this needs the one
state. -/
theorem spinner_widget_is_not_sound :
    ¬ WidgetSound (β := Holes.Val) (fun e => widgetOf (RenderSix.spinnerRender e)) := by
  intro h
  have hx : (widgetOf (RenderSix.spinnerRender ResultStatus.emptyClosedW)).finality
      = Finality.terminal :=
    h.1 ResultStatus.emptyClosedW ResultStatus.statusOf_emptyClosedW
  rw [RenderSix.spinnerRender_emptyClosedW] at hx
  exact Finality.noConfusion hx

/-- **…and therefore it cannot truthfully advertise `loading`.** Any widget-sound
surface returns `loading = false` at every definitively absent evidence. -/
theorem widget_sound_surface_cannot_load_at_absent {β : Type}
    {wf : Evidence.ResultEvidence β → SemanticWidget β} (h : WidgetSound wf)
    {e : Evidence.ResultEvidence β} (he : statusOf e = Status.absent) :
    loading (wf e) = false := by
  unfold loading
  rw [h.1 e he]

/-- ⚠ **SALIENCE SURVIVES — SAY IT PLAINLY.** The interface constrains the
*semantic* layer only. The last hop, `SemanticWidget α → β`, is still a function
into an arbitrary type, and constant functions still exist: six statuses, six
distinct widgets, one grey pixel. No interface reaches past its own output type,
and this one does not either. -/
theorem salience_is_still_not_enforceable_after_the_widget {α β : Type} (b : β)
    (w : Status α → SemanticWidget α) (st : Status α) :
    (fun _ : SemanticWidget α => b) (w st) = b := rfl

/-- ⚠ **THE WIDGET BITES WHERE SALIENCE DOES NOT.** Five clauses, and the
contrast is the middle two:

  * salience is unenforceable at the six-handler carrier — a consumer into an
    arbitrary `β` may be constant (`RenderSix.salience_is_not_enforceable6`);
  * a consumer into `SemanticWidget` may **not** be constant;
  * and no honest assignment loads at `absent`;
  * the sanctioned renderer's widget is sound, and the spinner's is not;
  * yet the final paint may still collapse all six to one value — the limit that
    survives, stated rather than omitted. -/
theorem the_widget_excludes_what_salience_cannot :
    (∀ (β : Type) (C : RenderSix.Carrier6 (Evidence.SealedFuture (α := Holes.Val)) Holes.Val)
        (b : β) (r : C.R), C.elim r (fun _ => b) (fun _ => b) b b b b = b)
      ∧ (∀ v : SemanticWidget Holes.Val, ¬ HonestWidget (fun _ : Status Holes.Val => v))
      ∧ (∀ w : Status Holes.Val → SemanticWidget Holes.Val, HonestWidget w →
          loading (w Status.absent) = false)
      ∧ WidgetSound (fun e => widgetOf (statusOf (α := Holes.Val) e))
      ∧ ¬ WidgetSound (β := Holes.Val) (fun e => widgetOf (RenderSix.spinnerRender e))
      ∧ (∀ (β : Type) (b : β) (st : Status Holes.Val),
          (fun _ : SemanticWidget Holes.Val => b) (widgetOf st) = b) :=
  ⟨fun _ C b r => RenderSix.salience_is_not_enforceable6 C b r,
   constant_widget_is_not_honest,
   fun _ h => no_honest_widget_loads_at_absent h,
   sanctioned_widget_is_sound,
   spinner_widget_is_not_sound,
   fun _ _ _ => rfl⟩

end Uwueave.RenderProgress
