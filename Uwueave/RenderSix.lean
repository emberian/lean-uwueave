/-
# Uwueave.RenderSix — the honest-render guarantees at SIX statuses, and the
limit `HonestRender.lean` named against itself, retired with a witness.

Two files were built in parallel and never met. `HonestRender.lean` proves the
render-boundary guarantees over an **abstract** five-handler carrier and then
names its own ceiling in its honest boundary:

> **The eliminator is five-way, and the sixth cell is a sibling's.**
> ⟨HISTORICAL LIMIT, DISCHARGED HERE⟩ …
> So a consumer of this carrier handles five statuses, not six, and a surface
> built on it **cannot tell a spinner from "there is no answer"**. The repair is
> a `Carrier` over `ResultStatus.Status` with a soundness contract proved for
> `statusOf`; **neither exists**, and nothing below pretends the fold is
> faithful.

`ResultStatus.lean` proves, independently, that the folded-away cell is real
(`sixth_cell_is_distinguishable`) and that its two halves have **opposite
finality**. This file is the repair the first file specified, built out of the
second file's material. Both exist here: `Carrier6` (§1) is the carrier,
`statusOf_sound6` (§3) is the soundness contract.

Nothing in `HonestRender.lean` or `Evidence.lean` is edited, restated or
rivalled. `StabilityCert` and `IsTheAnswer` are **imported
from `HonestRender`** and used verbatim, so §3's theorems are about that file's
notions and not about look-alikes; `statusOf`, `forget` and the six `statusOf_*`
lemmas are `ResultStatus`'s; the relation between the two dispatches is a
theorem (`dispatch6_collapses`), not a coincidence of shape.

## The four results worth reading

**§4 — THE LIMIT IS RETIRED, AND THE WITNESS IS SHARPER THAN EXPECTED.**
`five_handlers_cannot_separate`: at the two zero-candidate evidences **every**
five-handler consumer, at **every** display type, returns the same value —
the fold leaves it nothing to read. `six_carrier_separates`: the sanctioned
six-status renderer's two reports are told apart by a consumer that differs in
one handler. That is the spinner and the "no answer", distinguished.

**§5 — THE SIXTH-CELL DISHONESTY IS INVISIBLE TO THE FIVE-STATUS PREDICATE.**
`spinnerRender` shows a spinner where the answer is definitively absent — "loading
forever on an empty result", the bug every app has. `giveUpRender` shows "no
results" while data is still owed. Both are refuted by §3's contract
(`spinnerRender_is_not_sound6`, `giveUpRender_is_not_sound6`), and — the point —
**both fold to `Evidence.render` exactly**, so `HonestRender.HonestRenderer` is
*satisfied* by the spinner (`spinner_is_an_honest_five_status_renderer`). The
five-status honesty predicate certifies a renderer that spins forever on an
empty result. `six_is_strictly_stronger_than_five` states the containment and
its strictness in one place.

**§6 — IS `absent` MORE DEFENSIBLE THAN `exact`? YES, BUT NOT ON THE AXIS THE
QUESTION SUGGESTS.** `ResultStatus.absence_outlives_exactness` measures
`Evidence.render` and finds absence the most stable of the six. At `statusOf`
that gap **vanishes**: `absence_and_exactness_are_symmetric_under_every_future`
proves both contents are frozen under the *full extension* future, both badges
are retracted by a roster growth, and both badges are final under the sealed
future. `the_stability_gap_was_the_fold` puts the four measurements side by
side: the extra stability absence appeared to enjoy **was the fold's blindness**
— the very indistinguishability §4 removes. ⚠ So splitting the cell *costs* the
stability the fold gave away for free, and that is stated as a theorem rather
than omitted.

The asymmetry that does survive is on the **merge** axis, and it is stronger
than the one asked for: `absence_is_the_more_defensible_badge` proves
`absent` is I-confluent — two replicas that each report definitive absence merge
to a replica that reports definitive absence, coordination-free — while two
replicas each reporting `exact` merge to a **closed fork** (`exactW ⊔ exact49W`).
For a local-first UI that is the operative sense of "defensible": it is what
happens when two peers sync, and it is `Evidence.closed_iconfluent` meeting
`Holes.determinacy_not_iconfluent` at the render boundary.

**§7 — the six handlers are reached by real evidence.**
`HonestRender.every_status_slot_is_load_bearing` quantifies over `C.report s v`
for an arbitrary `v` — reports nobody claims a sound renderer ever makes.
`the_six_handlers_are_reached_by_real_evidence` pins all six to reports the
sanctioned renderer *does* make, at six named pieces of evidence.

## Honest boundary

⟨TERMINAL⟩ marks a theorem of the model; the other labels state their
precise scope or disposition without turning an honest caveat into hidden work.

  * **The split costs the badge's extension-finality at the zero row.** ⟨TERMINAL⟩
    `statusOf_not_extension_final_at_emptyClosedW`. A six-status surface must
    re-render "no results" as "loading" when a source nobody had heard of is
    admitted; the five-status surface did not flicker, because it could not see
    the difference. This is not repairable by a better carrier — it is
    `Evidence.render_retracts_when_a_new_source_appears` reaching the row it
    always applied to, and `SealedFuture` is where both rows are final.
  * **`pending_escapable` is the weakest honest liveness.**
    ⟨UNDONE U-0120 as temporal/all-path liveness⟩ It says *some* permitted future is
    not `pending`, not that every path leaves it and not that any path is taken.
    `RenderProgress.pending_progress_under_fair_delivery` now proves that a
    finite fair schedule of genuine deliveries reaches a non-pending status
    under its responsiveness premise. That theorem does not supply an infinite
    trace semantics, prove that every execution is fair, or turn this existential
    future property into temporal eventuality; those stronger claims remain open.
  * **`pending_escapable` needs an inhabitant of the value type.** ⟨TERMINAL⟩
    `statusOf_pending_escapable` takes an `a₀ : α`, because the only thing that
    stops a spinner is a value arriving. Over an empty value type `pending` is
    genuinely unescapable and the clause is genuinely false of `statusOf` —
    correctly, since nothing can ever arrive.
  * **Salience is still not enforceable.** ⟨TERMINAL⟩ `salience_is_not_enforceable6`
    is `HonestRender`'s theorem with a sixth constant handler. Six branches do
    not make six pixels differ, and no interface reaches that.
  * **`report` is public here too.** ⟨TERMINAL for this file's question⟩ A
    renderer must be able to say `absent`, including one that should not — which
    is exactly what makes §5 exhibitable.
  * **The original contract constrains three cells; its total extension is
    shipped.** ⟨HISTORICAL LIMIT, DISCHARGED BY `StatusEffects`⟩
    `SoundEvaluator6` deliberately remains the compatibility contract for
    `exact`, `absent` and escapability at `pending`.
    `StatusEffects.TotalSoundEvaluator6` supplies complete candidate and
    settledness semantics for all six cells; `semanticsAt` exposes the uniform
    `Status.Semantics` row, while `toSoundEvaluator6` projects back to this API.
    The boundary is load-bearing: the acceptance fixture's pending-with-a-
    candidate evaluator satisfies this compatibility contract and is rejected
    by the total one.
  * **Noncomputability is inherited.** ⟨TERMINAL at this carrier⟩ `statusOf`,
    `spinnerRender` and `giveUpRender` all quantify over an unbounded value type.
    `Classical.choice` is inside the audit floor.
  * **The checked adapter binds the six-way report site to the evaluated state.**
    ⟨DONE downstream in `Uwueave.Preo.ResultProgram`⟩ `CheckedReport.site_exact`
    proves the carrier site is the evaluated state, `refuses_wrong_site`
    rejects a contradictory claim, and `ObservedReport` retains an explicit
    `ObservationBoundary.Authentic` witness. Whether a deployment can supply
    that witness is stated once at that boundary rather than duplicated here.
-/
import Uwueave.HonestRender

namespace Uwueave.RenderSix

open Uwueave Uwueave.Catalog
open Uwueave.ResultStatus (Status statusOf)

/-! ## §1. The six-handler dispatch, and the carrier it pins.

`dispatch6` is `HonestRender.dispatch` with the zero-candidate row split: six
handlers, one per `ResultStatus.Status` constructor, and no default case to
write. `dispatch6_collapses` is the exact relation between the two: give the
same handler to `absent` and `pending` and you have written the five-handler
dispatch, composed with `ResultStatus.forget`. So the five-status interface is
not a different design — it is this one with the zero row collapsed, and the
collapse is the fold that §4 refutes. -/

/-- **The six-handler dispatch.** One handler per `ResultStatus.Status`
constructor. -/
def dispatch6 {α β : Type} (onExact onProvisional : α → β)
    (onForkedClosed onForkedOpen onAbsent onPending : β) : Status α → β
  | .exact a => onExact a
  | .provisional a => onProvisional a
  | .forkedClosed => onForkedClosed
  | .forkedOpen => onForkedOpen
  | .absent => onAbsent
  | .pending => onPending

/-- **The five-handler dispatch IS this one with the zero row collapsed.** Supply
one handler for both zero-candidate statuses and `dispatch6` is
`HonestRender.dispatch` after `ResultStatus.forget`. This is the precise sense in
which the sibling file's interface is a quotient of this one. -/
theorem dispatch6_collapses {α β : Type} (onE onP : α → β) (onFC onFO onV : β)
    (st : Status α) :
    dispatch6 onE onP onFC onFO onV onV st
      = HonestRender.dispatch onE onP onFC onFO onV (ResultStatus.forget st) := by
  cases st <;> rfl

/-- **A six-status result carrier for the future `F`.** `HonestRender.Carrier`
with `Evidence.View` replaced by `ResultStatus.Status`: a type of results, a
report constructor, the site a report was made at, the specification relation
`Says`, and a total **six**-handler eliminator pinned to `dispatch6` by
`elim_spec`.

As there, a consumer holding only a `Carrier6` has no constructor to match on,
because the interface exposes none — quantification, not `private`. -/
structure Carrier6 {S : Type} (F : Evidence.Future S) (α : Type) : Type 1 where
  /-- The type of results. -/
  R : Type
  /-- Make a report of a status at a site. Public: a renderer must be able to
  speak, including dishonestly (§5). -/
  report : S → Status α → R
  /-- The situation the report was made at. -/
  site : R → S
  /-- The specification: which status this result carries. -/
  Says : R → Status α → Prop
  /-- **The total eliminator.** Six handlers, one per status. -/
  elim : {β : Type} → R → (α → β) → (α → β) → β → β → β → β → β
  /-- A report is made at the site it was given. -/
  site_report : ∀ s v, site (report s v) = s
  /-- A report says the status it was made with. -/
  says_report : ∀ s v, Says (report s v) v
  /-- A result says at most one status. -/
  says_functional : ∀ r v v', Says r v → Says r v' → v = v'
  /-- A result says at least one status. -/
  says_total : ∀ r, ∃ v, Says r v
  /-- **The eliminator IS the six-way dispatch.** No default branch is
  expressible, because there is no behaviour left for one to have. -/
  elim_spec : ∀ {β : Type} (r : R) (v : Status α) (onE onP : α → β)
    (onFC onFO onA onPd : β), Says r v →
    elim r onE onP onFC onFO onA onPd = dispatch6 onE onP onFC onFO onA onPd v

/-- **The reference six-status result type.** A site and a status, with the
status `private` so no *other* module can project it. As in the sibling file the
module boundary is hygiene; `no_honest_projection6` is the enforcement. -/
structure Result6 {S : Type} (F : Evidence.Future S) (α : Type) : Type where
  private ofParts ::
  /-- The situation this report was made at. -/
  site : S
  private status : Status α

/-- **The six-status interface is inhabited**, so nothing stated over `Carrier6`
is a fact about an empty class. -/
def stdCarrier6 {S : Type} (F : Evidence.Future S) (α : Type) : Carrier6 F α where
  R := Result6 F α
  report := fun s v => Result6.ofParts s v
  site := Result6.site
  Says := fun r v => r.status = v
  elim := fun r onE onP onFC onFO onA onPd => dispatch6 onE onP onFC onFO onA onPd r.status
  site_report := fun _ _ => rfl
  says_report := fun _ _ => rfl
  says_functional := fun _ _ _ h h' => h ▸ h'
  says_total := fun r => ⟨r.status, rfl⟩
  elim_spec := fun _ _ _ _ _ _ _ _ h => by rw [← h]

/-- At the reference carrier, `Says` on a fresh report is status equality. -/
theorem std6_says {S α : Type} (F : Evidence.Future S) (s : S) (v v' : Status α) :
    (stdCarrier6 F α).Says ((stdCarrier6 F α).report s v) v' ↔ v = v' := Iff.rfl

/-! ## §2. Totality, factorisation, and six load-bearing slots.

`HonestRender.lean` §2 at six branches. Every statement below is that file's with
one more handler; none of them weakens, and `the_sixth_handler_separates` is the
one that has no counterpart there — it is the slot the fold did not have. -/

variable {S α : Type} {F : Evidence.Future S}

/-- `elim` on a fresh report is the dispatch on the status it was made with. -/
theorem elim_report {β : Type} (C : Carrier6 F α) (s : S) (v : Status α)
    (onE onP : α → β) (onFC onFO onA onPd : β) :
    C.elim (C.report s v) onE onP onFC onFO onA onPd
      = dispatch6 onE onP onFC onFO onA onPd v :=
  C.elim_spec _ v onE onP onFC onFO onA onPd (C.says_report s v)

/-- The `exact` computation rule. -/
theorem elim_exact {β : Type} (C : Carrier6 F α) (s : S) (a : α)
    (onE onP : α → β) (onFC onFO onA onPd : β) :
    C.elim (C.report s (Status.exact a)) onE onP onFC onFO onA onPd = onE a :=
  elim_report C s _ onE onP onFC onFO onA onPd

/-- The `provisional` computation rule. -/
theorem elim_provisional {β : Type} (C : Carrier6 F α) (s : S) (a : α)
    (onE onP : α → β) (onFC onFO onA onPd : β) :
    C.elim (C.report s (Status.provisional a)) onE onP onFC onFO onA onPd = onP a :=
  elim_report C s _ onE onP onFC onFO onA onPd

/-- The `forkedClosed` computation rule. -/
theorem elim_forkedClosed {β : Type} (C : Carrier6 F α) (s : S)
    (onE onP : α → β) (onFC onFO onA onPd : β) :
    C.elim (C.report s Status.forkedClosed) onE onP onFC onFO onA onPd = onFC :=
  elim_report C s _ onE onP onFC onFO onA onPd

/-- The `forkedOpen` computation rule. -/
theorem elim_forkedOpen {β : Type} (C : Carrier6 F α) (s : S)
    (onE onP : α → β) (onFC onFO onA onPd : β) :
    C.elim (C.report s Status.forkedOpen) onE onP onFC onFO onA onPd = onFO :=
  elim_report C s _ onE onP onFC onFO onA onPd

/-- The `absent` computation rule — the cell the five-handler eliminator did not
have a slot for. -/
theorem elim_absent {β : Type} (C : Carrier6 F α) (s : S)
    (onE onP : α → β) (onFC onFO onA onPd : β) :
    C.elim (C.report s Status.absent) onE onP onFC onFO onA onPd = onA :=
  elim_report C s _ onE onP onFC onFO onA onPd

/-- The `pending` computation rule — the other half of the split cell. -/
theorem elim_pending {β : Type} (C : Carrier6 F α) (s : S)
    (onE onP : α → β) (onFC onFO onA onPd : β) :
    C.elim (C.report s Status.pending) onE onP onFC onFO onA onPd = onPd :=
  elim_report C s _ onE onP onFC onFO onA onPd

/-- **The eliminator is total.** Every result says a status, and on it `elim` is
exactly the six-handler dispatch: defined at every result, and never returning a
value none of the six handlers supplied. -/
theorem elim_total6 {β : Type} (C : Carrier6 F α) (r : C.R)
    (onE onP : α → β) (onFC onFO onA onPd : β) :
    ∃ v, C.Says r v
      ∧ C.elim r onE onP onFC onFO onA onPd = dispatch6 onE onP onFC onFO onA onPd v := by
  obtain ⟨v, hv⟩ := C.says_total r
  exact ⟨v, hv, C.elim_spec r v onE onP onFC onFO onA onPd hv⟩

/-- **Every consumer is a six-handler dispatch.** `HonestRender.consumers_factor`
at six branches: for any `f : C.R → β` and any site, `f` agrees with the `elim`
built from `f`'s own behaviour on the six statuses. Totality is preserved by the
split — a consumer cannot avoid handling `absent` by writing something other than
`elim`, because whatever it wrote *is* an `elim`, extensionally. -/
theorem consumers_factor6 {β : Type} (C : Carrier6 F α) (f : C.R → β) (s : S)
    (v : Status α) :
    f (C.report s v)
      = C.elim (C.report s v)
          (fun a => f (C.report s (Status.exact a)))
          (fun a => f (C.report s (Status.provisional a)))
          (f (C.report s Status.forkedClosed))
          (f (C.report s Status.forkedOpen))
          (f (C.report s Status.absent))
          (f (C.report s Status.pending)) := by
  rw [elim_report]
  cases v <;> rfl

/-- **NO DEFAULT BRANCH — all six handler slots are observed.** Two consumers
differing in any one of the six handlers differ at some result, so none may be
supplied merely to typecheck. `HonestRender.every_status_slot_is_load_bearing`
with the two zero-candidate slots separated. -/
theorem every_status_slot_is_load_bearing6 {β : Type} (C : Carrier6 F α) (s : S)
    (onE onP onE' onP' : α → β) (onFC onFO onA onPd onFC' onFO' onA' onPd' : β) :
    (onE ≠ onE' → ∃ r : C.R,
        C.elim r onE onP onFC onFO onA onPd ≠ C.elim r onE' onP onFC onFO onA onPd)
      ∧ (onP ≠ onP' → ∃ r : C.R,
        C.elim r onE onP onFC onFO onA onPd ≠ C.elim r onE onP' onFC onFO onA onPd)
      ∧ (onFC ≠ onFC' → ∃ r : C.R,
        C.elim r onE onP onFC onFO onA onPd ≠ C.elim r onE onP onFC' onFO onA onPd)
      ∧ (onFO ≠ onFO' → ∃ r : C.R,
        C.elim r onE onP onFC onFO onA onPd ≠ C.elim r onE onP onFC onFO' onA onPd)
      ∧ (onA ≠ onA' → ∃ r : C.R,
        C.elim r onE onP onFC onFO onA onPd ≠ C.elim r onE onP onFC onFO onA' onPd)
      ∧ (onPd ≠ onPd' → ∃ r : C.R,
        C.elim r onE onP onFC onFO onA onPd ≠ C.elim r onE onP onFC onFO onA onPd') := by
  refine ⟨fun hne => ?_, fun hne => ?_, fun hne => ?_, fun hne => ?_, fun hne => ?_,
    fun hne => ?_⟩
  · obtain ⟨a, ha⟩ : ∃ a, onE a ≠ onE' a :=
      Classical.byContradiction fun hc =>
        hne (funext fun a => Classical.byContradiction fun h => hc ⟨a, h⟩)
    refine ⟨C.report s (Status.exact a), ?_⟩
    rw [elim_exact, elim_exact]
    exact ha
  · obtain ⟨a, ha⟩ : ∃ a, onP a ≠ onP' a :=
      Classical.byContradiction fun hc =>
        hne (funext fun a => Classical.byContradiction fun h => hc ⟨a, h⟩)
    refine ⟨C.report s (Status.provisional a), ?_⟩
    rw [elim_provisional, elim_provisional]
    exact ha
  · refine ⟨C.report s Status.forkedClosed, ?_⟩
    rw [elim_forkedClosed, elim_forkedClosed]
    exact hne
  · refine ⟨C.report s Status.forkedOpen, ?_⟩
    rw [elim_forkedOpen, elim_forkedOpen]
    exact hne
  · refine ⟨C.report s Status.absent, ?_⟩
    rw [elim_absent, elim_absent]
    exact hne
  · refine ⟨C.report s Status.pending, ?_⟩
    rw [elim_pending, elim_pending]
    exact hne

/-- A report determines its status: two reports at the same site with different
statuses are different results. -/
theorem report_status_inj (C : Carrier6 F α) {s : S} {v v' : Status α}
    (h : C.report s v = C.report s v') : v = v' :=
  C.says_functional _ v v' (h ▸ C.says_report s v) (C.says_report s v')

/-- ⚠ **A FIVE-HANDLER CONSUMER IS BLIND AT THE ZERO ROW.** Supply the same
handler to `absent` and `pending` — which is all a five-handler consumer can do,
by `dispatch6_collapses` — and the two reports are indistinguishable. This is
`HonestRender.lean`'s stated limit, restated inside the six-status carrier so
that the next theorem can refute it in the same language. -/
theorem folded_consumers_cannot_separate {β : Type} (C : Carrier6 F α) (s : S)
    (onE onP : α → β) (onFC onFO onV : β) :
    C.elim (C.report s Status.absent) onE onP onFC onFO onV onV
      = C.elim (C.report s Status.pending) onE onP onFC onFO onV onV := by
  rw [elim_absent, elim_pending]

/-- **…and the sixth slot is what removes the blindness.** Two handlers that
differ, and the two zero-candidate reports differ. The fifth handler of the
sibling file was doing double duty; here it is two handlers. -/
theorem the_sixth_handler_separates {β : Type} (C : Carrier6 F α) (s : S)
    (onE onP : α → β) (onFC onFO onA onPd : β) (h : onA ≠ onPd) :
    C.elim (C.report s Status.absent) onE onP onFC onFO onA onPd
      ≠ C.elim (C.report s Status.pending) onE onP onFC onFO onA onPd := by
  rw [elim_absent, elim_pending]
  exact h

/-! ## §3. The soundness contract at six statuses, and `statusOf` discharging it.

`Evidence.SoundEvaluator` constrains one cell: an `exact` report is true where it
is made and never retracted. That is the whole reason the five-status honesty
predicate cannot see §5's lies — they are not about `exact`.

`SoundEvaluator6` adds the two clauses the split makes statable, and they are the
two halves of `ResultStatus.sixth_cell_is_distinguishable`'s **opposite
finality**, turned into obligations on a renderer:

  * `absent_final` — a definitive absence is never retracted;
  * `pending_escapable` — a spinner can stop: some permitted future is not
    `pending`.

A renderer that swaps the two cells therefore fails one clause or the other,
whichever way it swaps, and that is §5. -/

/-- **Inversion at `exact`.** A status of `exact v` is backed by exactly the
evidence that licenses it: the value is a candidate, it seals the candidate set,
and the future is closed. `Evidence.values_of_render_exact` at the refined
status. -/
theorem values_of_statusOf_exact {β : Type} {e : Evidence.ResultEvidence β} {v : β}
    (h : statusOf e = Status.exact v) :
    Evidence.values e v = true ∧ Holes.SealsTo (Evidence.values e) v ∧ Evidence.Closed e :=
  (ResultStatus.statusOf_eq_iff e (Status.exact v)).1 h

/-- No candidate value is in an evidence whose `values` misses it. The bridge
from the value axis back to the attributed candidates, used by the merge
theorems of §6. -/
theorem candidate_false_of_values_false {β : Type} {e : Evidence.ResultEvidence β} {a : β}
    (h : Evidence.values e a = false) (o : Evidence.Source) :
    Evidence.candidates e (a, o) = false := by
  cases hx : Evidence.candidates e (a, o) with
  | false => rfl
  | true =>
    have hv := (Evidence.mem_values e a).mpr ⟨o, hx⟩
    rw [h] at hv
    exact Bool.noConfusion hv

/-- **Inversion at `absent`.** Definitive absence is backed by an empty candidate
set **and** a closed future — the two facts the fold could not keep apart. -/
theorem values_of_statusOf_absent {β : Type} {e : Evidence.ResultEvidence β}
    (h : statusOf e = Status.absent) :
    (∀ a, Evidence.values e a = false) ∧ Evidence.Closed e :=
  (ResultStatus.statusOf_eq_iff e Status.absent).1 h

/-- **Inversion at `pending`.** Nothing observed yet is backed by an empty
candidate set and an **open** future: the same values as `absent`, the opposite
closure. -/
theorem values_of_statusOf_pending {β : Type} {e : Evidence.ResultEvidence β}
    (h : statusOf e = Status.pending) :
    (∀ a, Evidence.values e a = false) ∧ ¬ Evidence.Closed e :=
  (ResultStatus.statusOf_eq_iff e Status.pending).1 h

/-- An open future has a witness: some source is owed and uncertified. -/
theorem exists_open_source {β : Type} {e : Evidence.ResultEvidence β}
    (h : ¬ Evidence.Closed e) :
    ∃ o, Evidence.obligations e o = true ∧ Evidence.certificates e o = false :=
  Classical.byContradiction fun hne =>
    h fun o ho => by
      cases hc : Evidence.certificates e o with
      | true => rfl
      | false => exact absurd ⟨o, ho, hc⟩ hne

/-- **A sound six-status evaluator.** `Evidence.SoundEvaluator`'s two clauses,
plus the three the split makes statable:

  * `exact_correct` / `exact_final` — verbatim the sibling contract;
  * `absent_correct` — a definitive absence is true where it is made: the answer
    set really is empty;
  * `absent_final` — and it is never retracted along a permitted future;
  * `pending_escapable` — a spinner can stop: **some** permitted future is not
    `pending`. Read the quantifier: this is the weakest honest liveness, and the
    boundary says what it does not buy.

`absent_final` and `pending_escapable` have **opposite** shapes, which is the
whole content of the sixth cell: the two zero-candidate statuses differ in
finality and in nothing else. -/
structure SoundEvaluator6 {S β : Type} (F : Evidence.Future S) (answer : S → GSet β)
    (peval : S → Status β) : Prop where
  /-- An exact report is backed by the answer at the state where it is made. -/
  exact_correct : ∀ s v, peval s = Status.exact v →
    answer s v = true ∧ Holes.SealsTo (answer s) v
  /-- An exact report is never retracted along a permitted future. -/
  exact_final : ∀ s t v, F s t → peval s = Status.exact v → peval t = Status.exact v
  /-- An `absent` report is backed where it is made: the answer set is empty. -/
  absent_correct : ∀ s, peval s = Status.absent → ∀ a, answer s a = false
  /-- An `absent` report is never retracted along a permitted future. -/
  absent_final : ∀ s t, F s t → peval s = Status.absent → peval t = Status.absent
  /-- A `pending` report is escapable: some permitted future is not `pending`. -/
  pending_escapable : ∀ s, peval s = Status.pending → ∃ t, F s t ∧ peval t ≠ Status.pending

/-- An exact status survives every sealed future — `Evidence.render_sound`'s
irrevocability at the refined status, proved through `Evidence.closed_freezes`
rather than restated. -/
theorem statusOf_exact_final {β : Type} {s t : Evidence.ResultEvidence β} {v : β}
    (hf : Evidence.SealedFuture s t) (h : statusOf s = Status.exact v) :
    statusOf t = Status.exact v := by
  obtain ⟨hm, hs, hc⟩ := values_of_statusOf_exact h
  obtain ⟨hval, hct⟩ := Evidence.sealed_future_of_closed hc hf
  exact ResultStatus.statusOf_exact (by rw [hval]; exact hm) (by rw [hval]; exact hs) hct

/-- A definitive absence survives every sealed future. The `absent` twin of
`statusOf_exact_final`, and `ResultStatus.empty_status_final_under_sealed` stated
as a transport of the badge rather than as finality of the function. -/
theorem statusOf_absent_final {β : Type} {s t : Evidence.ResultEvidence β}
    (hf : Evidence.SealedFuture s t) (h : statusOf s = Status.absent) :
    statusOf t = Status.absent := by
  obtain ⟨hempty, hc⟩ := values_of_statusOf_absent h
  obtain ⟨hval, hct⟩ := Evidence.sealed_future_of_closed hc hf
  exact ResultStatus.statusOf_absent (fun a => by rw [hval]; exact hempty a) hct

/-- **A `statusOf` spinner can always stop.** Where the status is `pending` some
source is owed and uncertified, so a *sealed* future — one arrival from a source
already owed — makes the candidate set non-empty and the status something other
than `pending`.

The value `a₀` is what arrives, and it is an argument because it has to be:
over an empty value type nothing can arrive and `pending` is genuinely
unescapable. -/
theorem statusOf_pending_escapable {β : Type} [DecidableEq β] (a₀ : β)
    {e : Evidence.ResultEvidence β} (h : statusOf e = Status.pending) :
    ∃ t, Evidence.SealedFuture e t ∧ statusOf t ≠ Status.pending := by
  obtain ⟨_, hopen⟩ := values_of_statusOf_pending h
  obtain ⟨o, ho, hcert⟩ := exists_open_source hopen
  refine ⟨(Evidence.candidates e ⊔ Delta.addDelta (a₀, o), Evidence.obligations e,
      Evidence.certificates e), ⟨⟨?_, ?_⟩, fun _ hx => hx⟩, ?_⟩
  · exact Evidence.leq_of_components (le_merge_left _ _) (leq_refl _) (leq_refl _)
  · intro q h1 h2
    have h3 : (Evidence.candidates e q || Delta.addDelta (a₀, o) q) = true := h2
    rw [h1, Bool.false_or] at h3
    have hq : q = (a₀, o) := of_decide_eq_true h3
    rw [hq]
    exact ⟨ho, hcert⟩
  · intro hp
    have hmem : Evidence.values (Evidence.candidates e ⊔ Delta.addDelta (a₀, o),
        Evidence.obligations e, Evidence.certificates e) a₀ = true := by
      refine (Evidence.mem_values _ a₀).mpr ⟨o, ?_⟩
      show (Evidence.candidates e (a₀, o) || Delta.addDelta (a₀, o) (a₀, o)) = true
      rw [show Delta.addDelta (a₀, o) (a₀, o) = true from by simp [Delta.addDelta]]
      exact Bool.or_true _
    rw [(values_of_statusOf_pending hp).1 a₀] at hmem
    exact Bool.noConfusion hmem

/-- ⚠ **THE CONTRACT `HonestRender.lean` SAID DID NOT EXIST.** `statusOf` is a
sound six-status evaluator for the sealed future: its `exact` reports are true
and irrevocable, its `absent` reports are true and irrevocable, and its `pending`
reports can always be escaped. Every theorem of §4–§5 is stated over a contract
this discharges, so none of them is about an empty class. -/
theorem statusOf_sound6 {β : Type} [DecidableEq β] [Inhabited β] :
    SoundEvaluator6 (Evidence.SealedFuture (α := β)) Evidence.values statusOf where
  exact_correct := fun _ _v h => ⟨(values_of_statusOf_exact h).1, (values_of_statusOf_exact h).2.1⟩
  exact_final := fun _ _ _ hf h => statusOf_exact_final hf h
  absent_correct := fun _ h => (values_of_statusOf_absent h).1
  absent_final := fun _ _ hf h => statusOf_absent_final hf h
  pending_escapable := fun _ h => statusOf_pending_escapable default h

/-- `ResultStatus.forget` reflects `exact`: a status that folds to an `exact`
view **was** that exact status. This is why the six-status contract implies the
five-status one. -/
theorem status_of_forget_exact {β : Type} {st : Status β} {v : β}
    (h : ResultStatus.forget st = Evidence.View.exact v) : st = Status.exact v := by
  cases st with
  | exact a =>
      have h' : Evidence.View.exact a = Evidence.View.exact v := h
      injection h' with ha
      exact congrArg Status.exact ha
  | provisional a =>
      exact absurd h (Evidence.view_ne_of_tag (by simp [Evidence.viewTag, ResultStatus.forget]))
  | forkedClosed =>
      exact absurd h (Evidence.view_ne_of_tag (by simp [Evidence.viewTag, ResultStatus.forget]))
  | forkedOpen =>
      exact absurd h (Evidence.view_ne_of_tag (by simp [Evidence.viewTag, ResultStatus.forget]))
  | absent =>
      exact absurd h (Evidence.view_ne_of_tag (by simp [Evidence.viewTag, ResultStatus.forget]))
  | pending =>
      exact absurd h (Evidence.view_ne_of_tag (by simp [Evidence.viewTag, ResultStatus.forget]))

/-- **THE SIX-STATUS CONTRACT IMPLIES THE FIVE-STATUS ONE.** Fold a sound
six-status evaluator and it is a sound `Evidence.SoundEvaluator`. So nothing the
sibling file proves is lost by moving to this carrier; §5 shows the converse
fails, which is what makes the implication strict. -/
theorem sound6_folds_to_sound {S β : Type} {F : Evidence.Future S} {answer : S → GSet β}
    {peval : S → Status β} (h : SoundEvaluator6 F answer peval) :
    Evidence.SoundEvaluator F answer (fun s => ResultStatus.forget (peval s)) where
  correct := fun s v hv => h.exact_correct s v (status_of_forget_exact hv)
  irrevocable := fun s t v hf hv =>
    congrArg ResultStatus.forget (h.exact_final s t v hf (status_of_forget_exact hv))

/-! ### The render boundary at six statuses -/

/-- **An honest six-status renderer**: some sound six-status evaluator is behind
it, and it reports that evaluator's status at each site. -/
def HonestRenderer6 (F : Evidence.Future S) (answer : S → GSet α)
    (C : Carrier6 F α) (ρ : S → C.R) : Prop :=
  ∃ peval : S → Status α,
    SoundEvaluator6 F answer peval ∧ ∀ s, ρ s = C.report s (peval s)

/-- A sound six-status evaluator, reported at the site it read, is an honest
six-status renderer. -/
theorem soundEvaluator6_renders_honestly {answer : S → GSet α} (C : Carrier6 F α)
    {peval : S → Status α} (hs : SoundEvaluator6 F answer peval) :
    HonestRenderer6 F answer C (fun s => C.report s (peval s)) :=
  ⟨peval, hs, fun _ => rfl⟩

/-- **RENDERED EXACT ⇒ STABLE, at six statuses.** `HonestRender.renderedExact_
implies_stable` re-proved over `Carrier6`, and with the *same* conclusion type:
`HonestRender.StabilityCert`, which is `ResultStatus.Exact`. The guarantee the
sibling file earns is not weakened by the split. -/
theorem renderedExact_implies_stable6 {answer : S → GSet α} {C : Carrier6 F α}
    {ρ : S → C.R} (hρ : HonestRenderer6 F answer C ρ) {s : S} {v : α}
    (h : C.Says (ρ s) (Status.exact v)) :
    HonestRender.StabilityCert F answer s v := by
  obtain ⟨peval, hsound, hrep⟩ := hρ
  have hsays : C.Says (ρ s) (peval s) := by
    rw [hrep s]; exact C.says_report s (peval s)
  have hv : peval s = Status.exact v := C.says_functional (ρ s) _ _ hsays h
  exact fun t ht => hsound.exact_correct t v (hsound.exact_final s t v ht hv)

/-- **An absence certificate**: the answer set is empty at every future `F`
permits from `s`. The `absent` twin of `HonestRender.StabilityCert`, and the
thing an "no results" badge is a promise about. -/
def AbsenceCert (F : Evidence.Future S) (answer : S → GSet α) (s : S) : Prop :=
  ∀ t, F s t → ∀ a, answer t a = false

/-- ⚠ **RENDERED ABSENT ⇒ NO ANSWER, EVER.** The guarantee that has no
counterpart in the five-status file, because the cell it is about was folded
away there: an honest renderer's `absent` report is a promise that the answer set
is empty at **every** permitted future, not merely now. -/
theorem renderedAbsent_implies_absent_forever {answer : S → GSet α} {C : Carrier6 F α}
    {ρ : S → C.R} (hρ : HonestRenderer6 F answer C ρ) {s : S}
    (h : C.Says (ρ s) Status.absent) : AbsenceCert F answer s := by
  obtain ⟨peval, hsound, hrep⟩ := hρ
  have hsays : C.Says (ρ s) (peval s) := by
    rw [hrep s]; exact C.says_report s (peval s)
  have hv : peval s = Status.absent := C.says_functional (ρ s) _ _ hsays h
  exact fun t ht => hsound.absent_correct t (hsound.absent_final s t ht hv)

/-- ⚠ **RENDERED PENDING ⇒ THE WAIT CAN END.** The other new guarantee: an
honest renderer's spinner has a permitted future at which it is not a spinner.
This is the clause `spinnerRender` violates in §5, and the reason "loading
forever on an empty result" is a *refutable* claim here rather than a taste. -/
theorem renderedPending_implies_the_wait_can_end {answer : S → GSet α}
    {C : Carrier6 F α} {ρ : S → C.R} (hρ : HonestRenderer6 F answer C ρ) {s : S}
    (h : C.Says (ρ s) Status.pending) :
    ∃ t, F s t ∧ ¬ C.Says (ρ t) Status.pending := by
  obtain ⟨peval, hsound, hrep⟩ := hρ
  have hsays : C.Says (ρ s) (peval s) := by
    rw [hrep s]; exact C.says_report s (peval s)
  have hv : peval s = Status.pending := C.says_functional (ρ s) _ _ hsays h
  obtain ⟨t, hft, hne⟩ := hsound.pending_escapable s hv
  refine ⟨t, hft, fun hbad => hne ?_⟩
  have hsayst : C.Says (ρ t) (peval t) := by
    rw [hrep t]; exact C.says_report t (peval t)
  exact C.says_functional (ρ t) _ _ hsayst hbad

/-- ⚠ **NO IMPLICIT COERCION, at six statuses.** `HonestRender.no_honest_
projection` re-proved over `Carrier6`, with `HonestRender.IsTheAnswer` as the
honesty notion — the same notion, not a look-alike. At a carrier over evidence
that forks at some site, no total function `C.R → α` is answer-honest. The split
buys a distinction at the zero row and costs nothing here. -/
theorem no_honest_projection6 (C : Carrier6 F α) (answer : S → GSet α) (s : S)
    (hfork : ∃ a b : α, a ≠ b ∧ answer s a = true ∧ answer s b = true) :
    ¬ ∃ g : C.R → α, ∀ r, HonestRender.IsTheAnswer answer (C.site r) (g r) := by
  rintro ⟨g, hg⟩
  obtain ⟨a, b, hab, ha, hb⟩ := hfork
  have h := hg (C.report s Status.forkedOpen)
  rw [C.site_report] at h
  exact hab ((h.2 a ha).trans (h.2 b hb).symm)

/-- **The certified read at six statuses.** The repair for the projection above:
it consumes the result *and* a stability certificate for a value at the result's
own site, and returns that value. -/
def readCertified6 (C : Carrier6 F α) (answer : S → GSet α) (_r : C.R) (v : α)
    (_cert : HonestRender.StabilityCert F answer (C.site _r) v) : α := v

/-- The certified read returns the answer — at every future `F` permits from the
site, not merely at the site. -/
theorem readCertified6_is_the_answer (C : Carrier6 F α) (answer : S → GSet α)
    (r : C.R) (v : α) (cert : HonestRender.StabilityCert F answer (C.site r) v)
    {t : S} (ht : F (C.site r) t) :
    HonestRender.IsTheAnswer answer t (readCertified6 C answer r v cert) := cert t ht

/-! ### The deployed six-status carrier and its sanctioned renderer -/

/-- The six-status carrier at the evidence sites, indexed by the sealed future —
`HonestRender.valCarrier`'s counterpart. -/
def valCarrier6 : Carrier6 (Evidence.SealedFuture (α := Holes.Val)) Holes.Val :=
  stdCarrier6 _ _

/-- **The sanctioned six-status renderer**: report `ResultStatus.statusOf` at the
evidence it read. -/
noncomputable def renderStatusReport
    (C : Carrier6 (Evidence.SealedFuture (α := Holes.Val)) Holes.Val)
    (e : Evidence.ResultEvidence Holes.Val) : C.R := C.report e (statusOf e)

theorem renderStatusReport_eq
    (C : Carrier6 (Evidence.SealedFuture (α := Holes.Val)) Holes.Val)
    (e : Evidence.ResultEvidence Holes.Val) :
    renderStatusReport C e = C.report e (statusOf e) := rfl

/-- The sanctioned six-status renderer is honest — `statusOf_sound6` at the
deployed carrier. -/
theorem renderStatusReport_honest
    (C : Carrier6 (Evidence.SealedFuture (α := Holes.Val)) Holes.Val) :
    HonestRenderer6 (Evidence.SealedFuture (α := Holes.Val)) Evidence.values C
      (renderStatusReport C) :=
  soundEvaluator6_renders_honestly C statusOf_sound6

/-! ### The two new guarantees are not about an empty class

`Evidence.blindEval` is the reason this section exists: an honesty predicate
alone buys nothing if the renderer never says anything. The sanctioned renderer
*does* say `absent` and *does* say `pending`, at named evidence, and the
certificates the badges yield are real. -/

theorem renderStatusReport_says_absent :
    valCarrier6.Says (renderStatusReport valCarrier6 ResultStatus.emptyClosedW)
      Status.absent :=
  (std6_says _ _ _ _).mpr ResultStatus.statusOf_emptyClosedW

theorem renderStatusReport_says_pending :
    valCarrier6.Says (renderStatusReport valCarrier6 ResultStatus.emptyOpenW)
      Status.pending :=
  (std6_says _ _ _ _).mpr ResultStatus.statusOf_emptyOpenW

/-- **The absence badge is backed.** The sanctioned renderer reports `absent` at
`emptyClosedW`, and `renderedAbsent_implies_absent_forever` turns that report
into a certificate: the answer set is empty at every sealed future of
`emptyClosedW`. -/
theorem absent_badge_at_emptyClosedW_is_backed :
    AbsenceCert (Evidence.SealedFuture (α := Holes.Val)) Evidence.values
      ResultStatus.emptyClosedW :=
  renderedAbsent_implies_absent_forever (renderStatusReport_honest valCarrier6)
    renderStatusReport_says_absent

/-- **The spinner badge is escapable.** The sanctioned renderer reports `pending`
at `emptyOpenW`, and `renderedPending_implies_the_wait_can_end` produces the
sealed future at which it is not a spinner — `bob`, still owed, speaks. -/
theorem pending_badge_at_emptyOpenW_can_end :
    ∃ t, Evidence.SealedFuture ResultStatus.emptyOpenW t
      ∧ ¬ valCarrier6.Says (renderStatusReport valCarrier6 t) Status.pending :=
  renderedPending_implies_the_wait_can_end (renderStatusReport_honest valCarrier6)
    renderStatusReport_says_pending

/-! ## §4. THE NAMED LIMIT, RETIRED.

> "a surface built on it cannot tell a spinner from 'there is no answer'"
> — `HonestRender.lean`, honest boundary

The two evidences are `ResultStatus`'s: `emptyClosedW` (definitive absence) and
`emptyOpenW` (nothing observed yet), with the **same** empty candidate set, so
nothing on the value axis separates them and no theorem below is smuggling the
distinction in through the values.

The refutation is in two halves. `five_handlers_cannot_separate` is the limit,
stated at full strength — *every* five-handler consumer, at *every* display type,
returns the same value at the two. `six_carrier_separates` exhibits a consumer of
the sanctioned six-status renderer's reports that returns `false` at one and
`true` at the other. -/

/-- **The limit, at full strength.** Every five-handler consumer — any display
type, any handlers — returns the same value at the two zero-candidate evidences,
because `Evidence.render` sends both to `vacuous`. -/
theorem five_handlers_cannot_separate {β : Type} (onE onP : Holes.Val → β)
    (onFC onFO onV : β) :
    HonestRender.dispatch onE onP onFC onFO onV
        (Evidence.render ResultStatus.emptyClosedW)
      = HonestRender.dispatch onE onP onFC onFO onV
        (Evidence.render ResultStatus.emptyOpenW) := by
  rw [ResultStatus.render_emptyClosedW, ResultStatus.render_emptyOpenW]

/-- **…and at the abstract five-status carrier too**, so the limit is not an
artifact of `dispatch`: at *any* `HonestRender.Carrier`, any site, any handlers,
the two rendered views give the same answer. -/
theorem five_carrier_cannot_separate {S' β : Type} {F' : Evidence.Future S'}
    (C : HonestRender.Carrier F' Holes.Val) (s : S') (onE onP : Holes.Val → β)
    (onFC onFO onV : β) :
    C.elim (C.report s (Evidence.render ResultStatus.emptyClosedW)) onE onP onFC onFO onV
      = C.elim (C.report s (Evidence.render ResultStatus.emptyOpenW)) onE onP onFC onFO onV := by
  rw [HonestRender.elim_report, HonestRender.elim_report,
    ResultStatus.render_emptyClosedW, ResultStatus.render_emptyOpenW]

/-- **THE SEPARATION.** The sanctioned six-status renderer's reports at the two
evidences, read by one consumer — `false` at definitive absence, `true` at
nothing-observed-yet. A surface on this carrier tells a spinner from "there is no
answer". -/
theorem six_carrier_separates :
    valCarrier6.elim (renderStatusReport valCarrier6 ResultStatus.emptyClosedW)
        (fun _ => false) (fun _ => false) false false false true = false
      ∧ valCarrier6.elim (renderStatusReport valCarrier6 ResultStatus.emptyOpenW)
        (fun _ => false) (fun _ => false) false false false true = true := by
  constructor
  · rw [renderStatusReport_eq, ResultStatus.statusOf_emptyClosedW, elim_absent]
  · rw [renderStatusReport_eq, ResultStatus.statusOf_emptyOpenW, elim_pending]

/-- ⚠ **THE LIMIT IS RETIRED, WITH A WITNESS.** Five clauses:

  * the two evidences have the **same** (empty) candidate set, so the value axis
    separates nothing;
  * `Evidence.render` sends both to `vacuous`, and therefore **every**
    five-handler consumer returns the same value at the two;
  * the sanctioned six-status renderer's reports are separated by a consumer;
  * the fold is still recovered exactly (`ResultStatus.forget_statusOf`), so this
    is a refinement and not a rival;
  * and what the separation *is about* is `ResultStatus.sixth_cell_is_
    distinguishable`: the two have opposite finality.

That is the boundary item formerly left open by `HonestRender.lean`, discharged
here. -/
theorem the_named_limit_is_retired :
    (∀ a, Evidence.values ResultStatus.emptyClosedW a = false)
      ∧ (∀ a, Evidence.values ResultStatus.emptyOpenW a = false)
      ∧ (∀ (β : Type) (onE onP : Holes.Val → β) (onFC onFO onV : β),
          HonestRender.dispatch onE onP onFC onFO onV
              (Evidence.render ResultStatus.emptyClosedW)
            = HonestRender.dispatch onE onP onFC onFO onV
              (Evidence.render ResultStatus.emptyOpenW))
      ∧ valCarrier6.elim (renderStatusReport valCarrier6 ResultStatus.emptyClosedW)
          (fun _ => false) (fun _ => false) false false false true
        ≠ valCarrier6.elim (renderStatusReport valCarrier6 ResultStatus.emptyOpenW)
          (fun _ => false) (fun _ => false) false false false true
      ∧ ResultStatus.forget (statusOf ResultStatus.emptyClosedW)
          = Evidence.render ResultStatus.emptyClosedW
      ∧ ResultStatus.forget (statusOf ResultStatus.emptyOpenW)
          = Evidence.render ResultStatus.emptyOpenW := by
  refine ⟨ResultStatus.values_candNone (e := ResultStatus.emptyClosedW) rfl,
    ResultStatus.values_candNone (e := ResultStatus.emptyOpenW) rfl,
    fun _ onE onP onFC onFO onV => five_handlers_cannot_separate onE onP onFC onFO onV,
    ?_, ResultStatus.forget_statusOf _, ResultStatus.forget_statusOf _⟩
  rw [six_carrier_separates.1, six_carrier_separates.2]
  exact Bool.noConfusion

/-! ## §5. THE SIXTH-CELL DISHONEST RENDERERS — and why the fold cannot see them.

`HonestRender.lean` §7 exhibits two dishonest renderers, both about `exact`.
Neither is available at the zero row, because the zero row had one cell. Here are
the two that are, and they are the two UI bugs everyone has shipped:

  * `spinnerRender` — a spinner where the answer is **definitively absent**.
    Loading forever on an empty result.
  * `giveUpRender` — "no results" where evidence is **still owed**. The empty
    state that flashes before the data arrives, asserted as final.

Neither is locally false: at `emptyClosedW` the answer set really is empty, and at
`emptyOpenW` it really is empty too. Both lies are about **finality**, which is
the only thing that separates the two cells — so no check on the *values* can
catch either, and that is why they need the split rather than a better evaluator.

⚠ And the sharp form: `ResultStatus.forget` sends both back to `Evidence.render`
on the nose, so the five-status honesty predicate is *satisfied* by the spinner.
The fold cannot see the lie because the lie lives exactly where the fold is. -/

/-- Swap `absent` for `pending`, leave the other five alone. -/
def spin {β : Type} : Status β → Status β
  | .absent => .pending
  | s => s

/-- Swap `pending` for `absent`, leave the other five alone. -/
def giveUp {β : Type} : Status β → Status β
  | .pending => .absent
  | s => s

/-- ⚠ **THE SPINNER THAT NEVER STOPS.** `statusOf` with definitive absence
re-badged as "nothing observed yet". -/
noncomputable def spinnerRender {β : Type} (e : Evidence.ResultEvidence β) : Status β :=
  spin (statusOf e)

/-- ⚠ **THE EMPTY STATE ASSERTED TOO EARLY.** `statusOf` with "nothing observed
yet" re-badged as definitive absence. -/
noncomputable def giveUpRender {β : Type} (e : Evidence.ResultEvidence β) : Status β :=
  giveUp (statusOf e)

/-- Both swaps are invisible to `ResultStatus.forget`: it sends `absent` and
`pending` to the same view. -/
theorem forget_spin {β : Type} (st : Status β) :
    ResultStatus.forget (spin st) = ResultStatus.forget st := by
  cases st <;> rfl

theorem forget_giveUp {β : Type} (st : Status β) :
    ResultStatus.forget (giveUp st) = ResultStatus.forget st := by
  cases st <;> rfl

/-- ⚠ **THE SPINNER FOLDS TO THE SANCTIONED RENDERER.** Forgetting the zero-row
split turns the lie back into `Evidence.render` — exactly. -/
theorem spinnerRender_folds_to_render {β : Type} (e : Evidence.ResultEvidence β) :
    ResultStatus.forget (spinnerRender e) = Evidence.render e := by
  rw [spinnerRender, forget_spin, ResultStatus.forget_statusOf]

/-- …and so does the premature empty state. -/
theorem giveUpRender_folds_to_render {β : Type} (e : Evidence.ResultEvidence β) :
    ResultStatus.forget (giveUpRender e) = Evidence.render e := by
  rw [giveUpRender, forget_giveUp, ResultStatus.forget_statusOf]

theorem spinnerRender_emptyClosedW :
    spinnerRender ResultStatus.emptyClosedW = Status.pending := by
  show spin (statusOf ResultStatus.emptyClosedW) = Status.pending
  rw [ResultStatus.statusOf_emptyClosedW]
  rfl

/-- **The spinner is correct where it is made** — as `HonestRender.eagerRender`
is. At `emptyClosedW` the answer set really is empty, so nothing about the
*values* is false; what is false is that waiting might help. -/
theorem spinnerRender_correct_where_it_is_made :
    ∀ a, Evidence.values ResultStatus.emptyClosedW a = false :=
  ResultStatus.values_candNone (e := ResultStatus.emptyClosedW) rfl

/-- Every sealed future of `emptyClosedW` is still a spinner: the evidence is
closed, so the status stays `absent` and the swap keeps re-badging it. This is
"loading forever" as a theorem — the spinner has **no** permitted future at which
it stops. -/
theorem spinnerRender_spins_forever (t : Evidence.ResultEvidence Holes.Val)
    (hf : Evidence.SealedFuture ResultStatus.emptyClosedW t) :
    spinnerRender t = Status.pending := by
  show spin (statusOf t) = Status.pending
  rw [statusOf_absent_final hf ResultStatus.statusOf_emptyClosedW]
  rfl

/-- ⚠ **THE SPINNER IS REFUTED, AND BY WHICH CLAUSE.** It reports `pending` at
`emptyClosedW` and every sealed future of `emptyClosedW` is again `pending`, so
`pending_escapable` fails: the wait cannot end. -/
theorem spinnerRender_is_not_sound6 :
    ¬ SoundEvaluator6 (Evidence.SealedFuture (α := Holes.Val)) Evidence.values
        spinnerRender := by
  intro hs
  obtain ⟨t, hf, hne⟩ := hs.pending_escapable ResultStatus.emptyClosedW
    spinnerRender_emptyClosedW
  exact hne (spinnerRender_spins_forever t hf)

theorem giveUpRender_emptyOpenW :
    giveUpRender ResultStatus.emptyOpenW = Status.absent := by
  show giveUp (statusOf ResultStatus.emptyOpenW) = Status.absent
  rw [ResultStatus.statusOf_emptyOpenW]
  rfl

theorem statusOf_bobSpokeW : statusOf ResultStatus.bobSpokeW = Status.provisional 47 :=
  ResultStatus.statusOf_provisional
    (ResultStatus.values_cand47bob (e := ResultStatus.bobSpokeW) rfl).1
    (ResultStatus.values_cand47bob (e := ResultStatus.bobSpokeW) rfl).2
    ResultStatus.not_closed_bobSpokeW

theorem giveUpRender_bobSpokeW :
    giveUpRender ResultStatus.bobSpokeW = Status.provisional 47 := by
  show giveUp (statusOf ResultStatus.bobSpokeW) = Status.provisional 47
  rw [statusOf_bobSpokeW]
  rfl

/-- **The premature empty state is correct where it is made too**: at
`emptyOpenW` the answer set is empty. The lie is again finality. -/
theorem giveUpRender_correct_where_it_is_made :
    ∀ a, Evidence.values ResultStatus.emptyOpenW a = false :=
  ResultStatus.values_candNone (e := ResultStatus.emptyOpenW) rfl

/-- ⚠ **THE PREMATURE EMPTY STATE IS REFUTED, AND BY THE OPPOSITE CLAUSE.** It
reports `absent` at `emptyOpenW`, and the sealed future in which `bob` — still
owed — contributes `47` reports `provisional 47`. So `absent_final` fails: a
definitive absence was retracted. -/
theorem giveUpRender_is_not_sound6 :
    ¬ SoundEvaluator6 (Evidence.SealedFuture (α := Holes.Val)) Evidence.values
        giveUpRender := by
  intro hs
  have h := hs.absent_final ResultStatus.emptyOpenW ResultStatus.bobSpokeW
    ResultStatus.emptyOpenW_seals_to_bobSpokeW giveUpRender_emptyOpenW
  rw [giveUpRender_bobSpokeW] at h
  cases h

/-- ⚠ **THE FIVE-STATUS PREDICATE CERTIFIES THE SPINNER.** The lie's fold is
`Evidence.render`, so `HonestRender.HonestRenderer` — the sibling file's honesty
predicate, unmodified — holds of the renderer that spins forever on a definitively
empty result. This is the limit's cost, stated as a satisfied honesty claim
rather than as a caveat. -/
theorem spinner_is_an_honest_five_status_renderer :
    HonestRender.HonestRenderer (Evidence.SealedFuture (α := Holes.Val))
      Evidence.values HonestRender.valCarrier
      (fun e => HonestRender.valCarrier.report e
        (ResultStatus.forget (spinnerRender e))) :=
  ⟨Evidence.render, Evidence.render_sound,
   fun e => congrArg (HonestRender.valCarrier.report e) (spinnerRender_folds_to_render e)⟩

/-- ⚠ **SIX IS STRICTLY STRONGER THAN FIVE.** Three clauses:

  * every sound six-status evaluator folds to a sound five-status one
    (`sound6_folds_to_sound`) — nothing is lost;
  * the spinner's fold **is** `Evidence.render`, so the five-status contract holds
    of it;
  * and the six-status contract does not.

The containment is strict, and the witness is the "loading forever on an empty
result" bug. -/
theorem six_is_strictly_stronger_than_five :
    (∀ (S' β : Type) (F' : Evidence.Future S') (answer : S' → GSet β)
        (peval : S' → Status β), SoundEvaluator6 F' answer peval →
        Evidence.SoundEvaluator F' answer (fun s => ResultStatus.forget (peval s)))
      ∧ (∀ e, ResultStatus.forget (spinnerRender e) = Evidence.render (α := Holes.Val) e)
      ∧ Evidence.SoundEvaluator (Evidence.SealedFuture (α := Holes.Val)) Evidence.values
          (fun e => ResultStatus.forget (spinnerRender e))
      ∧ ¬ SoundEvaluator6 (Evidence.SealedFuture (α := Holes.Val)) Evidence.values
          spinnerRender := by
  refine ⟨fun _ _ _ _ _ h => sound6_folds_to_sound h, spinnerRender_folds_to_render,
    ?_, spinnerRender_is_not_sound6⟩
  have hfun : (fun e => ResultStatus.forget (spinnerRender e))
      = Evidence.render (α := Holes.Val) := funext spinnerRender_folds_to_render
  rw [hfun]
  exact Evidence.render_sound

/-- ⚠ **AND THE FOLD ADMITS AN EVALUATOR THE SPLIT REFUTES TWICE OVER.**
`Evidence.blindEval` — always `vacuous` — is a *sound* five-status evaluator
(`Evidence.completeness_is_load_bearing`). It has exactly two refinements to six
statuses, the eternal spinner and the eternal empty state, and **both** are
refuted: the first has no escape from `pending`, the second claims an absence
that `exactW`'s evidence contradicts on the spot.

So the sound-but-silent evaluator the sibling file had to admit is not admissible
here — the split gives the contract teeth the fold could not have. -/
theorem the_fold_admits_an_evaluator_the_split_refutes :
    Evidence.SoundEvaluator (Evidence.SealedFuture (α := Holes.Val)) Evidence.values
        (Evidence.blindEval (S := Evidence.ResultEvidence Holes.Val))
      ∧ (∀ e : Evidence.ResultEvidence Holes.Val,
          ResultStatus.forget (Status.pending (α := Holes.Val))
            = Evidence.blindEval (β := Holes.Val) e)
      ∧ (∀ e : Evidence.ResultEvidence Holes.Val,
          ResultStatus.forget (Status.absent (α := Holes.Val))
            = Evidence.blindEval (β := Holes.Val) e)
      ∧ ¬ SoundEvaluator6 (Evidence.SealedFuture (α := Holes.Val)) Evidence.values
          (fun _ : Evidence.ResultEvidence Holes.Val => Status.pending (α := Holes.Val))
      ∧ ¬ SoundEvaluator6 (Evidence.SealedFuture (α := Holes.Val)) Evidence.values
          (fun _ : Evidence.ResultEvidence Holes.Val => Status.absent (α := Holes.Val)) := by
  refine ⟨Evidence.completeness_is_load_bearing.1, fun _ => rfl, fun _ => rfl, ?_, ?_⟩
  · intro hs
    obtain ⟨_, _, hne⟩ := hs.pending_escapable Evidence.exactW rfl
    exact hne rfl
  · intro hs
    have h := hs.absent_correct Evidence.exactW rfl 47
    rw [(Evidence.values_cand47 (e := Evidence.exactW) rfl).1] at h
    exact Bool.noConfusion h

/-! ## §6. IS `absent` MORE DEFENSIBLE THAN `exact`?

`ResultStatus.absence_outlives_exactness` says the folded-away cell is the *most
stable of the six*: `Evidence.render` is final at `emptyClosedW` under the full
extension future and is not final at `exactW`. The natural conjecture is that an
`absent` badge is therefore more defensible than an `exact` one, and that the
six-status carrier inherits the advantage.

It does not, and the measurement is worth having:

  * **content** — both are frozen under the *full extension* future, by
    `Evidence.closed_freezes`, since both statuses entail closure. No asymmetry;
  * **badge under extension** — **neither** survives. A roster growth turns
    `exact 47` into `provisional 47` and `absent` into `pending`. No asymmetry;
  * **badge under the sealed future** — both survive. No asymmetry;
  * **the fold** — `Evidence.render` survives at `emptyClosedW` and not at
    `exactW`, which is the theorem `ResultStatus` proved.

⚠ So the gap it measured is the fold's blindness: `render` does not move at
`emptyClosedW` **because it cannot see `absent` become `pending`**. Splitting the
cell — which §4 must do — costs exactly that stability. That is the one place the
six-status version is weaker, and it is stated here rather than omitted.

The asymmetry that does survive is on the **merge** axis, and it is the operative
one for a local-first surface: `absent` is I-confluent and `exact` is not. -/

/-- The content of an `exact` badge is frozen under the **full extension**
future, not merely the sealed one: closure freezes the candidate set, so the
certificate upgrades. Stated at `ResultStatus.Exact`, so it is
`HonestRender.StabilityCert` at a larger future relation. -/
theorem statusOf_exact_content_survives_extension {β : Type}
    {e : Evidence.ResultEvidence β} {v : β} (h : statusOf e = Status.exact v) :
    ResultStatus.Exact Evidence.ExtensionFuture Evidence.values e v := by
  obtain ⟨hm, hs, hc⟩ := values_of_statusOf_exact h
  intro t ht
  rw [Evidence.values_congr (Evidence.closed_freezes hc ht.1 ht.2)]
  exact ⟨hm, hs⟩

/-- The content of an `absent` badge is frozen under the full extension future
too — by the same closure argument, and to exactly the same degree. -/
theorem statusOf_absent_content_survives_extension {β : Type}
    {e : Evidence.ResultEvidence β} (h : statusOf e = Status.absent) :
    AbsenceCert Evidence.ExtensionFuture Evidence.values e := by
  obtain ⟨hempty, hc⟩ := values_of_statusOf_absent h
  intro t ht a
  rw [Evidence.values_congr (Evidence.closed_freezes hc ht.1 ht.2)]
  exact hempty a

/-- ⚠ **THE `absent` BADGE IS RETRACTED BY A ROSTER GROWTH.** Admit one source
nobody had heard of and `absent` re-opens to `pending`, with an identical (empty)
candidate set. `ResultStatus.absence_survives_values_not_closure` at the badge:
`statusOf` is **not** final at `emptyClosedW` under the extension future, though
`Evidence.render` is. -/
theorem statusOf_not_extension_final_at_emptyClosedW :
    ¬ Evidence.FreeTermination Evidence.ExtensionFuture
        (statusOf (α := Holes.Val)) ResultStatus.emptyClosedW := by
  intro hft
  have h := hft ResultStatus.emptyOpenW ResultStatus.emptyClosedW_extends_to_emptyOpenW
  rw [ResultStatus.statusOf_emptyOpenW, ResultStatus.statusOf_emptyClosedW] at h
  cases h

/-- …and the `exact` badge is retracted by the same move, which is
`Evidence.render_retracts_when_a_new_source_appears` at the status. -/
theorem statusOf_not_extension_final_at_exactW :
    ¬ Evidence.FreeTermination Evidence.ExtensionFuture
        (statusOf (α := Holes.Val)) Evidence.exactW := by
  intro hft
  have h := hft Evidence.openW Evidence.exactW_extends_to_openW
  rw [ResultStatus.statusOf_openW, ResultStatus.statusOf_exactW] at h
  cases h

/-- The `exact` badge is final under the sealed future. -/
theorem statusOf_sealed_final_at_exactW :
    Evidence.FreeTermination Evidence.SealedFuture
      (statusOf (α := Holes.Val)) Evidence.exactW := by
  intro t ht
  rw [statusOf_exact_final ht ResultStatus.statusOf_exactW, ResultStatus.statusOf_exactW]

/-- The `absent` badge is final under the sealed future. -/
theorem statusOf_sealed_final_at_emptyClosedW :
    Evidence.FreeTermination Evidence.SealedFuture
      (statusOf (α := Holes.Val)) ResultStatus.emptyClosedW := by
  intro t ht
  rw [statusOf_absent_final ht ResultStatus.statusOf_emptyClosedW,
    ResultStatus.statusOf_emptyClosedW]

/-- ⚠ **UNDER EVERY FUTURE THE TWO CELLS ARE SYMMETRIC.** Content frozen under
extension for both; badge retracted under extension for both; badge final under
the sealed future for both. Whatever makes `absent` more defensible than `exact`,
it is not stability along a future — and that is the conjecture this file went
looking for. -/
theorem absence_and_exactness_are_symmetric_under_every_future :
    AbsenceCert Evidence.ExtensionFuture Evidence.values ResultStatus.emptyClosedW
      ∧ ResultStatus.Exact Evidence.ExtensionFuture Evidence.values Evidence.exactW 47
      ∧ ¬ Evidence.FreeTermination Evidence.ExtensionFuture
          (statusOf (α := Holes.Val)) ResultStatus.emptyClosedW
      ∧ ¬ Evidence.FreeTermination Evidence.ExtensionFuture
          (statusOf (α := Holes.Val)) Evidence.exactW
      ∧ Evidence.FreeTermination Evidence.SealedFuture
          (statusOf (α := Holes.Val)) ResultStatus.emptyClosedW
      ∧ Evidence.FreeTermination Evidence.SealedFuture
          (statusOf (α := Holes.Val)) Evidence.exactW :=
  ⟨statusOf_absent_content_survives_extension ResultStatus.statusOf_emptyClosedW,
   statusOf_exact_content_survives_extension ResultStatus.statusOf_exactW,
   statusOf_not_extension_final_at_emptyClosedW,
   statusOf_not_extension_final_at_exactW,
   statusOf_sealed_final_at_emptyClosedW,
   statusOf_sealed_final_at_exactW⟩

/-- ⚠ **THE STABILITY GAP WAS THE FOLD.** Side by side: `Evidence.render` is
final at `emptyClosedW` under the extension future and not at `exactW` — the
sibling file's `absence_outlives_exactness` — while `statusOf` is final at
**neither**. The extra stability absence appeared to enjoy is the fold declining
to notice `absent` become `pending`, and `forget_statusOf` says the two functions
otherwise agree.

So this is the price of §4, quoted exactly: a six-status surface re-renders "no
results" as "loading" when a source nobody had heard of is admitted, where the
five-status surface did not flicker — **because it could not tell the two
apart**. -/
theorem the_stability_gap_was_the_fold :
    Evidence.FreeTermination Evidence.ExtensionFuture Evidence.render
        ResultStatus.emptyClosedW
      ∧ ¬ Evidence.FreeTermination Evidence.ExtensionFuture Evidence.render
          Evidence.exactW
      ∧ ¬ Evidence.FreeTermination Evidence.ExtensionFuture
          (statusOf (α := Holes.Val)) ResultStatus.emptyClosedW
      ∧ ¬ Evidence.FreeTermination Evidence.ExtensionFuture
          (statusOf (α := Holes.Val)) Evidence.exactW
      ∧ ResultStatus.forget (statusOf ResultStatus.emptyClosedW)
          = Evidence.render ResultStatus.emptyClosedW :=
  ⟨ResultStatus.absence_outlives_exactness.1,
   ResultStatus.absence_outlives_exactness.2,
   statusOf_not_extension_final_at_emptyClosedW,
   statusOf_not_extension_final_at_exactW,
   ResultStatus.forget_statusOf _⟩

/-! ### The merge axis — where absence really is the stronger badge -/

/-- **DEFINITIVE ABSENCE SURVIVES MERGE.** Two replicas that each report "there is
no answer and there will not be one" merge to a replica that reports it —
coordination-free, `Evidence.closed_iconfluent` on the closure axis and
`Catalog.gset_notmem_iconfluent`'s argument on the value axis. -/
theorem absent_iconfluent {β : Type} {e₁ e₂ : Evidence.ResultEvidence β}
    (h1 : statusOf e₁ = Status.absent) (h2 : statusOf e₂ = Status.absent) :
    statusOf (e₁ ⊔ e₂) = Status.absent := by
  obtain ⟨hem1, hc1⟩ := values_of_statusOf_absent h1
  obtain ⟨hem2, hc2⟩ := values_of_statusOf_absent h2
  refine ResultStatus.statusOf_absent (fun a => ?_) (Evidence.closed_iconfluent _ _ hc1 hc2)
  cases hb : Evidence.values (e₁ ⊔ e₂) a with
  | false => rfl
  | true =>
    obtain ⟨o, ho⟩ := (Evidence.mem_values _ a).mp hb
    have ho' : (Evidence.candidates e₁ (a, o) || Evidence.candidates e₂ (a, o)) = true := ho
    rw [candidate_false_of_values_false (hem1 a) o,
      candidate_false_of_values_false (hem2 a) o] at ho'
    exact Bool.noConfusion ho'

/-- One candidate, `49`, attributed to `bob`. -/
def cand49bob : GSet (Holes.Val × Evidence.Source) :=
  fun p => decide (p = (49, Evidence.bob))

/-- Only `bob` may still speak. -/
def srcsB : GSet Evidence.Source := fun o => decide (o = Evidence.bob)

/-- **A second exact replica.** `bob` said `49`, `bob` is the only source owed,
and `bob` is certified: by every measure this replica's answer is exact and
final. It is `Evidence.exactW` with the other peer's name and the other value. -/
def exact49W : Evidence.ResultEvidence Holes.Val := (cand49bob, srcsB, srcsB)

theorem mem_cand49bob {b : Holes.Val} {o : Evidence.Source} (h : cand49bob (b, o) = true) :
    b = 49 ∧ o = Evidence.bob := by
  have hd := of_decide_eq_true h
  exact ⟨congrArg Prod.fst hd, congrArg Prod.snd hd⟩

theorem values_cand49bob {e : Evidence.ResultEvidence Holes.Val}
    (h : Evidence.candidates e = cand49bob) :
    Evidence.values e 49 = true ∧ Holes.SealsTo (Evidence.values e) 49 := by
  constructor
  · exact (Evidence.mem_values e 49).mpr ⟨Evidence.bob, by rw [h]; decide⟩
  · intro b hb
    obtain ⟨o, ho⟩ := (Evidence.mem_values e b).mp hb
    rw [h] at ho
    exact (mem_cand49bob ho).1

theorem closed_exact49W : Evidence.Closed exact49W := fun _ h => h

theorem statusOf_exact49W : statusOf exact49W = Status.exact 49 :=
  ResultStatus.statusOf_exact (values_cand49bob (e := exact49W) rfl).1
    (values_cand49bob (e := exact49W) rfl).2 closed_exact49W

theorem values_merge_47 : Evidence.values (Evidence.exactW ⊔ exact49W) 47 = true :=
  (Evidence.mem_values _ 47).mpr ⟨Evidence.alice, by decide⟩

theorem values_merge_49 : Evidence.values (Evidence.exactW ⊔ exact49W) 49 = true :=
  (Evidence.mem_values _ 49).mpr ⟨Evidence.bob, by decide⟩

theorem closed_merge : Evidence.Closed (Evidence.exactW ⊔ exact49W) :=
  Evidence.closed_iconfluent _ _ Evidence.closed_exactW closed_exact49W

/-- ⚠ **TWO EXACT BADGES MERGE TO A CLOSED FORK.** Each replica is exact and
closed; the merge holds `47` and `49` and every source is certified, so waiting
will not fix it. -/
theorem statusOf_merge_of_two_exacts :
    statusOf (Evidence.exactW ⊔ exact49W) = Status.forkedClosed :=
  ResultStatus.statusOf_forkedClosed values_merge_47 values_merge_49 (by decide) closed_merge

/-- ⚠ **`absent` IS THE MORE DEFENSIBLE BADGE — ON THE MERGE AXIS.** The
asymmetry the future axis does not have:

  * two replicas each reporting definitive absence merge to definitive absence,
    for **every** pair, with no coordination (`absent_iconfluent`);
  * two replicas each reporting `exact` merge to a **closed fork** — `exactW` says
    `47`, `exact49W` says `49`, both are closed, and the merge is
    `forkedClosed`.

This is `Evidence.closed_iconfluent` and `Holes.determinacy_not_iconfluent`
meeting at the render boundary, and for a local-first surface it is the operative
sense of "defensible": it is what happens when two peers sync. An "no results"
badge survives the sync; a checkmark does not. -/
theorem absence_is_the_more_defensible_badge :
    (∀ e₁ e₂ : Evidence.ResultEvidence Holes.Val, statusOf e₁ = Status.absent →
        statusOf e₂ = Status.absent → statusOf (e₁ ⊔ e₂) = Status.absent)
      ∧ statusOf Evidence.exactW = Status.exact 47
      ∧ statusOf exact49W = Status.exact 49
      ∧ statusOf (Evidence.exactW ⊔ exact49W) = Status.forkedClosed :=
  ⟨fun _ _ h1 h2 => absent_iconfluent h1 h2, ResultStatus.statusOf_exactW,
   statusOf_exact49W, statusOf_merge_of_two_exacts⟩

/-! ## §7. All six cells, reached by evidence a sound renderer actually reports.

`HonestRender.every_status_slot_is_load_bearing` quantifies over `C.report s v`
for an arbitrary `v`: it proves the *slots* are observable, not that a sound
renderer ever produces the reports that observe them. At six statuses the
stronger statement is available, because `ResultStatus` names an evidence for
every cell — so each handler is pinned to a report the **sanctioned** renderer
makes at a **named** piece of evidence. -/

/-- All six cells are reached by `statusOf`, at six named evidences. -/
theorem six_cells_inhabited :
    statusOf Evidence.exactW = Status.exact 47
      ∧ statusOf Evidence.openW = Status.provisional 47
      ∧ statusOf Evidence.forkedClosedW = Status.forkedClosed
      ∧ statusOf Evidence.forkedOpenW = Status.forkedOpen
      ∧ statusOf ResultStatus.emptyClosedW = Status.absent
      ∧ statusOf ResultStatus.emptyOpenW = Status.pending :=
  ⟨ResultStatus.statusOf_exactW, ResultStatus.statusOf_openW,
   ResultStatus.statusOf_forkedClosedW, ResultStatus.statusOf_forkedOpenW,
   ResultStatus.statusOf_emptyClosedW, ResultStatus.statusOf_emptyOpenW⟩

/-- ⚠ **EVERY HANDLER IS THE WHOLE BEHAVIOUR OF A CONSUMER AT REAL EVIDENCE.**
For any display type and any six handlers, each handler *is* what a consumer of
the sanctioned renderer returns at one of six named pieces of evidence. So none
of the six may be supplied merely to typecheck — not because some report exists
that observes it, but because the deployed renderer makes that report. -/
theorem the_six_handlers_are_reached_by_real_evidence {β : Type}
    (onE onP : Holes.Val → β) (onFC onFO onA onPd : β) :
    valCarrier6.elim (renderStatusReport valCarrier6 Evidence.exactW)
        onE onP onFC onFO onA onPd = onE 47
      ∧ valCarrier6.elim (renderStatusReport valCarrier6 Evidence.openW)
        onE onP onFC onFO onA onPd = onP 47
      ∧ valCarrier6.elim (renderStatusReport valCarrier6 Evidence.forkedClosedW)
        onE onP onFC onFO onA onPd = onFC
      ∧ valCarrier6.elim (renderStatusReport valCarrier6 Evidence.forkedOpenW)
        onE onP onFC onFO onA onPd = onFO
      ∧ valCarrier6.elim (renderStatusReport valCarrier6 ResultStatus.emptyClosedW)
        onE onP onFC onFO onA onPd = onA
      ∧ valCarrier6.elim (renderStatusReport valCarrier6 ResultStatus.emptyOpenW)
        onE onP onFC onFO onA onPd = onPd := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [renderStatusReport_eq, ResultStatus.statusOf_exactW, elim_exact]
  · rw [renderStatusReport_eq, ResultStatus.statusOf_openW, elim_provisional]
  · rw [renderStatusReport_eq, ResultStatus.statusOf_forkedClosedW, elim_forkedClosed]
  · rw [renderStatusReport_eq, ResultStatus.statusOf_forkedOpenW, elim_forkedOpen]
  · rw [renderStatusReport_eq, ResultStatus.statusOf_emptyClosedW, elim_absent]
  · rw [renderStatusReport_eq, ResultStatus.statusOf_emptyOpenW, elim_pending]

/-! ## §8. The salience limit is unchanged, and that is the honest report.

`HonestRender.lean` §8's ⟨TERMINAL⟩ item survives the split verbatim: a
presentation is a function out of the result, constant functions exist, and a
sixth handler is one more thing that can be written identical to the other five.
What the split adds to the *enforceable* half is one more observed slot, which
`every_status_slot_is_load_bearing6` already carries. -/

/-- ⚠ **SALIENCE IS STILL NOT ENFORCEABLE.** A consumer that supplies all six
handlers may still return the same `β` at every result. Six branches, written
identical, is `OpenForked` in one-pixel grey with a spinner that looks the same
as "no results". -/
theorem salience_is_not_enforceable6 {β : Type} (C : Carrier6 F α) (b : β) (r : C.R) :
    C.elim r (fun _ => b) (fun _ => b) b b b b = b := by
  obtain ⟨v, hv⟩ := C.says_total r
  rw [C.elim_spec r v _ _ _ _ _ _ hv]
  cases v <;> rfl

/-- **PRESENCE IS ENFORCED, PROMINENCE IS NOT — at six statuses.** The negative
half is `salience_is_not_enforceable6`; the positive half is that the `absent`
handler is observed by some result, so the new slot is no more decorative than
the five it joins. -/
theorem presence_enforced_prominence_not6 {β : Type} (C : Carrier6 F α) (s : S)
    (b b' : β) (hbb : b ≠ b') :
    (∀ r : C.R, C.elim r (fun _ => b) (fun _ => b) b b b b = b)
      ∧ (∃ r : C.R, C.elim r (fun _ => b) (fun _ => b) b b b b
          ≠ C.elim r (fun _ => b) (fun _ => b) b b b' b) :=
  ⟨fun r => salience_is_not_enforceable6 C b r,
   (every_status_slot_is_load_bearing6 C s (fun _ => b) (fun _ => b) (fun _ => b)
      (fun _ => b) b b b b b b b' b).2.2.2.2.1 hbb⟩

end Uwueave.RenderSix
