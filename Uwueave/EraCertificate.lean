/-
# Uwueave.EraCertificate — ERA's finalisation, run through the certificate machinery.

**Origin: the oldest named ⟨UNDONE⟩ in the tree.** `Holes.lean` §6 built the
abstract collapse licence `Stable Arriving P`, named `Era.final_view_immune` as
"the intended implementing instance of the input-side licence", and closed with
the admission that *"the transport from Era's event lists into a `Stable`
hypothesis here is named in the boundary as unbuilt, and until it is built the
instance is a design intention rather than a theorem."* `Evidence.lean` §8
narrowed the hole — `closed_freezes` derives the licence from evidence — and
`CertificateScope.lean` then built the general theory the Era bridge needs
(`Residual`, `SufficientKey`, `KeyCertSound`, `key_licenses_reuse`,
`no_sound_key_cert_accepts`) while recording, in its own boundary, that nobody
had run Era through it:

> ⟨UNDONE⟩ **No Era placement.** Codex names "a sealed epoch" as a candidate
> implementation. What is proved here is about `World.epoch`, the producer's
> counter `WorldFuture.lean` defines; `Era.lean`'s arbiter cut is *not*
> transported to this carrier […] `epoch_sufficient_on_wellformed` is a fact
> about a `Nat` field, not about a finalisation.

This file is that placement. Nothing in `Era.lean`, `CertificateScope.lean`,
`Evidence.lean`, `WorldFuture.lean` or `Holes.lean` is edited; every connection
below is a theorem.

## The Era world, and its three futures

A replica's ERA state is grow-only in two components (`Era.EraState = GSet Cut ×
GSet Event`) sitting inside a context it cannot read: the events issued anywhere
(`pool`). `EraWorld` is that triple, and it separates **three** things that
`WorldFuture.lean`'s two futures conflate, because ERA has an actor
`WorldFuture` does not have — the arbiter:

  * `Delivery` — issued events arrive. Cuts frozen, pool frozen.
  * `Issuance` — new events are *created*. Cuts frozen, pool grows.
  * `Announcement` — **the arbiter acts.** The cut set grows.

⚠ Note the asymmetry, which is the protocol's and not the model's: events have a
pool bounding what may still arrive, and **announcements have no pool**. The
arbiter's stream is unbounded by construction (§4.1 of the paper: it announces
whenever it likes). Every negative result below lives on that axis.

## What landed

  * **The set form of finality** (§2). `resolveFinal_congr`: the finalised view
    is a function of the cut *set* and the finalised-delivered event *set*, and
    nothing else. `Era.final_view_immune` is re-derived from it as an instance
    (`era_final_view_immune_reproved`) rather than restated beside it.
  * **`era_finalisation_is_a_sound_certificate`** (§3) — the answer to the
    question this file exists for. The finalised-view evaluator is
    free-terminating under `Delivery` at every world where **`Settled`** holds:
    the arbiter has named no event the replica has not delivered. As a
    `KeyCertSound` instance at the key of §4, unscoped — the certificate needs
    no domain restriction, only the sufficiency does.
  * **ERA stops strictly before quiescence** (`era_stops_before_quiescence`) —
    the payoff, and the reason the certificate is worth having: at `wPre` the
    finalised view is stable while the **full** view is not, and the world is
    not quiesced. `WorldFuture.quiescence_is_a_sound_certificate` is the
    certificate a plain CRDT has; this is the one an arbiter buys.
  * **The sufficient key, and the refuted coarser sibling** (§4).
    `eraKey_sufficient_on_wf`: `(cut set, finalised delivered set, finalised
    pool set)` is sufficient for the finalised view under `Delivery`, on
    wellformed worlds. `finalPoolFreeKey_not_sufficient`: dropping the third
    component is **not** sufficient — the exact analogue of
    `CertificateScope.pool_not_sufficient`, and the same verdict in the same
    vocabulary: **the pool rides along**. `eraKey_drops_the_pending` shows the
    key genuinely quotients (pending events are invisible to it), so
    sufficiency is not injectivity in disguise.
  * **The trust premise, as a named hypothesis** (§5). `HonestExtension`: every
    new announcement record carries an epoch strictly above every announced
    epoch. Under it, `honest_announcement_resumes_the_finalised_view` — the new
    finalised view is the old one with the newly-finalised events folded on
    top. So an honest announcement **extends** the finalised view and never
    rewrites it, which is the precise sense in which an old certificate is
    still sound "for the view so far". `docs/TRUST.md` Ledger 3 records
    "prefix stability under cut growth is *not* claimed"; this claims it, under
    the hypothesis, and refutes it without.
  * ⚠ **The old answer stands and the old licence does not**, and the two are
    separate facts: `a_silent_announcement_keeps_the_view_and_revokes_the_licence`
    exhibits an announcement that leaves the finalised view *identical* and
    makes the certificate refuse, because something blessed is now in flight.
    `an_announcement_changes_the_name` is the structural reason no reuse is ever
    claimed across an announcement: the cut set is a key component.
  * ⚠ **Two Byzantine seams, exhibited rather than assumed away.**
    `backdated_cut_rewrites_the_finalised_view`: one announcement record naming
    an *already announced* epoch flips a finalised verdict — Alice and Bob swap
    roles, a finalised event rolled back, no delivery involved. And
    `an_event_born_finalised_rewrites_the_view`: an event **forged with an
    already-announced id** is finalised the moment it is issued, lands inside
    the finalised prefix and flips the same verdict — with a perfectly honest
    arbiter and a frozen cut set.
  * **`Holes.Stable` is inhabited by the Era instance** (§7).
    `era_cut_licenses_the_collapse` discharges §6's abstract hypothesis at a
    concrete Era `Arriving`, `era_seal_survives` runs
    `Holes.seal_survives_stable` on it, and
    `the_era_licence_is_not_the_trivial_one` separates it from
    `Holes.stable_of_subsumed`: the arrival it survives is one that has **not**
    happened and that genuinely carries news — it moves the full view.
    `the_cut_axis_breaks_the_seal` and `the_unlicensed_collapse_is_a_lie` are
    `Holes.unstable_seal_clash` at the Era carrier, on the axis that breaks.

## The TRANSPORTS row this file owes

**Abstract collapse licence → Era finalisation** ⚠
*transport* `EraCertificate.era_cut_licenses_the_collapse` (and
`era_finalisation_is_a_sound_certificate` in `CertificateScope`'s vocabulary) ·
*needs* **`Settled`** — the arbiter has named nothing the replica has not
delivered — **and the delivery axis only** · *without it*
`delivery_alone_does_not_license_the_finalised_view` (an announced-but-undelivered
event moves the finalised view under plain delivery),
`the_cut_axis_breaks_the_seal` (a new announcement moves it at a **quiesced**
world), `backdated_cut_rewrites_the_finalised_view` (a dishonest announcement
rolls a finalised verdict back), `an_event_born_finalised_rewrites_the_view` (an
id collision does the same with an honest arbiter).

## Honest boundary

⟨TERMINAL⟩ = a theorem of this model; ⟨UNDONE⟩ = work wearing a caveat's clothes.

  * ⟨TERMINAL⟩ **The certificate is about the finalised view, not the view.**
    `finalView` is what `Era.resolveFinal` reports; `fullView` is `Era.resolve`.
    The whole content of `era_stops_before_quiescence` is that these come apart,
    and no theorem here licenses stopping on the full view before quiescence.
  * ⟨TERMINAL⟩ **A key licenses reuse, not verification** — inherited verbatim
    from `CertificateScope`. `era_verifiedAt_is_sound` is the reuse form, and it
    needs one honest verification to have happened.
  * ⚠ ⟨UNDONE⟩ **Finality rests on event-id unforgeability, and the miniature
    drops it.** `Era.lean` says ids stand in for hashes and that no uniqueness
    premise is needed — which is exactly right for `resolve_same_sets`, whose
    determinism survives a collision. It is **not** right for finality:
    `an_event_born_finalised_rewrites_the_view` builds a second event with id
    `5`, which `laterCuts` has announced, and it enters the finalised prefix and
    reverses the duel. Closing this needs §2's recursive hash linking — the
    named-dropped plumbing — not a further theorem about this carrier.
  * ⟨UNDONE⟩ **`HonestExtension` is a hypothesis, not a detection.** It is
    satisfiable (`honest_setup_to_later`) and refutable
    (`backdating_is_not_honest`) and nothing here decides which one a live
    announcement is. The paper answers with signatures and fraud proofs (§5.1);
    both are out of scope in `Era.lean` and remain out of scope here.
  * ⟨UNDONE⟩ **The announcement future has no certificate at all.** §5 says what
    an honest announcement *does* to the finalised view; it exhibits no
    predicate on a world that licenses a stop under `Announcement`, and
    `announcement_moves_the_finalised_view` shows quiescence is not one. What
    would serve is a bound on the arbiter's remaining announcements — the pool
    the arbiter does not have.
  * ⟨UNDONE⟩ **One evaluator at a time**, and `Type 0` only —
    `CertificateScope`'s two, inherited.
  * ⟨UNDONE⟩ **The witnesses are witnesses.** §3-§6's separations run on
    `Era.duelLog` and its two cut sets. No theorem here characterises which
    worlds a key glues, and there is no decision procedure for `Settled` over
    unbounded pools.

Literature: ERA is Dougal, PaPoC 2026 (arXiv:2601.22963) — §2.1's `Final`, §4.1's
epoch layering, §5.1's monotone epoch creation and §5.2's "safe from rollback".
Free Termination (Power–Koutris–Hellerstein, arXiv:2502.00222) supplies the
stability question; the residual is Nerode's right congruence with futures in
place of word suffixes, as `CertificateScope.lean` records.
-/
import Uwueave.CertificateScope
import Uwueave.Era

namespace Uwueave.EraCertificate

open Uwueave Uwueave.Catalog Uwueave.CertificateScope

/-! ## §1. The Era world, and the three futures.

A replica **holds** two grow-only sets — the arbiter's announcement records and
the events it has delivered. It **sits in** a pool: the events issued anywhere,
which is what may still arrive without anyone doing anything new. That is
`WorldFuture.lean`'s `issued`, at Era's carrier.

There is deliberately **no pool for cuts**. The arbiter announces when it likes
(§4.1: "epochs are triggered based on the number of events in the pending
epoch"), so nothing bounds the announcement stream from inside a replica. The
three futures below separate the three things that can happen next, and §3-§6
show the certificate holds on exactly one of them. -/

/-- **An Era world.** What the replica holds — the arbiter's announcement
records and its delivered events — together with the pool of events issued
anywhere. The first two are `Era.EraState`'s two components in list transport;
the third is the context no replica can read. -/
structure EraWorld where
  /-- The arbiter's announcement records this replica has (§4.1). -/
  cuts : List Era.Cut
  /-- The events this replica has delivered. -/
  log : List Era.Event
  /-- Every event issued anywhere: the delivery pool. -/
  pool : List Era.Event

/-- **Wellformed**: what has been delivered was issued. `WorldFuture.Wf` at this
carrier, and carried as a hypothesis rather than an invariant for the same
reason: nothing in the type enforces it. -/
def Wf (w : EraWorld) : Prop := ∀ e ∈ w.log, e ∈ w.pool

/-- **Quiesced**: the whole pool has been delivered. The certificate a plain
CRDT has, and §3 shows ERA's is strictly weaker. -/
def Quiesced (w : EraWorld) : Prop := ∀ e ∈ w.pool, e ∈ w.log

instance (w : EraWorld) : Decidable (Wf w) := by unfold Wf; infer_instance

instance (w : EraWorld) : Decidable (Quiesced w) := by unfold Quiesced; infer_instance

/-- ⚠ Quiescence does **not** imply wellformedness here, and the two are not
two readings of one inclusion: `Quiesced` is `pool ⊆ log` and `Wf` is
`log ⊆ pool`. `WorldFuture.wf_of_quiesced` holds because there quiescence is an
*equality* of state and pool; at this carrier the two directions are separate
facts and both witnesses below carry them separately. -/
theorem quiesced_and_wf_iff_same_sets {w : EraWorld} :
    (Quiesced w ∧ Wf w) ↔ ∀ e, e ∈ w.log ↔ e ∈ w.pool :=
  ⟨fun h e => ⟨h.2 e, h.1 e⟩, fun h => ⟨fun e he => (h e).mpr he, fun e he => (h e).mp he⟩⟩

/-- **The delivery future.** Already-issued events arrive; the arbiter is
silent and nothing new is created. Cut set and pool are frozen — as *sets*,
since everything ERA decides is a function of the sets (`Era.resolve_same_sets`)
and nothing here should be able to see a list. -/
def Delivery (w t : EraWorld) : Prop :=
  (∀ c, c ∈ t.cuts ↔ c ∈ w.cuts)
    ∧ (∀ e, e ∈ t.pool ↔ e ∈ w.pool)
    ∧ (∀ e ∈ w.log, e ∈ t.log)
    ∧ (∀ e ∈ t.log, e ∈ w.pool)

/-- **The issuance future.** New events are created and may be delivered; the
arbiter is still silent. The pool grows, which is exactly what `Delivery`
forbids. -/
def Issuance (w t : EraWorld) : Prop :=
  (∀ c, c ∈ t.cuts ↔ c ∈ w.cuts)
    ∧ (∀ e ∈ w.pool, e ∈ t.pool)
    ∧ (∀ e ∈ w.log, e ∈ t.log)
    ∧ (∀ e ∈ t.log, e ∈ t.pool)

/-- **The announcement future — the arbiter acting.** The cut set grows;
delivery may happen alongside. This is the axis with no pool, and the axis every
negative result below lives on. -/
def Announcement (w t : EraWorld) : Prop :=
  (∀ c ∈ w.cuts, c ∈ t.cuts)
    ∧ (∀ e, e ∈ t.pool ↔ e ∈ w.pool)
    ∧ (∀ e ∈ w.log, e ∈ t.log)
    ∧ (∀ e ∈ t.log, e ∈ w.pool)

/-- Delivery is reflexive exactly at wellformed worlds — the side condition
`CertificateScope.key_licenses_reuse` cannot drop
(`the_reflexivity_side_condition_is_load_bearing`). -/
theorem delivery_refl {w : EraWorld} (h : Wf w) : Delivery w w :=
  ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, fun _ he => he, h⟩

/-- A delivery is an announcement that announced nothing: the sound future is a
sub-relation of the breaking one, which is why §5's refutations are refutations
of *this* certificate and not of a different one. -/
theorem delivery_is_announcement {w t : EraWorld} (h : Delivery w t) :
    Announcement w t :=
  ⟨fun c hc => (h.1 c).mpr hc, h.2.1, h.2.2.1, h.2.2.2⟩

/-- A delivery is an issuance that issued nothing. -/
theorem delivery_is_issuance {w t : EraWorld} (h : Delivery w t) : Issuance w t :=
  ⟨h.1, fun e he => (h.2.1 e).mpr he, h.2.2.1, fun e he => (h.2.1 e).mpr (h.2.2.2 e he)⟩

/-! ## §2. The finalised evaluator, and finality in set form.

`Era.resolveFinal` executes only what the arbiter has placed in an epoch. §2's
one lemma says what it depends on: the cut set, and the finalised part of the
delivered set. Everything below — the immunity theorem, the sufficient key, the
insufficiency of the coarser one — is that lemma read at a different index. -/

/-- **The finalised view** — `Era.resolveFinal` as an evaluator on worlds. What
§2.1 of the paper calls final: what no missed concurrent event can roll back. -/
def finalView (w : EraWorld) : Era.GroupView := Era.resolveFinal w.cuts w.log

/-- **The full view** — `Era.resolve` as an evaluator on worlds. The finalised
prefix with the pending suffix folded on top (`Era.resolve_resumes_final`). -/
def fullView (w : EraWorld) : Era.GroupView := Era.resolve w.cuts w.log

/-- Membership-equivalent cut lists agree on what is finalised —
`Era.epochOf_congr` at the `finalized` predicate. -/
theorem finalized_congr {cuts cuts' : List Era.Cut}
    (hc : ∀ c, c ∈ cuts ↔ c ∈ cuts') (e : Era.Event) :
    Era.finalized cuts e = Era.finalized cuts' e := by
  unfold Era.finalized
  rw [Era.epochOf_congr hc e.eid]

/-- **THE SET FORM OF FINALITY.** The finalised view is a function of two sets:
the announcement records, and the delivered events the announcements name.
Delivery order, duplication, batching and *every pending event whatsoever* are
invisible to it. `Era.final_view_immune` is the special case where the second
list is the first plus a pending batch. -/
theorem resolveFinal_congr {cuts cuts' : List Era.Cut} {log log' : List Era.Event}
    (hc : ∀ c, c ∈ cuts ↔ c ∈ cuts')
    (h : ∀ e, (e ∈ log ∧ Era.finalized cuts e = true)
            ↔ (e ∈ log' ∧ Era.finalized cuts' e = true)) :
    Era.resolveFinal cuts log = Era.resolveFinal cuts' log' := by
  have hmem : ∀ e : Era.Event,
      e ∈ log.filter (Era.finalized cuts) ↔ e ∈ log'.filter (Era.finalized cuts') := by
    intro e
    rw [List.mem_filter, List.mem_filter]
    exact h e
  unfold Era.resolveFinal
  rw [Era.execOrder_same_sets hc hmem]

/-- **`Era.final_view_immune`, re-derived.** The statement of Era's finality
theorem, obtained from the set form rather than restated beside it: a batch of
still-pending events changes nothing about the finalised view. -/
theorem era_final_view_immune_reproved (cuts : List Era.Cut) (log fresh : List Era.Event)
    (hfresh : ∀ e ∈ fresh, Era.finalized cuts e = false) :
    Era.resolveFinal cuts (log ++ fresh) = Era.resolveFinal cuts log := by
  refine resolveFinal_congr (fun _ => Iff.rfl) (fun e => ?_)
  constructor
  · rintro ⟨he, hf⟩
    rcases List.mem_append.mp he with h | h
    · exact ⟨h, hf⟩
    · exact absurd hf (by rw [hfresh e h]; exact Bool.noConfusion)
  · rintro ⟨he, hf⟩
    exact ⟨List.mem_append.mpr (Or.inl he), hf⟩

/-! ## §3. The certificate.

`Settled` is the world predicate the finalisation certificate accepts: *the
arbiter has named nothing I have not delivered*. It is what §2.1's rollback
immunity needs and — the point of the file — it is **weaker than quiescence**,
which is the whole reason ERA is worth its trust premise. -/

/-- **Settled**: every event in the pool that this replica's cuts finalise has
already been delivered. Equivalently: nothing the arbiter has blessed is still
in flight. ⚠ It is a fact about the **pool**, so a replica cannot read it off
itself — exactly `WorldFuture.Quiesced`'s epistemic status, and for the same
reason (`CertificateScope.deliveryKey_sufficient`: the pool rides along). -/
def Settled (w : EraWorld) : Prop :=
  ∀ e ∈ w.pool, Era.finalized w.cuts e = true → e ∈ w.log

instance (w : EraWorld) : Decidable (Settled w) := by unfold Settled; infer_instance

/-- Quiescence is the sledgehammer: deliver everything and nothing announced can
be outstanding. §3's separation says the converse fails. -/
theorem settled_of_quiesced {w : EraWorld} (h : Quiesced w) : Settled w :=
  fun e he _ => h e he

/-- **The finalised view does not move under delivery, at a settled world.**
`Era.final_view_immune` transported to the world carrier: a delivery can only
bring pending events, and pending events are invisible to `resolveFinal`. -/
theorem finalView_immune {w t : EraWorld} (hs : Settled w) (hd : Delivery w t) :
    finalView t = finalView w := by
  refine resolveFinal_congr (fun c => hd.1 c) (fun e => ?_)
  have hfin : Era.finalized t.cuts e = Era.finalized w.cuts e :=
    finalized_congr (fun c => hd.1 c) e
  constructor
  · rintro ⟨he, hf⟩
    refine ⟨hs e (hd.2.2.2 e he) (by rw [← hfin]; exact hf), by rw [← hfin]; exact hf⟩
  · rintro ⟨he, hf⟩
    exact ⟨hd.2.2.1 e he, by rw [hfin]; exact hf⟩

/-- **The finalisation certificate is sound, at the world index.** At a settled
world the finalised view is free-terminating under delivery — the property
`Evidence.lean` and `CertificateScope.lean` call stability, discharged for
ERA. -/
theorem era_final_view_free_terminating {w : EraWorld} (hs : Settled w) :
    Evidence.FreeTermination Delivery finalView w :=
  fun _ hd => finalView_immune hs hd

/-! ### §3.1 The premise is load-bearing, and the certificate beats quiescence -/

/-- Fig. 2's setup delivered, the duel still in flight: epoch 1 holds the two
joins and the promotion, and the two demotes are issued but not delivered here. -/
def wPre : EraWorld := ⟨Era.setupCuts, [Era.e1, Era.e2, Era.e3], Era.duelLog⟩

/-- The same world with the duel delivered — a legal delivery future of `wPre`,
and the one that moves the full view. -/
def wAll : EraWorld := ⟨Era.setupCuts, Era.duelLog, Era.duelLog⟩

/-- ⚠ The arbiter is **ahead of the replica**: `laterCuts` announces event `5`,
which this replica has not delivered. Same delivered log as `wPre`. -/
def wAhead : EraWorld := ⟨Era.laterCuts, [Era.e1, Era.e2, Era.e3], Era.duelLog⟩

/-- `wAhead` after the announced event lands. -/
def wAheadAll : EraWorld := ⟨Era.laterCuts, Era.duelLog, Era.duelLog⟩

/-- `wAhead`'s delivered log with a pool holding nothing else — the world that
shares `wAhead`'s pool-free key and does not share its residual. -/
def wClosed : EraWorld :=
  ⟨Era.laterCuts, [Era.e1, Era.e2, Era.e3], [Era.e1, Era.e2, Era.e3]⟩

theorem wf_wPre : Wf wPre := by decide

theorem wf_wAhead : Wf wAhead := by decide

theorem wf_wClosed : Wf wClosed := by decide

theorem settled_wPre : Settled wPre := by decide

theorem settled_wClosed : Settled wClosed := by decide

theorem quiesced_wAll : Quiesced wAll := by decide

theorem delivery_wPre_wAll : Delivery wPre wAll :=
  ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, by decide, by decide⟩

theorem delivery_wAhead_wAheadAll : Delivery wAhead wAheadAll :=
  ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, by decide, by decide⟩

/-- ⚠ **The `Settled` premise cannot be dropped.** At `wAhead` the arbiter has
announced event `5` and the replica has not delivered it; one delivery later the
*finalised* view has changed — Alice was an Admin in it and is a Reader now.
Nothing dishonest happened: the arbiter announced a cut over an event the
replica had not yet seen, which Fig. 6 permits explicitly.

This is the Era analogue of `WorldFuture.no_sound_state_cert_accepts_openW`: the
danger is not what has been delivered but what is still owed. -/
theorem delivery_alone_does_not_license_the_finalised_view :
    ¬ Settled wAhead ∧ ¬ Evidence.FreeTermination Delivery finalView wAhead := by
  refine ⟨by decide, fun h => ?_⟩
  have hmv := h wAheadAll delivery_wAhead_wAheadAll
  have hrole : (finalView wAheadAll).role Era.alice = (finalView wAhead).role Era.alice :=
    congrArg (fun v => v.role Era.alice) hmv
  exact absurd hrole (by decide)

/-- **ERA stops strictly before quiescence** — the theorem the trust premise is
paid for. At `wPre` the duel is still in flight: the world is not quiesced, the
**full** view is not stable (delivering the duel demotes Bob), and the
**finalised** view is stable anyway. A plain CRDT's only certificate is
`WorldFuture.quiescence_is_a_sound_certificate`, which `wPre` does not hold;
`Settled`, which it does hold, is what the arbiter's announcement buys. -/
theorem era_stops_before_quiescence :
    ¬ Quiesced wPre
      ∧ Settled wPre
      ∧ Evidence.FreeTermination Delivery finalView wPre
      ∧ ¬ Evidence.FreeTermination Delivery fullView wPre := by
  refine ⟨by decide, settled_wPre, era_final_view_free_terminating settled_wPre, fun h => ?_⟩
  have hmv := h wAll delivery_wPre_wAll
  have hrole : (fullView wAll).role Era.bob = (fullView wPre).role Era.bob :=
    congrArg (fun v => v.role Era.bob) hmv
  exact absurd hrole (by decide)

/-! ## §4. The sufficient key.

Which name may a finalisation certificate be filed under, so that another
replica carrying that name may reuse it? §4 answers with a key that is provably
sufficient and a plausible coarser one that is provably not, in the shape
`CertificateScope.the_key_table` uses. -/

/-- The finalised part of a list, as the grow-only set it transports. -/
def finalSet (cuts : List Era.Cut) (l : List Era.Event) : GSet Era.Event :=
  fun e => decide (e ∈ l) && Era.finalized cuts e

theorem mem_finalSet {cuts : List Era.Cut} {l : List Era.Event} {e : Era.Event} :
    finalSet cuts l e = true ↔ (e ∈ l ∧ Era.finalized cuts e = true) := by
  unfold finalSet
  rw [Bool.and_eq_true, decide_eq_true_iff]

/-- **The Era delivery key**: the announcement records, the finalised events
delivered, and the finalised events *issued*. The third component is the pool
`CertificateScope.deliveryKey_sufficient` insisted on, narrowed to the part of
the pool that can reach the finalised view at all. -/
def eraKey (w : EraWorld) : GSet Era.Cut × GSet Era.Event × GSet Era.Event :=
  (Era.cutSet w.cuts, finalSet w.cuts w.log, finalSet w.cuts w.pool)

/-- ⚠ **The plausible coarser key**: what I hold, and nothing about what is
still owed. Refuted below. -/
def finalPoolFreeKey (w : EraWorld) : GSet Era.Cut × GSet Era.Event :=
  (Era.cutSet w.cuts, finalSet w.cuts w.log)

theorem cutSet_iff {cs cs' : List Era.Cut} (h : Era.cutSet cs = Era.cutSet cs')
    (c : Era.Cut) : c ∈ cs ↔ c ∈ cs' :=
  decide_eq_decide.mp (congrFun h c)

/-- One inclusion of the residual transport: rebuild the future world over the
other world's context, keeping only the events that its cuts finalise. Nothing
else is visible to `resolveFinal`. -/
theorem residual_transport {w v : EraWorld} (hv : Wf v) (hk : eraKey w = eraKey v)
    (r : Era.GroupView) (hr : Residual finalView Delivery w r) :
    Residual finalView Delivery v r := by
  obtain ⟨t, hd, rfl⟩ := hr
  have hcut : ∀ c, c ∈ w.cuts ↔ c ∈ v.cuts := cutSet_iff (congrArg Prod.fst hk)
  have hlogk : finalSet w.cuts w.log = finalSet v.cuts v.log :=
    congrArg (fun k => k.2.1) hk
  have hpoolk : finalSet w.cuts w.pool = finalSet v.cuts v.pool :=
    congrArg (fun k => k.2.2) hk
  have hfin : ∀ e, Era.finalized w.cuts e = Era.finalized v.cuts e :=
    fun e => finalized_congr hcut e
  refine ⟨⟨v.cuts, v.log ++ t.log.filter (Era.finalized v.cuts), v.pool⟩, ?_, ?_⟩
  · refine ⟨fun _ => Iff.rfl, fun _ => Iff.rfl, fun e he => List.mem_append.mpr (Or.inl he),
      fun e he => ?_⟩
    rcases List.mem_append.mp he with h | h
    · exact hv e h
    · have hf := List.mem_filter.mp h
      have hwp : e ∈ w.pool := hd.2.2.2 e hf.1
      have hwf : Era.finalized w.cuts e = true := by rw [hfin e]; exact hf.2
      have hvp : finalSet v.cuts v.pool e = true := by
        rw [← hpoolk]
        exact mem_finalSet.mpr ⟨hwp, hwf⟩
      exact (mem_finalSet.mp hvp).1
  · refine resolveFinal_congr (fun c => (hcut c).symm.trans (hd.1 c).symm) (fun e => ?_)
    have hfint : Era.finalized t.cuts e = Era.finalized w.cuts e :=
      finalized_congr (fun c => hd.1 c) e
    constructor
    · rintro ⟨he, hf⟩
      have hft : Era.finalized t.cuts e = true := by
        rw [hfint, hfin e]; exact hf
      rcases List.mem_append.mp he with h | h
      · have hwl : e ∈ w.log := by
          have hwk : finalSet w.cuts w.log e = true := by
            rw [hlogk]
            exact mem_finalSet.mpr ⟨h, hf⟩
          exact (mem_finalSet.mp hwk).1
        exact ⟨hd.2.2.1 e hwl, hft⟩
      · exact ⟨(List.mem_filter.mp h).1, hft⟩
    · rintro ⟨he, hf⟩
      have hvf : Era.finalized v.cuts e = true := by
        rw [← hfin e, ← hfint]; exact hf
      exact ⟨List.mem_append.mpr (Or.inr (List.mem_filter.mpr ⟨he, hvf⟩)), hvf⟩

/-- **THE SUFFICIENT KEY.** Two wellformed worlds carrying the same
`(cuts, finalised delivered, finalised issued)` have the same residual for the
finalised view under delivery — so a finalisation certificate may travel by key
equality, and `CertificateScope.key_licenses_reuse_on` applies to it. -/
theorem eraKey_sufficient_on_wf :
    SufficientKeyOn Wf eraKey finalView Delivery := by
  intro w v hw hv hk r
  exact ⟨fun h => residual_transport hv hk r h,
         fun h => residual_transport hw hk.symm r h⟩

/-- The same world with one *pending* event delivered. -/
def wPrePlus : EraWorld :=
  ⟨Era.setupCuts, [Era.e1, Era.e2, Era.e3, Era.e4], Era.duelLog⟩

/-- ⚠ **The key genuinely quotients.** `wPre` and `wPrePlus` differ — one has
delivered Alice's demote — and carry the same key, because that event is
pending and the key sees only the finalised part. So
`eraKey_sufficient_on_wf` is not injectivity in disguise: the whole pending
epoch is invisible to it, which is the exact sense in which the finalisation
certificate is reusable while a state-keyed one is not. -/
theorem eraKey_drops_the_pending : eraKey wPre = eraKey wPrePlus ∧ wPre ≠ wPrePlus := by
  constructor
  · refine congrArg (fun s => (Era.cutSet Era.setupCuts, s, finalSet Era.setupCuts Era.duelLog))
      (funext fun e => ?_)
    show (decide (e ∈ [Era.e1, Era.e2, Era.e3]) && Era.finalized Era.setupCuts e)
        = (decide (e ∈ [Era.e1, Era.e2, Era.e3, Era.e4]) && Era.finalized Era.setupCuts e)
    by_cases h : e = Era.e4
    · subst h
      have : Era.finalized Era.setupCuts Era.e4 = false := by decide
      rw [this, Bool.and_false, Bool.and_false]
    · have hm : (e ∈ [Era.e1, Era.e2, Era.e3, Era.e4]) ↔ (e ∈ [Era.e1, Era.e2, Era.e3]) := by
        simp [List.mem_cons, h]
      rw [decide_eq_decide.mpr hm.symm]
  · intro h
    exact absurd (congrArg EraWorld.log h) (by decide)

/-- ⚠ **THE REFUTED COARSER SIBLING.** Drop the finalised-pool component and the
key is no longer sufficient — on wellformed worlds, with both witnesses in the
domain. `wAhead` and `wClosed` hold the same announcement records and have
delivered the same finalised events; one of them is still owed an *announced*
event and the other is not, and their residuals differ by exactly the verdict
that event carries.

The verdict is the one `CertificateScope.observe_not_sufficient` and
`frontierEpoch_not_sufficient` deliver on `WorldFuture`'s carrier — everything
about the context except what has been issued is not enough — and it is the exact
complement of `deliveryKey_sufficient`: **what is still owed rides in the key, or
the key licenses a reuse across a genuine change of future.** -/
theorem finalPoolFreeKey_not_sufficient :
    ¬ SufficientKeyOn Wf finalPoolFreeKey finalView Delivery := by
  intro h
  have hres := h wAhead wClosed wf_wAhead wf_wClosed rfl
  have hmem : Residual finalView Delivery wAhead (finalView wAheadAll) :=
    ⟨wAheadAll, delivery_wAhead_wAheadAll, rfl⟩
  obtain ⟨u, hu, heu⟩ := (hres (finalView wAheadAll)).mp hmem
  have hfix : finalView u = finalView wClosed := finalView_immune settled_wClosed hu
  have hrole : (finalView wAheadAll).role Era.alice = (finalView wClosed).role Era.alice :=
    congrArg (fun v => v.role Era.alice) (heu.symm.trans hfix)
  exact absurd hrole (by decide)

/-! ### §4.1 The certificate, keyed -/

/-- **The finalisation certificate, as a predicate on the key**: every finalised
event that exists has been delivered. Readable from the key alone — which is
what makes it a `KeyCertSound` instance rather than a world predicate wearing a
key's clothes. -/
def settledCert (k : GSet Era.Cut × GSet Era.Event × GSet Era.Event) : Prop :=
  ∀ e, k.2.2 e = true → k.2.1 e = true

/-- The certificate's acceptance at a world's key **is** `Settled` — an iff, so
nothing is lost in the passage to the key. -/
theorem settledCert_iff (w : EraWorld) : settledCert (eraKey w) ↔ Settled w := by
  constructor
  · intro h e he hf
    exact (mem_finalSet.mp (h e (mem_finalSet.mpr ⟨he, hf⟩))).1
  · intro h e hp
    obtain ⟨he, hf⟩ := mem_finalSet.mp hp
    exact mem_finalSet.mpr ⟨h e he hf, hf⟩

/-- **ERA'S FINALISATION IS A SOUND CERTIFICATE** — the theorem this file exists
for, in `CertificateScope`'s own vocabulary and at its own index. The evaluator
is the finalised view, the future is **delivery** (cuts frozen, pool frozen),
the key is §4's, and the certificate accepts exactly the keys whose finalised
pool is already delivered.

⚠ Unscoped: soundness needs no domain restriction. Only the *reuse* half
(`eraKey_sufficient_on_wf`, and `era_verifiedAt_is_sound` below) needs
wellformedness, because that is where reflexivity of the future is used. -/
theorem era_finalisation_is_a_sound_certificate :
    KeyCertSound eraKey finalView Delivery settledCert :=
  fun w hC => era_final_view_free_terminating ((settledCert_iff w).mp hC)

/-- The certificate is a floor and behaves like one: **satisfiable** at a world
with news still in flight, and **refutable** at one whose arbiter is ahead of
it. A certificate that could not go red would not be one. -/
theorem the_certificate_is_satisfiable_and_refutable :
    settledCert (eraKey wPre) ∧ ¬ settledCert (eraKey wAhead) :=
  ⟨(settledCert_iff wPre).mpr settled_wPre,
   fun h => (by decide : ¬ Settled wAhead) ((settledCert_iff wAhead).mp h)⟩

/-- **The reuse form.** `CertificateScope.verifiedAt_sound_of_sufficientKeyOn`
applied to §4's key: one honest verification, filed under the key, is sound for
every wellformed world carrying that key. This is `key_licenses_reuse` for a
finalisation, and the reason the key had to be sufficient and not merely
correct. -/
theorem era_verifiedAt_is_sound :
    KeyCertSoundOn Wf eraKey finalView Delivery
      (verifiedAt Wf eraKey finalView Delivery) :=
  verifiedAt_sound_of_sufficientKeyOn eraKey_sufficient_on_wf
    (fun _ h => delivery_refl h)

/-! ## §5. The cut axis — the arbiter acting, and the premise that makes it safe.

`Era.lean`'s header is explicit that "prefix stability under *cut* growth is
correspondingly NOT claimed", and `docs/TRUST.md`'s third ledger repeats it as a
premise of the protocol. §5 turns that premise into a **hypothesis of a
theorem**: `HonestExtension` says every new announcement record carries an epoch
strictly above everything already announced, and under it the finalised view is
*extended*, never rewritten. Without it, a single record rolls a finalised
verdict back. -/

/-- **The honest-announcement premise.** New records only, and every new record
sits strictly above every epoch already announced. §5.1's "consistency of
finalised events relies on the monotonic creation of epochs", as a relation
between two announcement sets.

⚠ This is a hypothesis, not a check: nothing here detects a violation. The paper
answers detection with signatures and fraud proofs, both out of scope. -/
def HonestExtension (cuts cuts' : List Era.Cut) : Prop :=
  (∀ c ∈ cuts, c ∈ cuts') ∧ (∀ c ∈ cuts', c ∉ cuts → ∀ d ∈ cuts, d.1 < c.1)

instance (cuts cuts' : List Era.Cut) : Decidable (HonestExtension cuts cuts') := by
  unfold HonestExtension; infer_instance

/-- Under honest extension an already-assigned epoch is **preserved**, not
merely lowered: `Era.epochOf_mono` gives `≤`, and the honesty premise closes the
gap, because a smaller answer would have to come from a new record. -/
theorem epochOf_preserved {cuts cuts' : List Era.Cut} (h : HonestExtension cuts cuts')
    {eid m : Nat} (hm : Era.epochOf cuts eid = some m) :
    Era.epochOf cuts' eid = some m := by
  obtain ⟨m', hm', hle⟩ := Era.epochOf_mono h.1 hm
  by_cases hin : (m', eid) ∈ cuts
  · have hge : m ≤ m' := Era.epochOf_some_le hm hin
    rw [hm', Nat.le_antisymm hle hge]
  · have hlt : m < m' :=
      h.2 (m', eid) (Era.epochOf_some_mem hm') hin (m, eid) (Era.epochOf_some_mem hm)
    omega

theorem epochOf_none_of_not_finalized {cuts : List Era.Cut} {e : Era.Event}
    (h : Era.finalized cuts e = false) : Era.epochOf cuts e.eid = none := by
  cases hh : Era.epochOf cuts e.eid with
  | none => rfl
  | some k =>
    exfalso
    have : Era.finalized cuts e = true := by unfold Era.finalized; rw [hh]; rfl
    rw [this] at h
    exact Bool.noConfusion h

theorem epochOf_some_of_finalized {cuts : List Era.Cut} {e : Era.Event}
    (h : Era.finalized cuts e = true) : ∃ m, Era.epochOf cuts e.eid = some m := by
  cases hh : Era.epochOf cuts e.eid with
  | none =>
    exfalso
    have : Era.finalized cuts e = false := by unfold Era.finalized; rw [hh]; rfl
    rw [this] at h
    exact Bool.noConfusion h
  | some m => exact ⟨m, rfl⟩

/-- An already-finalised event keeps its exact epoch across an honest
announcement. -/
theorem epochOf_agree {cuts cuts' : List Era.Cut} (h : HonestExtension cuts cuts')
    {e : Era.Event} (hf : Era.finalized cuts e = true) :
    Era.epochOf cuts' e.eid = Era.epochOf cuts e.eid := by
  obtain ⟨m, hm⟩ := epochOf_some_of_finalized hf
  rw [hm]
  exact epochOf_preserved h hm

/-- The finalised region only grows — `Era.epochOf_mono` at the `finalized`
predicate. -/
theorem finalized_mono {cuts cuts' : List Era.Cut} (h : HonestExtension cuts cuts')
    {e : Era.Event} (hf : Era.finalized cuts e = true) :
    Era.finalized cuts' e = true := by
  unfold Era.finalized
  rw [epochOf_agree h hf]
  exact hf

/-- **Newly finalised events execute after every previously finalised one.**
This is where honesty does its work: a new record's epoch outranks every old
one, so the events it blesses land at the *end* of the finalised order rather
than in the middle of it. -/
theorem honest_cross {cuts cuts' : List Era.Cut} (h : HonestExtension cuts cuts')
    (a b : Era.Event) (ha : Era.finalized cuts a = true)
    (hb : Era.finalized cuts b = false) : Era.elt cuts' a b := by
  obtain ⟨m, hma⟩ := epochOf_some_of_finalized ha
  have ha' : Era.epochOf cuts' a.eid = some m := epochOf_preserved h hma
  have hbn : Era.epochOf cuts b.eid = none := epochOf_none_of_not_finalized hb
  cases hmb : Era.epochOf cuts' b.eid with
  | none => exact Era.elt_final_pending ha' hmb
  | some k =>
    have hknot : (k, b.eid) ∉ cuts := fun hc => (Era.epochOf_none_iff.mp hbn k) hc
    have hlt : m < k :=
      h.2 (k, b.eid) (Era.epochOf_some_mem hmb) hknot (m, a.eid) (Era.epochOf_some_mem hma)
    exact Era.elt_of_epoch_lt ha' hmb hlt

/-- On events already finalised, the announcement changes no comparison — their
epochs are preserved, and `Era.elt` reads nothing else about the cuts. -/
theorem elt_agree {cuts cuts' : List Era.Cut} (h : HonestExtension cuts cuts')
    {a b : Era.Event} (ha : Era.finalized cuts a = true)
    (hb : Era.finalized cuts b = true) : Era.elt cuts' a b ↔ Era.elt cuts a b := by
  unfold Era.elt Era.epri Era.epnum
  rw [epochOf_agree h ha, epochOf_agree h hb]

/-- Pairwise transfer along an implication that only has to hold on the list's
own members — `Era.pairwise_mono` is global, and §5 needs the restricted
version. -/
theorem pairwise_imp_mem {R S : Era.Event → Era.Event → Prop} :
    ∀ {l : List Era.Event}, (∀ a ∈ l, ∀ b ∈ l, R a b → S a b) →
      l.Pairwise R → l.Pairwise S := by
  intro l
  induction l with
  | nil => intro _ _; exact List.Pairwise.nil
  | cons a t ih =>
    intro hRS hp
    cases hp with
    | cons ha ht =>
      refine List.Pairwise.cons
        (fun b hb => hRS a (List.Mem.head t) b (List.Mem.tail a hb) (ha b hb)) ?_
      exact ih (fun x hx y hy => hRS x (List.Mem.tail a hx) y (List.Mem.tail a hy)) ht

/-- The events an announcement newly finalises, out of a delivered log. -/
def newlyFinal (cuts cuts' : List Era.Cut) (log : List Era.Event) : List Era.Event :=
  (log.filter (Era.finalized cuts')).filter (fun e => !Era.finalized cuts e)

/-- **AN HONEST ANNOUNCEMENT EXTENDS THE FINALISED VIEW; IT DOES NOT REWRITE
IT.** The new finalised view is the old finalised view with the newly-blessed
events folded on top — `Era.resolve_resumes_final`'s shape, one axis over: there
the pending suffix resumes from the finalised prefix, here a *later
announcement* resumes from the earlier one.

This is the exact sense in which a finalisation certificate remains sound for
the view it was about: what it reported is still a state the protocol passes
through. It is **not** a licence to reuse the certificate at the new cut set —
§5.1 shows the key changes, so the licence is never claimed. -/
theorem honest_announcement_resumes_the_finalised_view {cuts cuts' : List Era.Cut}
    (h : HonestExtension cuts cuts') (log : List Era.Event) :
    Era.resolveFinal cuts' log
      = (Era.execOrder cuts' (newlyFinal cuts cuts' log)).foldl Era.applyEvent
          (Era.resolveFinal cuts log) := by
  have hpre : Era.execOrder cuts'
        ((log.filter (Era.finalized cuts')).filter (Era.finalized cuts))
      = Era.execOrder cuts (log.filter (Era.finalized cuts)) := by
    refine Era.sorted_unique (Era.pairwise_execOrder cuts' _) ?_ ?_
    · refine pairwise_imp_mem ?_ (Era.pairwise_execOrder cuts (log.filter (Era.finalized cuts)))
      intro a ha b hb hab
      have ha' := (List.mem_filter.mp (Era.mem_execOrder.mp ha)).2
      have hb' := (List.mem_filter.mp (Era.mem_execOrder.mp hb)).2
      exact (elt_agree h ha' hb').mpr hab
    · intro b
      rw [Era.mem_execOrder, Era.mem_execOrder, List.mem_filter, List.mem_filter,
        List.mem_filter]
      constructor
      · rintro ⟨⟨hb1, _⟩, hb3⟩
        exact ⟨hb1, hb3⟩
      · rintro ⟨hb1, hb2⟩
        exact ⟨⟨hb1, finalized_mono h hb2⟩, hb2⟩
  show (Era.execOrder cuts' (log.filter (Era.finalized cuts'))).foldl Era.applyEvent
      Era.initView = _
  rw [Era.execOrder_split_by cuts' (Era.finalized cuts) (fun a b ha hb => honest_cross h a b ha hb)
    (log.filter (Era.finalized cuts')), List.foldl_append, hpre]
  rfl

/-- **An honest announcement that finalises nothing new changes nothing.** The
corollary a replica actually uses: the arbiter spoke, none of my delivered
events was newly blessed, my finalised view is untouched. -/
theorem honest_silent_announcement_keeps_the_view {cuts cuts' : List Era.Cut}
    (h : HonestExtension cuts cuts') {log : List Era.Event}
    (hnone : ∀ e ∈ log, Era.finalized cuts' e = true → Era.finalized cuts e = true) :
    Era.resolveFinal cuts' log = Era.resolveFinal cuts log := by
  have hnil : newlyFinal cuts cuts' log = [] := by
    refine Era.filter_nil_of_false (fun e he => ?_)
    have hm := List.mem_filter.mp he
    show (!Era.finalized cuts e) = false
    rw [hnone e hm.1 hm.2]
    rfl
  rw [honest_announcement_resumes_the_finalised_view h log, hnil]
  rfl

/-! ### §5.1 What the arbiter's announcement does to the certificate -/

theorem honest_setup_to_later : HonestExtension Era.setupCuts Era.laterCuts := by decide

/-- Epoch 2 newly finalises exactly Bob's demote — so the resumption theorem's
fold is over a non-empty list and the extension below is a real one, not a
restatement of an equality. -/
theorem newlyFinal_setup_later :
    newlyFinal Era.setupCuts Era.laterCuts Era.duelLog = [Era.e5] := by decide

/-- The concrete resumption: the finalised view under `laterCuts` is the
finalised view under `setupCuts` with `e5` executed on top. -/
theorem honest_announcement_is_an_extension :
    Era.resolveFinal Era.laterCuts Era.duelLog
      = (Era.execOrder Era.laterCuts (newlyFinal Era.setupCuts Era.laterCuts Era.duelLog)).foldl
          Era.applyEvent (Era.resolveFinal Era.setupCuts Era.duelLog) :=
  honest_announcement_resumes_the_finalised_view honest_setup_to_later Era.duelLog

/-- **The announcement that finalises nothing I hold leaves my view alone** —
`honest_silent_announcement_keeps_the_view` at `wPre`: epoch 2 blesses event `5`,
which this replica has not delivered, so its finalised view is unchanged. -/
theorem silent_announcement_keeps_the_view : finalView wAhead = finalView wPre :=
  honest_silent_announcement_keeps_the_view honest_setup_to_later (by decide)

/-- ⚠ **…and it revokes the licence anyway.** The view did not move and the
certificate is now refused: something the arbiter has blessed is in flight, which
is precisely the `Settled` clause. This is what "sound for the view so far"
amounts to in practice — the old *answer* stands, the old *licence* does not, and
the two facts are separate. -/
theorem a_silent_announcement_keeps_the_view_and_revokes_the_licence :
    finalView wAhead = finalView wPre ∧ Settled wPre ∧ ¬ Settled wAhead :=
  ⟨silent_announcement_keeps_the_view, settled_wPre, by decide⟩

theorem announcement_wAll_wAheadAll : Announcement wAll wAheadAll :=
  ⟨by decide, fun _ => Iff.rfl, fun _ he => he, by decide⟩

/-- ⚠ **QUIESCENCE DOES NOT CLOSE THE CUT AXIS.** `wAll` has delivered its whole
pool — every event that exists is in its log — and one announcement later its
*finalised* view has changed: Alice was an Admin in it and is a Reader now. So
the certificate of §3 is sound for `Delivery` and unsound for `Announcement`,
and the strongest delivery-side premise available does not repair it: `wAll`
already has quiescence, which implies `Settled` and everything below it. The
announcement axis has no pool to be settled against. -/
theorem announcement_moves_the_finalised_view :
    Quiesced wAll ∧ Settled wAll
      ∧ ¬ Evidence.FreeTermination Announcement finalView wAll := by
  refine ⟨quiesced_wAll, settled_of_quiesced quiesced_wAll, fun h => ?_⟩
  have hmv := h wAheadAll announcement_wAll_wAheadAll
  have hrole : (finalView wAheadAll).role Era.alice = (finalView wAll).role Era.alice :=
    congrArg (fun v => v.role Era.alice) hmv
  exact absurd hrole (by decide)

/-- **An announcement changes the name.** The cut set is a component of the key,
so a genuine announcement never produces key equality — `key_licenses_reuse`
cannot fire across it, and the old certificate is not *reused*, it is re-filed.
That is the whole answer to "is the old certificate still sound after a new
cut": its verdict about the old finalised region stands
(`honest_announcement_resumes_the_finalised_view`), and it is no longer a
verdict about the current one. -/
theorem an_announcement_changes_the_name : eraKey wAll ≠ eraKey wAheadAll := by
  intro h
  exact absurd (congrFun (congrArg Prod.fst h) (2, 5)) (by decide)

/-! ### §5.2 The first Byzantine seam: a backdated announcement -/

/-- ⚠ **A BACKDATED CUT ROLLS A FINALISED VERDICT BACK.** `laterCuts` has
finalised Bob's demote, and the finalised view says Alice is a Reader and Bob an
Admin. One further record — event `4` announced into epoch `1`, *below* the
epoch `2` already announced — and the finalised view says the opposite: Alice
Admin, Bob Reader. Not a new answer on top of an old one; the old one **undone**.

`HonestExtension` is exactly what fails, and it fails on the clause that does
the work in `honest_cross`: the new record's epoch does not outrank the
announced ones, so the event it blesses lands in the middle of the finalised
order instead of at its end. This is §5.1's backdating, priced: an equivocating
arbiter cannot cause divergence (`Era.resolve_same_sets` holds with no honesty
hypothesis) and it **can** cause rollback. -/
theorem backdated_cut_rewrites_the_finalised_view :
    (Era.resolveFinal Era.laterCuts Era.duelLog).role Era.alice = Era.reader
      ∧ (Era.resolveFinal Era.laterCuts Era.duelLog).role Era.bob = Era.admin
      ∧ (Era.resolveFinal (Era.advance Era.laterCuts 1 [4]) Era.duelLog).role Era.alice
          = Era.admin
      ∧ (Era.resolveFinal (Era.advance Era.laterCuts 1 [4]) Era.duelLog).role Era.bob
          = Era.reader
      ∧ ¬ HonestExtension Era.laterCuts (Era.advance Era.laterCuts 1 [4]) :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

/-- The premise is a floor and behaves like one: satisfied by one real
announcement and refuted by another, so it is a genuine restriction on the
arbiter and not a fact about announcements. -/
theorem honest_extension_is_satisfiable_and_refutable :
    HonestExtension Era.setupCuts Era.laterCuts
      ∧ ¬ HonestExtension Era.laterCuts (Era.advance Era.laterCuts 1 [4]) :=
  ⟨honest_setup_to_later, by decide⟩

/-! ## §6. The second Byzantine seam: an event born finalised.

`Era.lean` says event ids stand in for hashes and that "no uniqueness premise is
needed — two distinct events sharing an id are still totally ordered by the
remaining fields". For `resolve_same_sets` that is exactly right: a collision
costs determinism nothing. For **finality** it is not right, and §6 exhibits the
difference. A cut names an *id*; an event created afterwards carrying an
already-announced id is finalised the instant it is issued. It does not arrive
by delivery and it does not need a dishonest arbiter — it needs only that ids
are forgeable, which is what dropping §2's recursive hash linking costs. -/

/-- A second event carrying event id `5`, which `laterCuts` has already
announced into epoch `2`: Alice demotes Bob, where `Era.e5` was Bob demoting
Alice. -/
def eForged : Era.Event := Era.demoteEv 5 Era.alice Era.bob Era.reader

/-- The forged event, issued and delivered. -/
def wForged : EraWorld :=
  ⟨Era.laterCuts, Era.duelLog ++ [eForged], Era.duelLog ++ [eForged]⟩

theorem issuance_wAheadAll_wForged : Issuance wAheadAll wForged :=
  ⟨fun _ => Iff.rfl, by decide, by decide, by decide⟩

/-- ⚠ **AN EVENT BORN FINALISED REWRITES THE FINALISED VIEW.** `wAheadAll` is
quiesced, settled, and its arbiter is perfectly honest — the cut set does not
move at all. One newly *issued* event, carrying an id the arbiter announced
before that event existed, is finalised on arrival, executes inside the
finalised prefix, and reverses the duel.

So the certificate of §3 is unsound for `Issuance` as well as for
`Announcement`, and for a different reason: not the arbiter acting, but a cut
naming an id rather than an event. ⟨UNDONE⟩ in the boundary — the repair is
§2's hash linking, which this miniature drops by design. -/
theorem an_event_born_finalised_rewrites_the_view :
    Era.finalized Era.laterCuts eForged = true
      ∧ (finalView wAheadAll).role Era.alice = Era.reader
      ∧ (finalView wAheadAll).role Era.bob = Era.admin
      ∧ (finalView wForged).role Era.alice = Era.admin
      ∧ (finalView wForged).role Era.bob = Era.reader
      ∧ ¬ Evidence.FreeTermination Issuance finalView wAheadAll := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, fun h => ?_⟩
  have hmv := h wForged issuance_wAheadAll_wForged
  have hrole : (finalView wForged).role Era.alice = (finalView wAheadAll).role Era.alice :=
    congrArg (fun v => v.role Era.alice) hmv
  exact absurd hrole (by decide)

/-! ## §7. `Holes.Stable`, inhabited by the Era instance.

`Holes.lean` §6: *"`Era.lean`'s arbiter cut is the intended implementing
instance of the input-side licence (`Era.final_view_immune`: a finalised prefix
stops moving); the transport from Era's event lists into a `Stable` hypothesis
here is named in the boundary as unbuilt, and until it is built the instance is
a design intention rather than a theorem."*

§7 builds it. The `Partial` is a single user's role in the finalised view, the
`Arriving` predicate is "what a delivery may report", and the licence is §3's
certificate. `Holes.seal_survives_stable` then runs unchanged. -/

/-- The answer a replica is about to collapse: user `u`'s role in the finalised
view, as a `Holes.Partial`. A singleton by construction, which is what makes the
seal below a real one. -/
def roleAnswer (u : Nat) (w : EraWorld) : Holes.Partial Nat :=
  fun r => decide ((finalView w).role u = r)

/-- **What may still arrive**, at Era's carrier: the answers a delivery may
report. `Holes.lean` §6 left this abstract "precisely because" a freeze, a
causal cut and an arbiter cut discharge it differently; this is the arbiter-cut
discharge. -/
def arriving (w : EraWorld) (u : Nat) : Holes.Partial Nat → Prop :=
  fun Q => ∃ t, Delivery w t ∧ Q = roleAnswer u t

/-- …and the same for the axis that breaks. -/
def arrivingCut (w : EraWorld) (u : Nat) : Holes.Partial Nat → Prop :=
  fun Q => ∃ t, Announcement w t ∧ Q = roleAnswer u t

/-- **THE ARBITER'S CUT LICENSES THE COLLAPSE.** `Holes.Stable`, discharged at a
concrete Era `Arriving` by §3's certificate. This is the transport two files
named as unbuilt. -/
theorem era_cut_licenses_the_collapse {w : EraWorld} (hs : Settled w) (u : Nat) :
    Holes.Stable (arriving w u) (roleAnswer u w) := by
  rintro Q ⟨t, hd, rfl⟩
  have hft : roleAnswer u t = roleAnswer u w := by
    unfold roleAnswer
    rw [finalView_immune hs hd]
  rw [hft]
  exact merge_idem _

/-- The answer is sealed: every candidate it holds is the role it reports. -/
theorem era_answer_seals (u : Nat) (w : EraWorld) :
    Holes.SealsTo (roleAnswer u w) ((finalView w).role u) :=
  fun _ hb => (of_decide_eq_true hb).symm

/-- **The seal survives every arrival** — `Holes.seal_survives_stable`, run on
the Era licence. A replica at a settled world may collapse the finalised role to
a single answer and nothing a delivery brings falsifies it. -/
theorem era_seal_survives {w : EraWorld} (hs : Settled w) (u : Nat) :
    ∀ Q, arriving w u Q → Holes.SealsTo (roleAnswer u w ⊔ Q) ((finalView w).role u) :=
  Holes.seal_survives_stable (era_cut_licenses_the_collapse hs u) (era_answer_seals u w)

/-- ⚠ **AND IT IS NOT THE TRIVIAL LICENCE.** `Holes.stable_of_subsumed` is
stability against arrivals that carry no news (`V ⊑ W` in the *inputs*), and
`Holes.lean` says so: "a real instance and a weak one. The licence worth having
is a statement about arrivals that have **not** happened yet".

This is that one, and the non-triviality is a claim about the inputs, not the
answers. The arriving world holds two events `wPre` has never delivered, and the
arrival is **observable**: the same carrier's full view moves under it, demoting
Bob. The *finalised* answer does not move — which is the theorem, not the
triviality. -/
theorem the_era_licence_is_not_the_trivial_one :
    Settled wPre
      ∧ ¬ Quiesced wPre
      ∧ arriving wPre Era.bob (roleAnswer Era.bob wAll)
      ∧ Era.e4 ∉ wPre.log ∧ Era.e4 ∈ wAll.log
      ∧ Era.e5 ∉ wPre.log ∧ Era.e5 ∈ wAll.log
      ∧ (fullView wAll).role Era.bob ≠ (fullView wPre).role Era.bob
      ∧ roleAnswer Era.bob wAll = roleAnswer Era.bob wPre := by
  refine ⟨settled_wPre, by decide, ⟨wAll, delivery_wPre_wAll, rfl⟩, by decide, by decide,
    by decide, by decide, by decide, ?_⟩
  unfold roleAnswer
  rw [finalView_immune settled_wPre delivery_wPre_wAll]

/-- ⚠ **The cut axis breaks the seal.** At the *quiesced* world `wAll` the same
licence fails on the announcement axis: the arbiter's next record makes Alice a
Reader in the finalised view, and the merged answer is no longer the sealed
one. -/
theorem the_cut_axis_breaks_the_seal :
    ¬ Holes.Stable (arrivingCut wAll Era.alice) (roleAnswer Era.alice wAll) := by
  intro h
  have hst := h (roleAnswer Era.alice wAheadAll) ⟨wAheadAll, announcement_wAll_wAheadAll, rfl⟩
  exact absurd (congrFun hst Era.reader) (by decide)

/-- ⚠ **…and the unlicensed collapse is a lie, concretely.**
`Holes.unstable_seal_clash` at the Era carrier: a replica that sealed "Alice is
an Admin" against the announcement axis has asserted something the merged answer
refutes — not a stale answer, a wrong one. -/
theorem the_unlicensed_collapse_is_a_lie :
    ¬ Holes.SealsTo (roleAnswer Era.alice wAll ⊔ roleAnswer Era.alice wAheadAll)
        Era.admin := by
  intro h
  exact absurd (h Era.reader (by decide)) (by decide)

/-! ## §8. The row.

`CertificateScope.the_key_table` and `the_certificate_table` have two columns;
this is Era's line in both, plus the axis verdicts that make it a line and not a
restatement. -/

/-- **THE ERA ROW.** The key column: `(cuts, finalised delivered, finalised
issued)` is sufficient on wellformed worlds, and dropping the pool component is
not. The certificate column: `Settled` is readable from the key, is satisfiable
and refutable, and is a sound certificate for the finalised view under
**delivery** — at a world where the *full* view is not stable — while it is
unsound under **announcement** at a quiesced world, and unsound under
**issuance** at a quiesced world with an honest arbiter. The cut axis is
governed instead by the honest-extension resumption. And the licence `Holes.lean`
§6 assumed is inhabited by this certificate, and broken by the cut axis. -/
theorem the_era_certificate_row :
    SufficientKeyOn Wf eraKey finalView Delivery
      ∧ ¬ SufficientKeyOn Wf finalPoolFreeKey finalView Delivery
      ∧ KeyCertSound eraKey finalView Delivery settledCert
      ∧ (∀ w : EraWorld, settledCert (eraKey w) ↔ Settled w)
      ∧ (settledCert (eraKey wPre) ∧ ¬ settledCert (eraKey wAhead))
      ∧ Evidence.FreeTermination Delivery finalView wPre
      ∧ ¬ Evidence.FreeTermination Delivery fullView wPre
      ∧ ¬ Evidence.FreeTermination Delivery finalView wAhead
      ∧ ¬ Evidence.FreeTermination Announcement finalView wAll
      ∧ ¬ Evidence.FreeTermination Issuance finalView wAheadAll
      ∧ (∀ cuts cuts' : List Era.Cut, HonestExtension cuts cuts' →
          ∀ log : List Era.Event, Era.resolveFinal cuts' log
            = (Era.execOrder cuts' (newlyFinal cuts cuts' log)).foldl Era.applyEvent
                (Era.resolveFinal cuts log))
      ∧ Holes.Stable (arriving wPre Era.bob) (roleAnswer Era.bob wPre)
      ∧ ¬ Holes.Stable (arrivingCut wAll Era.alice) (roleAnswer Era.alice wAll) :=
  ⟨eraKey_sufficient_on_wf, finalPoolFreeKey_not_sufficient,
   era_finalisation_is_a_sound_certificate, settledCert_iff,
   the_certificate_is_satisfiable_and_refutable,
   era_final_view_free_terminating settled_wPre,
   era_stops_before_quiescence.2.2.2,
   delivery_alone_does_not_license_the_finalised_view.2,
   announcement_moves_the_finalised_view.2.2,
   an_event_born_finalised_rewrites_the_view.2.2.2.2.2,
   fun _ _ h log => honest_announcement_resumes_the_finalised_view h log,
   era_cut_licenses_the_collapse settled_wPre Era.bob,
   the_cut_axis_breaks_the_seal⟩

end Uwueave.EraCertificate

