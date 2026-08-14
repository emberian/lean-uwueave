/-
# Uwueave.WorldFuture — a future is indexed by the WORLD, not by the state.

`Evidence.lean` defines its two future relations over **states**:
`ExtensionFuture : ResultEvidence α → ResultEvidence α → Prop`, and a
pool-parameterised `DeliveryFuture pool : ResultEvidence α → …`. This file
says why the first shape cannot be right for delivery, builds the carrier that
is, and relates the two by theorem rather than replacing one with the other.

## Origin: codex's second review, third P0

The diagnosis is **codex's**, from a second external review of this library
(the first produced `Evidence.lean`'s two corrections). In its words: two
replicas can have the *same materialized state* while differing in which
events have been issued-but-not-delivered, their causal frontier, whether a
producer sealed an epoch, the accepted roster, outstanding capabilities, and
known merge bases. So

> `DeliveryFuture s t` cannot in general be defined from `s : State` alone,

and an exactness certificate that escapes its frontier/epoch context is
unsound under reuse. This file is the execution; the credit for the diagnosis
is not ours.

The correction lands on a shape `Evidence.lean` had already half-admitted:
`Evidence.DeliveryFuture` takes the **pool** as an explicit parameter, so that
file was already not state-indexed at that point — what it lacked was a place
to put the parameter, and a theorem saying the parameter is not recoverable
from the state. `World` is that place and §3 is that theorem.

## ⚠ `World` here is NOT `Holes.World` — two different things, one word

`Holes.World` is a **candidate valuation**: one internally-consistent
possibility for what every replicated register holds (`List Val`, read by
`Holes.read`). A replica's uncertainty is a *set* of them.

`WorldFuture.World` is a **replica's epistemic situation**: the materialized
state it has, plus the context that state was materialized in — what has been
issued, who is on the roster, what the producer sealed, which epoch. It is not
a valuation and it is not a set of valuations.

They compose without colliding — the candidate values inside a
`WorldFuture.World`'s state may perfectly well be an image of `Holes.World`s
under `Holes.evalSet`, which is what `Evidence.fromWorlds` builds — but they
are different types with different jobs and the shared name is an accident of
English. Nothing below reads a `Holes.World`.

## The headline — the separation (§3)

`delivery_futures_differ`:

    observe wQuiesced = observe wPending          (identical materialized state)
    DeliveryFuture wPending  wDelivered
    ¬ DeliveryFuture wQuiesced wDelivered

Two worlds whose materialized states are **equal** — same candidates, same
frontier, same held certificates — and whose delivery futures differ, because
in one of them `bob` has issued `49` and it has not arrived yet, and in the
other `bob` has issued nothing. The corollary is the theorem that stops future
semantics collapsing back to `S → S → Prop`:

  * `delivery_future_is_not_state_indexed` — there is **no** relation
    `F : Future (ResultEvidence α)` with `DeliveryFuture w v ↔ F (observe w) (observe v)`;
  * `delivery_stability_is_not_state_indexed` — and the value-level version:
    no predicate on states decides whether the rendered answer is
    delivery-stable. It is stable at `wQuiesced` and not at `wPending`, and
    those two are indistinguishable through `observe`.

⚠ **And it is the pool, not the frontier or the epoch, that separates them**
(`frontier_and_epoch_do_not_separate`). The two witness worlds agree on
frontier, on held certificates, on roster and on epoch. Codex's remedy
"index by the world (or by the frontier/epoch)" is right in its first form and
**insufficient in its second**, at least at this witness: a certificate keyed
on frontier-and-epoch is reusable across exactly the pair that breaks it.

## The soundness consequence (§5) — what this is for

An **exactness certificate** is a licence to stop saying "pending". §5 asks
what it may be indexed by, and answers with a pair:

  * `quiescence_is_a_sound_certificate` — quiescence (`observe w = pool w`, a
    fact about the *world*) soundly licenses "the rendered answer will not move
    under delivery";
  * ⚠ `no_sound_state_cert_accepts_openW` — **no** sound *state*-indexed
    certificate may accept the state `openW`, even though a replica standing at
    `wQuiesced` has correctly verified that at that state, in that world,
    nothing is left to deliver. The verification was true where it was made and
    is false one world over, and the certificate carries nothing that can tell
    the difference.

That is the reuse unsoundness in one line: **a certificate that escapes its
world is a true statement filed under the wrong key.** The repair is not a
stronger check — it is the *same* check with the world in the index
(`certificate_reuse_is_unsound` states both halves together).

## The relationship to `Evidence.lean` (§4) — projection, image, transfer

`Evidence.lean` is not superseded and is not edited. `observe` is a
projection, and:

  * **The state-level relations are exactly the IMAGE of the world-level ones.**
    `extension_image` and `delivery_image` are iffs, not one-way soundness
    claims. So `Evidence.ExtensionFuture` is the loosest sound state-level
    reading of the world-level relation, which is the right thing for it to be.
  * **The extension image is witnessed by *quiesced* worlds**
    (`extension_image` carries `Quiesced w ∧ Quiesced v`). That is the whole
    diagnosis in one clause: the state level only ever sees worlds whose pool
    *is* their state, so the pool is invisible there by construction, not by
    oversight.
  * **Most of `Evidence.lean` transfers for free — and one thing does not.**
    This was checked, not assumed, and the check found something. Free:
    `FreeTermination`, `SoundEvaluator`, `divergent_futures_force_nonexact`
    (`no_exact_at_wPending`) and `exact_sound`
    (`exact_survives_sealed_futures`) are stated over an arbitrary `Future S`
    and instantiate at `S := World α` unchanged. Free by **pullback along
    `observe`**, one lemma rather than a reproof: the results about
    `ResultEvidence` specifically — `render_sound` becomes `renderW_sound` via
    `sealed_projects`.

    ⚠ **Not free: completeness.** `renderW_complete` holds only from a
    wellformed world with a known roster, and the unconditional structure
    `Evidence.CanonicalEvaluator` is **refuted** at this carrier
    (`renderW_not_canonical`). Completeness is the one property that reads the
    *whole* future set, so a world with no futures satisfies it vacuously at
    every value at once — and `World α` contains such worlds, because
    wellformedness is a hypothesis here and not a property of the type.
    `sealed_future_realized` shows nothing else was lost: every state-level
    sealed future is realized by a world-level one from any wellformed world.
    So the gap is exactly the ill-formed carrier junk, and it is named rather
    than papered over.
  * ⚠ **One reading of `Evidence.lean` does not survive, and it is a reading,
    not a theorem.** `Evidence.quiesced_delivery_stable` says every query is
    stable under `DeliveryFuture s` — the delivery relation *with the pool
    instantiated at `s` itself*. The theorem is true and its docstring is
    careful ("a replica that has delivered the whole pool"); `futures_not_
    interchangeable` says "at `openW`, **taken as its own pool**". What the
    world level adds is the price of that phrase: taking a state as its own
    pool is the hypothesis `Quiesced`, it is a fact about the world, and
    `not_quiesced_wPending` exhibits a world with that exact state where it is
    false. Nothing in `Evidence.lean` is retracted; what was a parenthetical
    is now a hypothesis with a refutation.

## Honest boundary

⟨TERMINAL⟩ = a theorem of the model; ⟨UNDONE U-0153⟩ = work wearing a caveat's
clothes.

  * **No deployed network, scheduler proof, or time.** ⟨TERMINAL for this
    file's question, ⟨UNDONE U-0154⟩ as a system model⟩ A delivery future here is a
    *relation between two worlds*, not a run of a protocol. The successor
    `Uwueave.Temporal` now supplies the missing formal run layer:
    `WorldAdapter.pendingDeliveryTrace_adjacent` is an infinite adjacent trace
    whose first step is the genuine `wPending`-to-`wDelivered` delivery;
    `RenderAdapter.fair_bob_delivery_exits_pending` connects weak fairness to
    a real pending exit; and `WorldAdapter.starvedPendingTrace_not_weakFair`
    proves the constant pending trace valid but unfair. The marker remains:
    no network implementation is proved fair, and nothing models loss,
    reordering, partition, retry/retransmission, latency, timeouts, or
    wall-clock bounds. The separation in §3 still answers what a future *may*
    be; `Temporal` states explicitly which scheduler premise makes one occur.
  * **This carrier drops two of codex's six components; the successor restores
    them.** `Uwueave.WorldContext` adds outstanding active grants, a
    downward-closed `CausalReach.Cut`, and a known version base/head in a real
    history, with projection and conditional lift theorems back to this world.
    `Uwueave.AuthenticatedWorldContext` now closes the model-level successor
    boundary with accepted-and-issued signed typed-position claims, exact
    signed world/value/position binding, signed-decoded origin/version checks,
    authenticated lawful frontier progress, and grow-only capability-use
    receipts. ⟨UNDONE U-0155 at deployment boundaries⟩
    the decoder and signature security premise remain external, and
    `ResultEvidence` still carries neither id automatically.
  * **The frontier here is still a flat set of sources.**
    `Uwueave.Frontier` now supplies the Timely-style antichain whose advance
    retires a timestamp range and a narrow theorem transporting complete,
    settled worlds to stability of `Evidence.values`. ⟨UNDONE U-0156 for this carrier
    and deployment⟩ `World.frontier` remains a `GSet Source`, and timestamps or
    authentication records are not stored in `ResultEvidence`.
    `Uwueave.AuthenticatedFrontier` and
    `Uwueave.AuthenticatedWorldContext` authenticate proof-level progress and
    bind it to a lawful decoded advance, but no runtime generates that progress
    or discharges the deployed signature premise. Full `render` stability is
    not claimed. `roster` bounds accepted membership, but a roster is not an
    antichain.
  * **A seal is still trusted, not verified.** ⟨UNDONE U-0157⟩ `epoch` and `sealed`
    are a producer's announcement, exactly as `Era.advance` announces a cut
    unconditionally. What is *new* here and not in `Evidence.lean` is that the
    announcement is **priced**: `no_closure_within_an_epoch` proves no
    extension future closes a source without advancing the epoch, so `Closed`
    can never be earned by delivery or by application writes alone. That makes
    the trust in the arbiter a load-bearing hypothesis with a theorem attached
    rather than an unremarked one; it does not make the arbiter honest.
  * **`Wf` and `RosterKnown` are hypotheses, not invariants.** ⟨UNDONE U-0158⟩
    Wellformedness (`observe w ⊑ pool w`) is carried as a side condition on the
    future relations and proved for the concrete witnesses. No theorem says a
    running system's worlds are wellformed, because there is no running system
    here — that is what a state machine over these worlds would establish and
    none is built.
  * **`renderW` is noncomputable.** ⟨TERMINAL at this carrier⟩ It is
    `Evidence.render` composed with a projection, and `render` quantifies over
    an unbounded value type. `Classical.choice` is inside the audit floor.
  * **The separation is one witness, not a classification.** ⟨UNDONE U-0159⟩ §3 proves
    that *some* pair of worlds is separated by the pool, which is what refutes
    the collapse. It does **not** characterise which state/world pairs are
    separated, or give a decidable test for when a state-indexed reading is
    safe. `Quiesced` is one sufficient condition and there is no claim it is
    necessary.

## Literature — what each is for here

  * **Free Termination** (Power, Koutris, Hellerstein, arXiv:2502.00222) — the
    state-relative finality (Def. 3) `FreeTermination` names, imported from
    `Evidence.lean` unchanged. Their §1.1 gap — CRDTs give *quiescence*, not
    free termination, because you cannot locally tell you have heard everything
    — is precisely what §3 makes formal: quiescence is not a function of the
    state, so a replica cannot read it off what it holds.
  * **Timely progress tracking** (Brun, Decova, Lattuada, Traytel, ITP 2021) —
    the frontier as a bound on what may still arrive. `pool` is that bound made
    explicit as a component of the world rather than an argument threaded
    through a relation.
  * **ERA** (Dougal, PaPoC 2026; `Era.lean`) — the epoch and the arbiter's cut.
    `no_closure_within_an_epoch` is `Era.final_view_immune`'s discipline read at
    this carrier: the finalised prefix stops moving, and nothing that is not the
    arbiter may finalise.
-/
import Uwueave.Evidence

namespace Uwueave.WorldFuture

open Uwueave Uwueave.Catalog

universe u v

/-! ## §1. The world — the materialized state, and the context it sits in.

A `World` is what a replica **is**, as opposed to what it **holds**. It holds
`state : Evidence.ResultEvidence α` — the delivered candidates, the frontier
of sources still owed, and the closure certificates in hand. It *is* that
state together with four facts that no replica can read off it:

  * `issued` — every event issued anywhere in the system. The delivery pool:
    what may still arrive without anyone doing anything new.
  * `roster` — the accepted membership. Who may speak at all; the bound on how
    far the frontier can grow.
  * `sealed` — the closure certificates the producer has sealed. The pool for
    the certificate component, exactly as `issued` is for the candidates.
  * `epoch` — the producer's epoch counter. A new seal costs an advance (§2).

`observe` forgets the last four. That forgetting is the subject of this file.

The three pools line up componentwise with the three components of the state,
so they collect into one `ResultEvidence` — `pool w` — and wellformedness is
the single clause **`observe w ⊑ pool w`**: what a replica has materialized is
below what exists to be materialized. -/

/-- **A world.** The materialized state, plus the context that state was
materialized in. ⚠ Not `Holes.World`, which is a candidate valuation — see the
header. -/
structure World (α : Type u) where
  /-- What the replica has materialized: delivered candidates, frontier, held
  certificates. This is exactly `Evidence.lean`'s carrier. -/
  state : Evidence.ResultEvidence α
  /-- Every event issued anywhere — the delivery pool. -/
  issued : GSet (α × Evidence.Source)
  /-- The accepted roster: who may speak at all. -/
  roster : GSet Evidence.Source
  /-- The closure certificates the producer has sealed. -/
  sealed : GSet Evidence.Source
  /-- The producer's epoch counter. -/
  epoch : Nat

/-- **The projection.** What a replica can read off itself: its materialized
state, and nothing about the world it is in. Every state-level notion in
`Evidence.lean` is a notion about this value. -/
def observe {α : Type u} (w : World α) : Evidence.ResultEvidence α := w.state

/-- **The pool**: the three issuance bounds, collected into the same shape as
the state so that "below what exists" is one `⊑`. -/
def pool {α : Type u} (w : World α) : Evidence.ResultEvidence α :=
  (w.issued, w.roster, w.sealed)

/-- The events this replica has delivered — `Evidence.candidates` of the
materialized state, renamed to say what it is at this carrier. -/
abbrev delivered {α : Type u} (w : World α) : GSet (α × Evidence.Source) :=
  Evidence.candidates (observe w)

/-- The frontier: sources this replica is still owed. `Evidence.obligations`. -/
abbrev frontier {α : Type u} (w : World α) : GSet Evidence.Source :=
  Evidence.obligations (observe w)

/-- The certificates in hand. `Evidence.certificates`. -/
abbrev held {α : Type u} (w : World α) : GSet Evidence.Source :=
  Evidence.certificates (observe w)

/-- **Wellformed**: what has been materialized is below what exists to be
materialized — delivered ⊆ issued, frontier ⊆ roster, held ⊆ sealed, in one
componentwise `⊑`. Carried as a hypothesis, not an invariant (see boundary). -/
def Wf {α : Type u} (w : World α) : Prop := observe w ⊑ pool w

/-- **Quiesced**: the state *is* the pool. Everything issued has been
delivered, the whole roster is known, every seal is in hand. This is the
hypothesis `Evidence.lean` writes as "taken as its own pool", here a fact about
the world — and §3 exhibits a world with the same state where it is false. -/
def Quiesced {α : Type u} (w : World α) : Prop := observe w = pool w

/-- **The replica has heard the whole roster.** The converse inclusion to
`Wf`'s middle component: every accepted source is already an obligation, so no
member can appear as *news*. This is what `Evidence.SealedFuture`'s membership
clause needs, and at the world level it is a fact about the **roster**. -/
def RosterKnown {α : Type u} (w : World α) : Prop := w.roster ⊑ frontier w

theorem wf_of_quiesced {α : Type u} {w : World α} (h : Quiesced w) : Wf w := by
  rw [Wf, h]
  exact leq_refl _

/-! ## §2. The two futures, at the world level.

Both are `Evidence.lean`'s relation on the *observed* part, conjoined with what
the context is permitted to do — and the whole difference between them is that
clause:

  * **delivery** — the context does not move at all (`pool v = pool w`,
    `v.epoch = w.epoch`). Only already-issued evidence arrives. `Evidence.
    DeliveryFuture`'s pool parameter is read off the world instead of supplied.
  * **extension** — the context may grow: new events issued, new members
    admitted, new seals announced. With one price attached: a seal that was not
    already sealed costs an **epoch advance** (`no_closure_within_an_epoch`).

`SealedFuture` is the extension future under a closed roster, which is where
`Evidence.render` is sound. Its two clauses are both roster facts here, which
is the world-level explanation of `Evidence.render_retracts_when_a_new_source_
appears`: that retraction is a **roster growth**. -/

/-- **The delivery future.** Only already-issued evidence arrives; the context
is frozen. The pool is `pool w` — read off the world, not handed in. -/
def DeliveryFuture {α : Type u} (w v : World α) : Prop :=
  Evidence.DeliveryFuture (pool w) (observe w) (observe v)
    ∧ pool v = pool w
    ∧ v.epoch = w.epoch

/-- **The extension future.** New application events, new roster members and
new seals are all permitted — the pool may grow — and the future world is
itself wellformed. A seal that is genuinely new costs an epoch advance. -/
def ExtensionFuture {α : Type u} (w v : World α) : Prop :=
  Evidence.ExtensionFuture (observe w) (observe v)
    ∧ pool w ⊑ pool v
    ∧ observe v ⊑ pool v
    ∧ w.epoch ≤ v.epoch
    ∧ (∀ o, w.sealed o = false → v.sealed o = true → w.epoch < v.epoch)

/-- **The sealed future**: an extension future under a **closed roster**, from
a replica that has already heard the whole roster. Both clauses are roster
facts, and together they are exactly what `Evidence.SealedFuture` asks for
(`sealed_projects`). -/
def SealedFuture {α : Type u} (w v : World α) : Prop :=
  ExtensionFuture w v ∧ v.roster ⊑ w.roster ∧ RosterKnown w

/-- Every delivery future is an extension future — the containment survives the
move to worlds, because "the context did not move" implies "the context only
grew". The seal clause is vacuous: a frozen pool seals nothing new. -/
theorem delivery_is_extension {α : Type u} {w v : World α} (h : DeliveryFuture w v) :
    ExtensionFuture w v := by
  obtain ⟨hd, hp, he⟩ := h
  refine ⟨⟨hd.1, hd.2.2⟩, ?_, ?_, Nat.le_of_eq he.symm, ?_⟩
  · rw [hp]; exact leq_refl _
  · rw [hp]; exact hd.2.1
  · intro o h0 h1
    have hs : v.sealed = w.sealed := congrArg (fun p => p.2.2) hp
    rw [hs] at h1
    exact Bool.noConfusion (h0.symm.trans h1)

/-- **The delivery future is reflexive at a wellformed world** — "nothing
arrived" is a delivery. This is what keeps every `FreeTermination` statement
below from being an empty quantifier: the relation it ranges over is inhabited
wherever wellformedness holds. -/
theorem delivery_refl {α : Type u} {w : World α} (h : Wf w) : DeliveryFuture w w :=
  ⟨⟨leq_refl _, h, Evidence.admits_refl _⟩, rfl, rfl⟩

/-- **A closure costs an epoch.** An extension future that does not advance the
producer's epoch holds no certificate for a source that was not already sealed
— so `Evidence.Closed` is never earned by delivery, and never by application
writes; it is bought from the arbiter, and the epoch counter is the receipt.
This is `Era.lean`'s discipline at this carrier: only the arbiter finalises. -/
theorem no_closure_within_an_epoch {α : Type u} {w v : World α}
    (h : ExtensionFuture w v) (hep : v.epoch = w.epoch) {o : Evidence.Source}
    (h0 : w.sealed o = false) : held v o = false := by
  cases hv : v.sealed o with
  | false =>
    cases hh : held v o with
    | false => rfl
    | true =>
      have hsub := (Holes.gset_leq_iff_subset _ _).mp
        (Evidence.certificates_mono h.2.2.1) o hh
      exact absurd (hsub.symm.trans hv) (by decide)
  | true =>
    have hlt := h.2.2.2.2 o h0 hv
    rw [hep] at hlt
    exact absurd hlt (Nat.lt_irrefl _)

/-- The delivery future projects to `Evidence.DeliveryFuture` **at the pool the
world names** — definitionally, since that is how it was built. -/
theorem delivery_projects {α : Type u} {w v : World α} (h : DeliveryFuture w v) :
    Evidence.DeliveryFuture (pool w) (observe w) (observe v) := h.1

/-- The extension future projects to `Evidence.ExtensionFuture`. -/
theorem extension_projects {α : Type u} {w v : World α} (h : ExtensionFuture w v) :
    Evidence.ExtensionFuture (observe w) (observe v) := h.1

/-- **The sealed future projects too** — and this is the one that needs a proof
rather than a projection. `Evidence.SealedFuture` demands that no obligation
appears that was not already there; at the world level that is the chain
*frontier of `v`* ⊆ *roster of `v`* ⊆ *roster of `w`* ⊆ *frontier of `w`*,
whose three links are wellformedness of the future world, the closed roster,
and `RosterKnown`. Membership closure is a roster fact. -/
theorem sealed_projects {α : Type u} {w v : World α} (h : SealedFuture w v) :
    Evidence.SealedFuture (observe w) (observe v) := by
  refine ⟨h.1.1, fun o ho => ?_⟩
  have h1 : frontier v ⊑ w.roster :=
    leq_trans (Evidence.obligations_mono h.1.2.2.1) h.2.1
  exact (Holes.gset_leq_iff_subset _ _).mp (leq_trans h1 h.2.2) o ho

/-- **Stability under extension implies stability under delivery**, at the
world level — `Evidence.extension_stable_implies_delivery_stable` transported,
by the same one-line argument over the new containment. -/
theorem extension_stable_implies_delivery_stable {α : Type u} {β : Type v} {q : World α → β}
    {w : World α} (h : Evidence.FreeTermination ExtensionFuture q w) :
    Evidence.FreeTermination DeliveryFuture q w :=
  fun v hv => h v (delivery_is_extension hv)

/-- **Quiescence is what "nothing left to deliver" means.** At a quiesced
world, every query that reads only the materialized state is delivery-stable:
the state is already the pool, so by antisymmetry the only reachable
observation is the one in hand.

⚠ Read the quantifier: `q` factors through `observe`. A query that reads the
*world* — "has bob issued anything?" — is not covered and is not stable, which
is the point of §3. -/
theorem quiesced_freeTermination {α : Type u} {β : Type v}
    (q : Evidence.ResultEvidence α → β) {w : World α} (hq : Quiesced w) :
    Evidence.FreeTermination DeliveryFuture (fun v => q (observe v)) w := by
  intro v hv
  have h1 : observe w ⊑ observe v := hv.1.1
  have h2 : observe v ⊑ observe w := by rw [hq]; exact hv.1.2.1
  show q (observe v) = q (observe w)
  rw [leq_antisymm h1 h2]

/-- The rendered view of a world: `Evidence.render` of what it has
materialized. Noncomputable for `render`'s reason. -/
noncomputable def renderW {α : Type u} (w : World α) : Evidence.View α :=
  Evidence.render (observe w)

theorem quiesced_render_stable {α : Type u} {w : World α} (hq : Quiesced w) :
    Evidence.FreeTermination DeliveryFuture (renderW (α := α)) w := by
  intro v hv
  exact quiesced_freeTermination Evidence.render hq v hv

/-! ## §3. THE SEPARATION — two worlds, one state, different futures.

Three worlds over `Evidence.lean`'s own witnesses, so that every fact about the
*states* below is a fact `Evidence.lean` already proved:

  * `wQuiesced` — state `openW`, and the pool is `openW` too. `alice` said
    `47`, `bob` is owed and has said **nothing**. There is nothing to deliver.
  * `wPending` — state `openW`, **identical**, but the pool is `openForkW`:
    `bob` has issued `49` and it has not arrived. There is something to
    deliver, and the replica cannot see that there is.
  * `wDelivered` — state `openForkW`: `bob`'s `49` has arrived.

`observe wQuiesced = observe wPending` is `rfl`. The delivery futures differ.
That is the whole file. -/

/-- **Nothing left to deliver.** State `openW`, pool `openW`. -/
def wQuiesced : World Holes.Val where
  state := Evidence.openW
  issued := Evidence.cand47
  roster := Evidence.srcsAB
  sealed := Evidence.srcsA
  epoch := 0

/-- **The same state, and `bob`'s `49` in flight.** State `openW`, pool
`openForkW`. Indistinguishable from `wQuiesced` by anything the replica holds. -/
def wPending : World Holes.Val where
  state := Evidence.openW
  issued := Evidence.cand4749
  roster := Evidence.srcsAB
  sealed := Evidence.srcsA
  epoch := 0

/-- `bob`'s `49` delivered: state `openForkW`, same pool as `wPending`. -/
def wDelivered : World Holes.Val where
  state := Evidence.openForkW
  issued := Evidence.cand4749
  roster := Evidence.srcsAB
  sealed := Evidence.srcsA
  epoch := 0

/-- **The materialized states are equal, on the nose.** Not "agree on the
values" — the same `ResultEvidence`: same candidates, same frontier, same held
certificates. -/
theorem same_observation : observe wQuiesced = observe wPending := rfl

theorem quiesced_wQuiesced : Quiesced wQuiesced := rfl

theorem wf_wPending : Wf wPending := Evidence.openW_extends_to_openForkW.1

theorem wf_wDelivered : Wf wDelivered := leq_refl _

/-- ⚠ …and `wPending` is **not** quiesced, with the same state. The predicate
`Evidence.lean` writes as "taken as its own pool" is false here. -/
theorem not_quiesced_wPending : ¬ Quiesced wPending := by
  intro h
  have h1 : Evidence.cand47 = Evidence.cand4749 := congrArg Prod.fst h
  exact absurd (congrFun h1 (49, Evidence.bob)) (by decide)

/-- Non-vacuity for `stable_at_wQuiesced`: `wQuiesced` **has** delivery futures
— it is one of its own — so the stability claim quantifies over an inhabited
relation rather than an empty one. Likewise at `wPending`. -/
theorem delivery_refl_witnesses :
    DeliveryFuture wQuiesced wQuiesced ∧ DeliveryFuture wPending wPending :=
  ⟨delivery_refl (wf_of_quiesced quiesced_wQuiesced), delivery_refl wf_wPending⟩

theorem delivery_wPending_wDelivered : DeliveryFuture wPending wDelivered :=
  ⟨⟨Evidence.openW_extends_to_openForkW.1, leq_refl _,
    Evidence.openW_extends_to_openForkW.2⟩, rfl, rfl⟩

/-- ⚠ …and the same step is **not** a delivery future of `wQuiesced`, for the
substantive reason: `(49, bob)` was never issued there, so the clause
`observe v ⊑ pool w` — "you may only deliver what exists" — fails on it. -/
theorem not_delivery_wQuiesced_wDelivered : ¬ DeliveryFuture wQuiesced wDelivered := by
  intro h
  have hb : Evidence.cand4749 ⊑ Evidence.cand47 :=
    Evidence.candidates_mono h.1.2.1
  exact absurd ((Holes.gset_leq_iff_subset _ _).mp hb (49, Evidence.bob) (by decide))
    (by decide)

/-- ⚠ **THE SEPARATION.** Two worlds with *identical* materialized state, and a
world that is a delivery future of one and not of the other.

This is codex's claim made concrete: `DeliveryFuture s t` cannot be defined
from `s : State` alone, because `s` is the same on both sides of this
conjunction and the answer is not. -/
theorem delivery_futures_differ :
    observe wQuiesced = observe wPending
      ∧ DeliveryFuture wPending wDelivered
      ∧ ¬ DeliveryFuture wQuiesced wDelivered :=
  ⟨same_observation, delivery_wPending_wDelivered, not_delivery_wQuiesced_wDelivered⟩

/-- ⚠ **THE COLLAPSE IS IMPOSSIBLE.** There is no state-level relation
whatsoever that reproduces the world-level delivery future — not a clever one,
not an approximate one, none. Any `F` would have to answer the same at
`observe wQuiesced` and `observe wPending`, and the delivery future does not.

This is the theorem that stops future semantics falling back to
`S → S → Prop`. Everything else in this file is what to do about it. -/
theorem delivery_future_is_not_state_indexed :
    ¬ ∃ F : Evidence.Future (Evidence.ResultEvidence Holes.Val),
        ∀ w v : World Holes.Val, DeliveryFuture w v ↔ F (observe w) (observe v) := by
  rintro ⟨F, hF⟩
  have h1 : F (observe wPending) (observe wDelivered) :=
    (hF wPending wDelivered).mp delivery_wPending_wDelivered
  rw [← same_observation] at h1
  exact not_delivery_wQuiesced_wDelivered ((hF wQuiesced wDelivered).mpr h1)

/-! ### The value-level separation

The relational statement above is the sharp one; this is the one an
application feels. `renderW` is delivery-stable at `wQuiesced` — waiting will
change nothing — and not at `wPending`, where `bob`'s `49` turns
`provisional 47` into `forkedOpen`. Same state, opposite verdicts. -/

theorem stable_at_wQuiesced :
    Evidence.FreeTermination DeliveryFuture renderW wQuiesced :=
  quiesced_render_stable quiesced_wQuiesced

theorem not_stable_at_wPending :
    ¬ Evidence.FreeTermination DeliveryFuture renderW wPending := by
  intro hst
  have h := hst wDelivered delivery_wPending_wDelivered
  have h' : Evidence.View.forkedOpen = Evidence.View.provisional (47 : Holes.Val) := by
    rw [← Evidence.render_openForkW, ← Evidence.four_states_inhabited.2.1]
    exact h
  exact absurd h' (Evidence.view_ne_of_tag (by simp [Evidence.viewTag]))

/-- ⚠ **Delivery-stability is not a property of the state.** No predicate on
materialized states decides whether the rendered answer will move under
delivery — the two worlds it would have to separate are equal through
`observe`. An interface that computes "is this settled?" from what the replica
holds is computing something that does not exist. -/
theorem delivery_stability_is_not_state_indexed :
    ¬ ∃ P : Evidence.ResultEvidence Holes.Val → Prop,
        ∀ w : World Holes.Val,
          P (observe w) ↔ Evidence.FreeTermination DeliveryFuture renderW w := by
  rintro ⟨P, hP⟩
  have h1 : P (observe wQuiesced) := (hP wQuiesced).mpr stable_at_wQuiesced
  rw [same_observation] at h1
  exact not_stable_at_wPending ((hP wPending).mp h1)

/-- ⚠ **It is the POOL that separates them — not the frontier, not the epoch.**
The two witness worlds agree on frontier, on held certificates, on roster and
on epoch; they differ only in what has been issued.

So codex's remedy in its second form — "index by the frontier/epoch" — is
**not sufficient at this witness**: a certificate keyed on frontier-and-epoch
is reusable across exactly the pair that breaks it. The first form, "index by
the world", is the one §5 discharges. -/
theorem frontier_and_epoch_do_not_separate :
    frontier wQuiesced = frontier wPending
      ∧ held wQuiesced = held wPending
      ∧ wQuiesced.roster = wPending.roster
      ∧ wQuiesced.epoch = wPending.epoch
      ∧ pool wQuiesced ≠ pool wPending := by
  refine ⟨rfl, rfl, rfl, rfl, fun h => ?_⟩
  have h1 : Evidence.cand47 = Evidence.cand4749 := congrArg Prod.fst h
  exact absurd (congrFun h1 (49, Evidence.bob)) (by decide)

/-! ## §4. The relationship to `Evidence.lean` — image, and transfer.

Two directions, both stated as theorems rather than as a claim that one file
supersedes the other.

**Image.** The state-level relations are *exactly* the images of the
world-level ones under `observe` — iffs, not one-way soundness. So
`Evidence.ExtensionFuture` is the loosest sound state-level reading of the
world-level relation, and `Evidence.DeliveryFuture pool` likewise at each fixed
pool. Nothing there is wrong; what §3 shows is that the pool is not a function
of the state, so the *family* cannot be collapsed to a member.

⚠ And note what witnesses the extension image: **quiesced** worlds, in which
the pool *is* the state. That is the diagnosis in one clause — the state level
only ever sees worlds where the forgotten context is determined, so it cannot
have noticed forgetting it.

**Transfer.** `Evidence.lean`'s general results are stated over an arbitrary
`Future S` and instantiate at `S := World α` for free; the results specific to
`ResultEvidence` come across by pullback along `observe`. Both are exercised
below rather than asserted. -/

/-- **The state-level delivery relation is the image of the world-level one**,
at each fixed pool. Forward: the pool becomes the world's context. Backward:
projection. -/
theorem delivery_image {α : Type u} (p s t : Evidence.ResultEvidence α) :
    Evidence.DeliveryFuture p s t
      ↔ ∃ w v : World α,
          pool w = p ∧ observe w = s ∧ observe v = t ∧ DeliveryFuture w v := by
  constructor
  · intro h
    exact ⟨⟨s, p.1, p.2.1, p.2.2, 0⟩, ⟨t, p.1, p.2.1, p.2.2, 0⟩, rfl, rfl, rfl,
      ⟨h, rfl, rfl⟩⟩
  · rintro ⟨w, v, hp, hs, ht, hd⟩
    rw [← hp, ← hs, ← ht]
    exact hd.1

/-- **The state-level extension relation is the image of the world-level one**
— and the witnesses can be taken **quiesced**, which is exactly why the state
level cannot see a pool: in its whole image, the pool is the state.

(The epochs are `0` and `1` because the construction must be free to seal, and
sealing costs an advance — `no_closure_within_an_epoch`.) -/
theorem extension_image {α : Type u} (s t : Evidence.ResultEvidence α) :
    Evidence.ExtensionFuture s t
      ↔ ∃ w v : World α, observe w = s ∧ observe v = t
          ∧ Quiesced w ∧ Quiesced v ∧ ExtensionFuture w v := by
  constructor
  · intro h
    exact ⟨⟨s, s.1, s.2.1, s.2.2, 0⟩, ⟨t, t.1, t.2.1, t.2.2, 1⟩, rfl, rfl, rfl, rfl,
      ⟨h, h.1, leq_refl _, Nat.zero_le 1, fun _ _ _ => Nat.zero_lt_one⟩⟩
  · rintro ⟨w, v, hs, ht, _, _, he⟩
    rw [← hs, ← ht]
    exact he.1

/-- **`Evidence.render_sound` transports by pullback**, not by reproof: an
`exact` report at a world is the `exact` report at its observation, and a
sealed future of worlds projects to a sealed future of states
(`sealed_projects`). This is `Evidence.SoundEvaluator` — a general definition
over any `Future S` — instantiated at `S := World α`. -/
theorem renderW_sound {α : Type u} :
    Evidence.SoundEvaluator (SealedFuture (α := α))
      (fun w => Evidence.values (observe w)) (renderW (α := α)) where
  correct := fun w v h => Evidence.render_sound.correct (observe w) v h
  irrevocable := fun w u v hf h =>
    Evidence.render_sound.irrevocable (observe w) (observe u) v (sealed_projects hf) h

theorem sealed_wPending_refl : SealedFuture wPending wPending :=
  ⟨⟨Evidence.extensionFuture_refl _, leq_refl _, wf_wPending, Nat.le_refl _,
    fun _ h0 h1 => Bool.noConfusion (h0.symm.trans h1)⟩, leq_refl _, leq_refl _⟩

theorem sealed_wPending_wDelivered : SealedFuture wPending wDelivered :=
  ⟨⟨Evidence.openW_extends_to_openForkW, leq_refl _, wf_wDelivered, Nat.le_refl _,
    fun _ h0 h1 => Bool.noConfusion (h0.symm.trans h1)⟩, leq_refl _, leq_refl _⟩

/-- The two reachable observations disagree: `openForkW` holds `49` and
`openW` does not. -/
theorem values_openForkW_ne_openW :
    Evidence.values Evidence.openForkW ≠ Evidence.values Evidence.openW := by
  intro heq
  have h49 : Evidence.values Evidence.openW 49 = true := by
    rw [← heq]
    exact (Evidence.values_cand4749 (e := Evidence.openForkW) rfl).2
  obtain ⟨o, ho⟩ := (Evidence.mem_values Evidence.openW 49).mp h49
  have ho' : Evidence.cand47 (49, o) = true := ho
  exact absurd (Evidence.mem_cand47 ho').1 (by decide)

/-- **`Evidence.divergent_futures_force_nonexact` at the world carrier.** Two
sealed futures of `wPending` disagree about the answer, so no sound evaluator
may call it exact — and the theorem is the one `Evidence.lean` proved, used
here with `S := World Holes.Val` and no modification.

It agrees with `Evidence.no_exact_at_an_open_fork`, as it must:
`observe wPending = openW`. The content is that the general theorem instantiates
at the new carrier for free, which is verified here rather than assumed. -/
theorem no_exact_at_wPending : ¬ ∃ v, renderW wPending = Evidence.View.exact v :=
  Evidence.divergent_futures_force_nonexact renderW_sound
    sealed_wPending_wDelivered sealed_wPending_refl values_openForkW_ne_openW

/-- **`Evidence.exact_sound` at the world carrier**, likewise free: an exact
report survives every sealed future of the world it was made in. -/
theorem exact_survives_sealed_futures {α : Type u} {w u : World α} {v : α}
    (hv : renderW w = Evidence.View.exact v) (hf : SealedFuture w u) :
    Evidence.values (observe u) v = true
      ∧ Holes.SealsTo (Evidence.values (observe u)) v :=
  Evidence.exact_sound renderW_sound hv hf

/-! ### The transfer is not uniformly free — completeness needs wellformedness

Soundness came across by pullback and the two general theorems above came
across by instantiation. **Completeness does not**, and the reason is worth
having: completeness reads the *whole* set of permitted futures, so a world
with **no** sealed futures satisfies its hypothesis vacuously, at every value
at once. Wellformed worlds have futures (`delivery_refl`); the carrier `World α`
also contains worlds that do not, and `Evidence.CanonicalEvaluator` cannot tell
them apart. -/

/-- **The world-level sealed future realizes every state-level one.** Given a
sealed future of the *state*, a wellformed world with a known roster has a
sealed future observing it. So the world-level relation is not artificially
small: nothing about completeness leaks away in the move to worlds, and what
is left is only the ill-formed carrier junk below. -/
theorem sealed_future_realized {α : Type u} {w : World α}
    (hwf : Wf w) (hrk : RosterKnown w) {t : Evidence.ResultEvidence α}
    (h : Evidence.SealedFuture (observe w) t) :
    ∃ u : World α, observe u = t ∧ SealedFuture w u := by
  refine ⟨⟨t, w.issued ⊔ Evidence.candidates t, w.roster,
           w.sealed ⊔ Evidence.certificates t, w.epoch + 1⟩, rfl,
          ⟨h.1, ?_, ?_, Nat.le_succ _, fun _ _ _ => Nat.lt_succ_self _⟩,
          leq_refl _, hrk⟩
  · exact Evidence.leq_of_components (le_merge_left _ _) (leq_refl _)
      (le_merge_left _ _)
  · refine Evidence.leq_of_components (le_merge_right _ _) ?_ (le_merge_right _ _)
    refine (Holes.gset_leq_iff_subset _ _).mpr (fun o ho => ?_)
    exact (Holes.gset_leq_iff_subset _ _).mp (Evidence.obligations_mono hwf) o
      (h.2 o ho)

/-- **Completeness transfers — from a wellformed world with a known roster.**
If every sealed future of `w` agrees the answer is exactly `v`, `renderW` says
so. `Evidence.render_complete` does the work; `sealed_future_realized` is the
bridge that stops the world-level quantifier being weaker. -/
theorem renderW_complete {w : World Holes.Val} (hwf : Wf w) (hrk : RosterKnown w)
    (v : Holes.Val)
    (hall : ∀ u, SealedFuture w u →
      Evidence.values (observe u) v = true
        ∧ Holes.SealsTo (Evidence.values (observe u)) v) :
    renderW w = Evidence.View.exact v := by
  refine Evidence.render_complete Evidence.natFresh (observe w) v (fun t ht => ?_)
  obtain ⟨u, hu, hsf⟩ := sealed_future_realized hwf hrk ht
  rw [← hu]
  exact hall u hsf

/-- A world whose roster is not known to it: `bob` is on the roster and is not
an obligation. It has **no** sealed futures — not even itself. -/
def wRosterUnknown : World Holes.Val where
  state := Evidence.exactW
  issued := Evidence.cand47
  roster := Evidence.srcsAB
  sealed := Evidence.srcsA
  epoch := 0

theorem no_sealed_future_of_wRosterUnknown (u : World Holes.Val) :
    ¬ SealedFuture wRosterUnknown u := by
  intro h
  exact absurd ((Holes.gset_leq_iff_subset _ _).mp h.2.2 Evidence.bob (by decide))
    (by decide)

/-- ⚠ **AND THE UNCONDITIONAL `CanonicalEvaluator` IS FALSE AT `World α`.**
Not "unproved" — refuted. `wRosterUnknown` has no sealed futures, so
completeness' hypothesis is vacuously satisfied at *every* value, and the
structure would force `renderW` to report `exact 0` and `exact 1` at the same
world.

This is the one place the instantiation was **not** free, and the reason is the
one worth carrying: `Evidence.CanonicalEvaluator` was stated over a carrier
where every state has at least the reflexive future. `World α` is not such a
carrier — wellformedness is a hypothesis here, not a property of the type — so
completeness has to name it (`renderW_complete`) and the unconditional form
dies. Soundness, `exact_sound` and `divergent_futures_force_nonexact` are
unaffected: none of them reads the future set for emptiness. -/
theorem renderW_not_canonical :
    ¬ Evidence.CanonicalEvaluator (SealedFuture (α := Holes.Val))
        (fun w => Evidence.values (observe w)) renderW := by
  intro hc
  have h0 := hc.complete wRosterUnknown 0
    (fun u hu => absurd hu (no_sealed_future_of_wRosterUnknown u))
  have h1 := hc.complete wRosterUnknown 1
    (fun u hu => absurd hu (no_sealed_future_of_wRosterUnknown u))
  have heq : Evidence.View.exact (0 : Holes.Val)
      = Evidence.View.exact (1 : Holes.Val) := h0.symm.trans h1
  injection heq with hv
  exact absurd hv (by decide)

/-- A fourth world: `alice` is the only source, she is certified, and the pool
holds nothing else. Its state is `Evidence.exactW`. -/
def wExact : World Holes.Val where
  state := Evidence.exactW
  issued := Evidence.cand47
  roster := Evidence.srcsA
  sealed := Evidence.srcsA
  epoch := 1

/-- **`renderW` is a non-trivially sound evaluator at the world carrier**: it
does report `exact` somewhere, so `renderW_sound` is not `Evidence.blindEval`'s
kind of soundness and `no_exact_at_wPending` is not a fact about an evaluator
that never speaks. -/
theorem renderW_reports_exact : renderW wExact = Evidence.View.exact 47 :=
  Evidence.four_states_inhabited.1

/-! ## §5. THE SOUNDNESS CONSEQUENCE — a certificate must carry its world.

An **exactness certificate** is a licence to stop saying "pending". §3 says
delivery-stability is not a function of the state; §5 says what that costs the
certificate, and what fixes it.

`StateCertSound C` asks the honest thing of a state-indexed certificate: at
**every** world whose observation `C` accepts, the rendered answer really is
delivery-stable. That is what "reuse" means — a certificate is a value, it
travels, and wherever it lands it is applied to whatever world holds that
state.

The pair below is the payoff:

  * quiescence — the *same check*, keyed on the world — is sound;
  * no state-indexed certificate may accept `openW`, **even though the check
    that produced it was correct where it was made**. -/

/-- A certificate indexed by the materialized state. -/
def StateCert (α : Type u) : Type u := Evidence.ResultEvidence α → Prop

/-- A certificate indexed by the world. -/
def WorldCert (α : Type u) : Type u := World α → Prop

/-- **Sound**, for a state-indexed certificate: every world whose observation
it accepts really has a delivery-stable rendered answer. The quantifier over
worlds is the reuse. -/
def StateCertSound {α : Type u} (C : StateCert α) : Prop :=
  ∀ w : World α, C (observe w) →
    Evidence.FreeTermination DeliveryFuture (renderW (α := α)) w

/-- **Sound**, for a world-indexed certificate. Same conclusion, and the
premise may read the world. -/
def WorldCertSound {α : Type u} (C : WorldCert α) : Prop :=
  ∀ w : World α, C w →
    Evidence.FreeTermination DeliveryFuture (renderW (α := α)) w

/-- **Quiescence is a sound certificate** — a real one, discharged for a real
world (`quiesced_wQuiesced`), not an empty class. -/
theorem quiescence_is_a_sound_certificate {α : Type u} :
    WorldCertSound (fun w : World α => Quiesced w) :=
  fun _ h => quiesced_render_stable h

/-- ⚠ **NO SOUND STATE-INDEXED CERTIFICATE MAY ACCEPT `openW`.** Not a
conservative one, not a clever one: any `C` that accepts that state is unsound,
because `wPending` observes it and is not stable.

And the sting is that the state *is* settled at `wQuiesced`, where a replica
can check it and be right. The certificate is a true statement filed under a
key that does not determine its truth. -/
theorem no_sound_state_cert_accepts_openW (C : StateCert Holes.Val)
    (hC : StateCertSound C) : ¬ C Evidence.openW := by
  intro h
  exact not_stable_at_wPending (hC wPending h)

/-- ⚠ **THE REUSE UNSOUNDNESS, whole.** A replica at `wQuiesced` verifies —
correctly — that its rendered answer is settled under delivery. It files that
verification against the state it observed. One world over, a replica with the
**identical** state is not settled, and the certificate cannot tell.

So the exactness certificate must be indexed by the world. The last conjunct
says it in the strongest available form: *every* sound state-indexed
certificate must **refuse** the state at which the check succeeded. A
state-indexed certificate is not merely weaker — at this state it is
prohibited from ever saying yes. -/
theorem certificate_reuse_is_unsound :
    Quiesced wQuiesced
      ∧ Evidence.FreeTermination DeliveryFuture renderW wQuiesced
      ∧ observe wPending = observe wQuiesced
      ∧ ¬ Evidence.FreeTermination DeliveryFuture renderW wPending
      ∧ ∀ C : StateCert Holes.Val, StateCertSound C → ¬ C (observe wQuiesced) :=
  ⟨quiesced_wQuiesced, stable_at_wQuiesced, rfl, not_stable_at_wPending,
   fun C hC => no_sound_state_cert_accepts_openW C hC⟩

/-- **The repair, in one line.** The same distinction the state could not make,
the world makes: `wQuiesced` is quiesced and `wPending` is not, and quiescence
is sound (`quiescence_is_a_sound_certificate`). Moving the index from the state
to the world is not a stronger check — it is the check, correctly keyed. -/
theorem the_world_index_separates_them :
    Quiesced wQuiesced ∧ ¬ Quiesced wPending ∧ observe wQuiesced = observe wPending :=
  ⟨quiesced_wQuiesced, not_quiesced_wPending, same_observation⟩

end Uwueave.WorldFuture
