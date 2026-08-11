/-
# Uwueave.Preo.Future — world-indexed futures and proof-projected certificates.

This is the semantic kernel for a future-facing `preo` surface. It deliberately
contains no syntax or elaborator code. A future declaration is not merely a
relation on materialized states:

  * `WorldModel` names the world carrier and its state, pool, frontier and epoch
    projections.
  * `FutureDecl` adds a stable declaration name and a typed scope tag.
  * `WorldIndex` stores the world itself. Its four visible coordinates are
    computed from that world, so they cannot be supplied inconsistently.
  * `CheckedStability` and `CheckedCertificate` can only be built from proofs.
    Their conclusions are projected back out as `FreeTermination`; there is no
    state-only `exact` Boolean or badge.

`Delivery ⊆ Extension` is represented by `FutureDecl.IncludedIn`. Stability
and certificate soundness restrict **from** the larger extension future **to**
the smaller delivery future. The converse is refuted concretely: the same
rendered world is stable under delivery at `wQuiesced`, but an extension may
deliver a newly issued value and change the report.

The second concrete instance is ERA. Its delivery declaration retains the
event pool, outstanding-delivery frontier, cut-set epoch and `.delivery` scope.
`eraSettledCertificate` is projected from
`EraCertificate.era_finalisation_is_a_sound_certificate`; it is accepted at
`wPre` and refuted at `wAhead`.

Most importantly, `state_certificate_cannot_be_checked_at_quiesced` packages
`WorldFuture`'s same-state/different-world counterexample at the language
boundary. A valid world-indexed certificate exists at `wQuiesced`, but no sound
certificate indexed only by its materialized state may be checked there.
-/
import Uwueave.EraCertificate

namespace Uwueave.Preo.Future

open Uwueave
open Uwueave.CertificateScope
open Uwueave.Catalog

/-! ## §1. World models and named future declarations. -/

/-- A typed scope identity carried by a future declaration. These constructors
name distinct axes; they do not claim the corresponding relations coincide. -/
inductive Scope where
  | delivery
  | extension
  | issuance
  | announcement
  | sealed
  deriving DecidableEq, Repr

/-- The projections a language declaration may expose about a world. The world
remains present; these projections are never used as a replacement key. -/
structure WorldModel where
  World : Type
  State : Type
  Pool : Type
  Frontier : Type
  Epoch : Type
  observe : World → State
  pool : World → Pool
  frontier : World → Frontier
  epoch : World → Epoch

/-- A world index. There are no independently authored state/pool/frontier/
epoch fields: all four are computed from `world`. -/
structure WorldIndex (M : WorldModel) where
  world : M.World

namespace WorldIndex

def state {M : WorldModel} (i : WorldIndex M) : M.State := M.observe i.world

def pool {M : WorldModel} (i : WorldIndex M) : M.Pool := M.pool i.world

def frontier {M : WorldModel} (i : WorldIndex M) : M.Frontier := M.frontier i.world

def epoch {M : WorldModel} (i : WorldIndex M) : M.Epoch := M.epoch i.world

/-- The visible coordinates are definitional projections of the retained
world, not claims reconstructed from a state. -/
theorem projections_are_world_indexed {M : WorldModel} (i : WorldIndex M) :
    i.state = M.observe i.world
      ∧ i.pool = M.pool i.world
      ∧ i.frontier = M.frontier i.world
      ∧ i.epoch = M.epoch i.world :=
  ⟨rfl, rfl, rfl, rfl⟩

@[ext] theorem ext {M : WorldModel} {i j : WorldIndex M}
    (h : i.world = j.world) : i = j := by
  cases i
  cases j
  cases h
  rfl

end WorldIndex

/-- A source-level future declaration after semantic checking: stable name,
scope identity, and a relation on worlds. -/
structure FutureDecl (M : WorldModel) where
  name : String
  scope : Scope
  future : Evidence.Future M.World

namespace FutureDecl

/-- Relation inclusion. `narrow.IncludedIn broad` means every narrow future is
also a broad future. -/
def IncludedIn {M : WorldModel} (narrow broad : FutureDecl M) : Prop :=
  ∀ ⦃w v⦄, narrow.future w v → broad.future w v

theorem includedIn_refl {M : WorldModel} (F : FutureDecl M) : F.IncludedIn F :=
  fun {_ _} h => h

theorem includedIn_trans {M : WorldModel} {F G H : FutureDecl M}
    (hFG : F.IncludedIn G) (hGH : G.IncludedIn H) : F.IncludedIn H :=
  fun {_ _} h => hGH (hFG h)

end FutureDecl

/-! ## §2. Proof-projected artifacts. -/

/-- A checked stability result at one exact world index. The declaration scope
and every world coordinate remain available through the type parameters. -/
structure CheckedStability {M : WorldModel} (D : FutureDecl M)
    {R : Type} (answer : M.World → R) (index : WorldIndex M) where
  proof : Evidence.FreeTermination D.future answer index.world

namespace CheckedStability

/-- Construct a checked artifact only from the semantic proof. -/
def checked {M : WorldModel} {D : FutureDecl M} {R : Type}
    {answer : M.World → R} (index : WorldIndex M)
    (h : Evidence.FreeTermination D.future answer index.world) :
    CheckedStability D answer index := ⟨h⟩

/-- Project the semantic conclusion; this is the only meaning of the artifact. -/
theorem sound {M : WorldModel} {D : FutureDecl M} {R : Type}
    {answer : M.World → R} {index : WorldIndex M}
    (a : CheckedStability D answer index) :
    Evidence.FreeTermination D.future answer index.world := a.proof

/-- Restrict a proof from a broader future to a contained future. This is the
sound variance direction. -/
def restrict {M : WorldModel} {narrow broad : FutureDecl M}
    {R : Type} {answer : M.World → R} {index : WorldIndex M}
    (h : narrow.IncludedIn broad) (a : CheckedStability broad answer index) :
    CheckedStability narrow answer index :=
  ⟨fun v hv => a.proof v (h hv)⟩

end CheckedStability

/-- A checked key certificate at an exact world index. Both acceptance and the
universal soundness theorem are carried; neither is synthesized from state. -/
structure CheckedCertificate {M : WorldModel} (D : FutureDecl M)
    {K R : Type} (answer : M.World → R) (key : M.World → K) (C : K → Prop)
    (index : WorldIndex M) where
  accepted : C (key index.world)
  soundForAll : KeyCertSound key answer D.future C

namespace CheckedCertificate

/-- Every checked certificate projects to checked stability at its retained
world. -/
def stability {M : WorldModel} {D : FutureDecl M} {K R : Type}
    {answer : M.World → R} {key : M.World → K} {C : K → Prop}
    {index : WorldIndex M} (a : CheckedCertificate D answer key C index) :
    CheckedStability D answer index :=
  ⟨a.soundForAll index.world a.accepted⟩

/-- Certificate soundness is contravariant in the future relation, just like
stability: a certificate sound for a broader future is sound for a contained
one. -/
def restrict {M : WorldModel} {narrow broad : FutureDecl M}
    {K R : Type} {answer : M.World → R} {key : M.World → K} {C : K → Prop}
    {index : WorldIndex M} (h : narrow.IncludedIn broad)
    (a : CheckedCertificate broad answer key C index) :
    CheckedCertificate narrow answer key C index where
  accepted := a.accepted
  soundForAll := fun w hC v hv => a.soundForAll w hC v (h hv)

end CheckedCertificate

/-- The theorem-level form used by elaborators before an artifact exists. -/
theorem certificate_sound_restrict {M : WorldModel}
    {narrow broad : FutureDecl M} {K R : Type}
    {answer : M.World → R} {key : M.World → K} {C : K → Prop}
    (h : narrow.IncludedIn broad)
    (hs : KeyCertSound key answer broad.future C) :
    KeyCertSound key answer narrow.future C :=
  fun w hC v hv => hs w hC v (h hv)

/-! ## §3. The evidence-world declarations: Delivery ⊆ Extension. -/

/-- `WorldFuture.World` with every context coordinate exposed but still tied to
the retained world. -/
abbrev evidenceWorldModel (α : Type) : WorldModel where
  World := WorldFuture.World α
  State := Evidence.ResultEvidence α
  Pool := Evidence.ResultEvidence α
  Frontier := GSet Evidence.Source
  Epoch := Nat
  observe := WorldFuture.observe
  pool := WorldFuture.pool
  frontier := WorldFuture.frontier
  epoch := fun w => w.epoch

/-- Only already-issued evidence may arrive. -/
def Delivery (α : Type) : FutureDecl (evidenceWorldModel α) where
  name := "delivery"
  scope := .delivery
  future := WorldFuture.DeliveryFuture

/-- New evidence, membership and seals may be issued. -/
def Extension (α : Type) : FutureDecl (evidenceWorldModel α) where
  name := "extension"
  scope := .extension
  future := WorldFuture.ExtensionFuture

/-- **The inclusion used by the language.** Delivery is the narrower future. -/
theorem delivery_le_extension (α : Type) :
    (Delivery α).IncludedIn (Extension α) := by
  intro w v h
  exact WorldFuture.delivery_is_extension h

/-- Named coercion for surface elaboration: an extension-stability artifact may
be used wherever delivery stability is requested. -/
def extensionStabilityToDelivery {α R : Type}
    {answer : WorldFuture.World α → R} {index : WorldIndex (evidenceWorldModel α)}
    (a : CheckedStability (Extension α) answer index) :
    CheckedStability (Delivery α) answer index :=
  a.restrict (delivery_le_extension α)

/-- The corresponding certificate coercion, in the same sound direction. -/
def extensionCertificateToDelivery {α K R : Type}
    {answer : WorldFuture.World α → R} {key : WorldFuture.World α → K}
    {C : K → Prop} {index : WorldIndex (evidenceWorldModel α)}
    (a : CheckedCertificate (Extension α) answer key C index) :
    CheckedCertificate (Delivery α) answer key C index :=
  a.restrict (delivery_le_extension α)

/-! ## §4. Same state, different worlds: reuse is blocked. -/

def quiescedIndex : WorldIndex (evidenceWorldModel Holes.Val) :=
  ⟨WorldFuture.wQuiesced⟩

def pendingIndex : WorldIndex (evidenceWorldModel Holes.Val) :=
  ⟨WorldFuture.wPending⟩

/-- The indices expose the same state, frontier and epoch, but keep the pool
difference and therefore remain different world indices. -/
theorem same_state_indices_keep_the_world_difference :
    quiescedIndex.state = pendingIndex.state
      ∧ quiescedIndex.frontier = pendingIndex.frontier
      ∧ quiescedIndex.epoch = pendingIndex.epoch
      ∧ quiescedIndex.pool ≠ pendingIndex.pool
      ∧ quiescedIndex ≠ pendingIndex := by
  have h := WorldFuture.frontier_and_epoch_do_not_separate
  refine ⟨WorldFuture.same_observation, h.1, h.2.2.2.1, h.2.2.2.2, ?_⟩
  intro hi
  exact h.2.2.2.2 (congrArg WorldIndex.pool hi)

/-- A real proof-projected stability artifact at the quiesced world. -/
def quiescedRenderStability :
    CheckedStability (Delivery Holes.Val) WorldFuture.renderW quiescedIndex :=
  CheckedStability.checked quiescedIndex WorldFuture.stable_at_wQuiesced

/-- The world-indexed quiescence certificate is checkable at that world. -/
def quiescedWorldCertificate :
    CheckedCertificate (Delivery Holes.Val) WorldFuture.renderW
      (fun w => w) (fun w => WorldFuture.Quiesced w) quiescedIndex where
  accepted := WorldFuture.quiesced_wQuiesced
  soundForAll := WorldFuture.quiescence_is_a_sound_certificate

/-- **No state-only checked certificate can be produced at the very state where
the world-indexed check succeeds.** The identical state also occurs at
`wPending`, where the answer is not delivery-stable. -/
theorem state_certificate_cannot_be_checked_at_quiesced :
    ¬ ∃ C : Evidence.ResultEvidence Holes.Val → Prop,
      CheckedCertificate (Delivery Holes.Val) WorldFuture.renderW
        WorldFuture.observe C quiescedIndex := by
  rintro ⟨C, a⟩
  have hsound : WorldFuture.StateCertSound C := a.soundForAll
  exact WorldFuture.no_sound_state_cert_accepts_openW C hsound a.accepted

/-- The complete satisfiable/refutable boundary exposed to the future surface. -/
theorem same_state_different_worlds_block_certificate_reuse :
    quiescedIndex.state = pendingIndex.state
      ∧ Evidence.FreeTermination (Delivery Holes.Val).future
          WorldFuture.renderW quiescedIndex.world
      ∧ ¬ Evidence.FreeTermination (Delivery Holes.Val).future
          WorldFuture.renderW pendingIndex.world
      ∧ (¬ ∃ C : Evidence.ResultEvidence Holes.Val → Prop,
          CheckedCertificate (Delivery Holes.Val) WorldFuture.renderW
            WorldFuture.observe C quiescedIndex) :=
  ⟨WorldFuture.same_observation, WorldFuture.stable_at_wQuiesced,
   WorldFuture.not_stable_at_wPending,
   state_certificate_cannot_be_checked_at_quiesced⟩

/-! ### The inclusion is one-way. -/

/-- A genuine extension from the quiesced world issues the pending value and
then materializes it. This step is not a delivery of the original pool. -/
theorem extension_wQuiesced_wDelivered :
    (Extension Holes.Val).future WorldFuture.wQuiesced WorldFuture.wDelivered := by
  refine ⟨Evidence.openW_extends_to_openForkW, ?_, WorldFuture.wf_wDelivered,
    Nat.le_refl _, ?_⟩
  · exact Evidence.openW_extends_to_openForkW.1
  · intro o h0 h1
    exact Bool.noConfusion (h0.symm.trans h1)

/-- Delivery stability does not promote to extension stability. -/
theorem quiesced_render_not_extension_stable :
    ¬ Evidence.FreeTermination (Extension Holes.Val).future
        WorldFuture.renderW WorldFuture.wQuiesced := by
  intro h
  have hmoved := h WorldFuture.wDelivered extension_wQuiesced_wDelivered
  rw [CertificateScope.renderW_wDelivered,
    CertificateScope.renderW_wQuiesced] at hmoved
  exact absurd hmoved (Evidence.view_ne_of_tag (by simp [Evidence.viewTag]))

/-- Thus there is no inverse artifact coercion at the concrete witness. -/
theorem delivery_artifact_does_not_promote_to_extension :
    ¬ CheckedStability (Extension Holes.Val) WorldFuture.renderW quiescedIndex :=
  fun a => quiesced_render_not_extension_stable a.proof

/-- Quiescence is a sound delivery certificate but not a sound extension
certificate, so certificate coercion has the same strict direction. -/
theorem quiescence_certificate_not_sound_for_extension :
    ¬ KeyCertSound (fun w : WorldFuture.World Holes.Val => w)
        WorldFuture.renderW (Extension Holes.Val).future WorldFuture.Quiesced := by
  intro h
  exact quiesced_render_not_extension_stable
    (h WorldFuture.wQuiesced WorldFuture.quiesced_wQuiesced)

/-! ## §5. ERA declarations and its checked finalisation certificate. -/

/-- Events in the pool which have not yet been delivered. -/
def eraFrontier (w : EraCertificate.EraWorld) : GSet Era.Event :=
  fun e => decide (e ∈ w.pool ∧ e ∉ w.log)

/-- ERA's finalised view is the materialized state; the event pool, outstanding
delivery frontier and cut set remain attached to the retained world. -/
abbrev eraWorldModel : WorldModel where
  World := EraCertificate.EraWorld
  State := Era.GroupView
  Pool := GSet Era.Event
  Frontier := GSet Era.Event
  Epoch := GSet Era.Cut
  observe := EraCertificate.finalView
  pool := fun w e => decide (e ∈ w.pool)
  frontier := eraFrontier
  epoch := fun w => Era.cutSet w.cuts

def EraDelivery : FutureDecl eraWorldModel where
  name := "era.delivery"
  scope := .delivery
  future := EraCertificate.Delivery

def EraIssuance : FutureDecl eraWorldModel where
  name := "era.issuance"
  scope := .issuance
  future := EraCertificate.Issuance

def EraAnnouncement : FutureDecl eraWorldModel where
  name := "era.announcement"
  scope := .announcement
  future := EraCertificate.Announcement

/-- ERA also proves both narrow inclusions, without conflating the axes. -/
theorem era_delivery_le_issuance : EraDelivery.IncludedIn EraIssuance :=
  fun {_ _} h => EraCertificate.delivery_is_issuance h

theorem era_delivery_le_announcement : EraDelivery.IncludedIn EraAnnouncement :=
  fun {_ _} h => EraCertificate.delivery_is_announcement h

def eraPreIndex : WorldIndex eraWorldModel := ⟨EraCertificate.wPre⟩

def eraAheadIndex : WorldIndex eraWorldModel := ⟨EraCertificate.wAhead⟩

/-- ERA's settled certificate, projected from the existing universal soundness
proof and retained at the complete world index. -/
def eraSettledCertificate :
    CheckedCertificate EraDelivery EraCertificate.finalView
      EraCertificate.eraKey EraCertificate.settledCert eraPreIndex where
  accepted := (EraCertificate.settledCert_iff EraCertificate.wPre).mpr
    EraCertificate.settled_wPre
  soundForAll := EraCertificate.era_finalisation_is_a_sound_certificate

/-- The stability artifact is obtained from the certificate artifact; there is
no second state-only check. -/
def eraSettledStability :
    CheckedStability EraDelivery EraCertificate.finalView eraPreIndex :=
  eraSettledCertificate.stability

/-- Concrete acceptance and refusal, at two fully retained world indices. -/
theorem era_certificate_is_satisfiable_and_refutable :
    EraCertificate.settledCert (EraCertificate.eraKey eraPreIndex.world)
      ∧ ¬ EraCertificate.settledCert (EraCertificate.eraKey eraAheadIndex.world) :=
  EraCertificate.the_certificate_is_satisfiable_and_refutable

/-- The Era index exposes each coordinate from its retained world and keeps the
delivery scope attached to the declaration. -/
theorem era_artifact_retains_identity :
    eraPreIndex.state = EraCertificate.finalView eraPreIndex.world
      ∧ eraPreIndex.pool = (fun e => decide (e ∈ eraPreIndex.world.pool))
      ∧ eraPreIndex.frontier = eraFrontier eraPreIndex.world
      ∧ eraPreIndex.epoch = Era.cutSet eraPreIndex.world.cuts
      ∧ EraDelivery.scope = Scope.delivery :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

end Uwueave.Preo.Future
