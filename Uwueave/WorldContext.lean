/-
# Uwueave.WorldContext — delivery futures carry authority and history context.

`WorldFuture.World` fixes the first hidden axis behind a materialized evidence
state: the issued pool.  This module adds three more axes that a delivery
decision can genuinely depend on:

  * outstanding authority capabilities, interpreted through
    `Authority.Active` and `Gated.covers`;
  * a causally closed known-history cut, using `CausalReach.Cut` rather than an
    arbitrary set of operation names;
  * a known version base and head in a labelled `Histories.History`, related by
    `Histories.Reaches`.

`Context` projects to `WorldFuture.World` by forgetting all three.  The
context-aware futures refine the projected future with exact side conditions:
newly delivered candidates must be licensed by an outstanding active grant,
their causal origin must be in the known cut, and their version must be
reachable from the known base.  Delivery freezes the context; extension may
grow authority, outstanding capability knowledge and the causal cut while its
base/head advance in the version DAG.

The projection theorems are deliberately asymmetric.  Context delivery or
extension always projects to `WorldFuture`; lifting a projected step requires
the named `Frozen`/`Extends` and `Admits` hypotheses.  The witnesses at the end
show those hypotheses cannot be erased: contexts with the same materialized
state, pool, frontier and epoch permit different deliveries when their
capability set, causal cut, or known base differs.

## Honest boundary

⟨TERMINAL⟩ = a theorem of this model; ⟨UNDONE⟩ = deliberately outside it.

  * ⟨TERMINAL⟩ **Capabilities are active grants, not opaque booleans.** A source
    is licensed only by a grant present in `outstanding`, active in the carried
    `GatedState`, and whose scope covers a source-shaped probe operation.
  * ⟨TERMINAL⟩ **Known history is a causal cut.** Downward closure comes from
    `CausalReach.Cut.down`; this file never calls an arbitrary `GSet` a history.
  * ⟨TERMINAL⟩ **Known bases are version facts.** `base_reaches_head` is
    `Histories.Reaches` in a real labelled `History`.  Turning a base into a
    state-level merge decision additionally requires `Histories.RunRealized`
    and a genuine `CommonAncestor`; `known_base_selected_valid` exposes both.
  * ⟨DONE in the proof-carrying successor; UNDONE for deployment crypto⟩
    **Authentication and capability consumption remain outside this carrier.**
    `Uwueave.AuthenticatedWorldContext` adds accepted-and-issued signed typed
    position claims and grow-only consumption tombstones while projecting its
    distinct consuming step to `WorldFuture`.  This file still neither verifies
    a deployed scheme nor deletes an outstanding grant.
  * ⟨DONE with an explicit signed decoder; TERMINAL against automatic recovery⟩
    **Origin/version attribution is not implicit.** `ResultEvidence` stores
    neither causal operation ids nor version ids.  The authenticated successor
    therefore retains a caller-supplied decoder, exact signed
    world/value/position binding, and signed-decoded origin/version admission
    checks against the cut and base, rather than inventing defaults.
  * ⟨TERMINAL⟩ **Projection is lossy.** The three witness pairs prove that the
    extra axes change allowed futures while every `WorldFuture` field agrees.
-/
import Uwueave.WorldFuture
import Uwueave.Gated
import Uwueave.CausalReach
import Uwueave.Histories

namespace Uwueave.WorldContext

open Uwueave Uwueave.Catalog

/-! ## 1. The extended world -/

/-- A `WorldFuture.World` together with the authority, causal-history, and
version-base context in which delivery is judged.  The history objects are
parameters, so two values of this type cannot silently disagree on what their
causal or version relation means. -/
structure Context (α CausalOp Version HistoryOp : Type)
    (H : CausalReach.FinHistory CausalOp)
    (VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp) where
  world : WorldFuture.World α
  authority : Gated.GatedState
  outstanding : Authority.GrantSet
  known : CausalReach.Cut H
  base : Version
  head : Version
  base_reaches_head : Histories.Reaches VH.dag base head

/-- Forget the extra context. -/
def project {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    (c : Context α CausalOp Version HistoryOp H VH) : WorldFuture.World α :=
  c.world

/-- A source-shaped gated operation.  Only `node` is semantically consumed by
`Gated.covers`; `cite` records which grant is being exercised. -/
def sourceProbe (source cite : Evidence.Source) : Gated.GOp where
  t := 0
  node := source
  dest := none
  cite := cite

/-- An outstanding active capability covers a source. -/
def CapabilityAllows {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    (c : Context α CausalOp Version HistoryOp H VH)
    (source : Evidence.Source) : Prop :=
  ∃ grant : Authority.Grant,
    c.outstanding grant = true
      ∧ Authority.Active (Gated.grants c.authority) (Gated.revoked c.authority) grant
      ∧ Gated.covers grant.2.2 (sourceProbe source grant.1)

/-- The causal origin is in the downward-closed history cut known here. -/
def CausallyKnown {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    (origin : (α × Evidence.Source) → CausalOp)
    (c : Context α CausalOp Version HistoryOp H VH)
    (event : α × Evidence.Source) : Prop :=
  c.known.mem (origin event) = true

/-- The event's version is at or beyond the base known here. -/
def BaseAllows {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    (versionOf : (α × Evidence.Source) → Version)
    (c : Context α CausalOp Version HistoryOp H VH)
    (event : α × Evidence.Source) : Prop :=
  Histories.Reaches VH.dag c.base (versionOf event)

/-- The extra admission check on candidates newly materialized in a step. -/
def Admits {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    (origin : (α × Evidence.Source) → CausalOp)
    (versionOf : (α × Evidence.Source) → Version)
    (c : Context α CausalOp Version HistoryOp H VH)
    (s t : Evidence.ResultEvidence α) : Prop :=
  ∀ event, Evidence.candidates s event = false →
    Evidence.candidates t event = true →
      CapabilityAllows c event.2
        ∧ CausallyKnown origin c event
        ∧ BaseAllows versionOf c event

/-- Delivery freezes every extra context axis.  Cut equality is stated on
membership rather than proof fields, which is the observable content. -/
structure Frozen {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    (c d : Context α CausalOp Version HistoryOp H VH) : Prop where
  authority : d.authority = c.authority
  outstanding : d.outstanding = c.outstanding
  known : ∀ op, d.known.mem op = c.known.mem op
  base : d.base = c.base
  head : d.head = c.head

/-- Extension may grow monotone context and advance its base/head.  A causal
cut is grown by inclusion; its downward-closure proof remains inside `Cut`. -/
structure Extends {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    (c d : Context α CausalOp Version HistoryOp H VH) : Prop where
  authority : c.authority ⊑ d.authority
  outstanding : c.outstanding ⊑ d.outstanding
  known : ∀ op, c.known.mem op = true → d.known.mem op = true
  base : Histories.Reaches VH.dag c.base d.base
  head : Histories.Reaches VH.dag c.head d.head

theorem frozen_extends {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    {c d : Context α CausalOp Version HistoryOp H VH} (h : Frozen c d) :
    Extends c d := by
  constructor
  · rw [h.authority]
    exact leq_refl _
  · rw [h.outstanding]
    exact leq_refl _
  · intro op hop
    rw [h.known op]
    exact hop
  · rw [h.base]
    exact Histories.Reaches.refl VH.dag _
  · rw [h.head]
    exact Histories.Reaches.refl VH.dag _

/-! ## 2. Context-aware futures and exact projection -/

def DeliveryFuture {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    (origin : (α × Evidence.Source) → CausalOp)
    (versionOf : (α × Evidence.Source) → Version)
    (c d : Context α CausalOp Version HistoryOp H VH) : Prop :=
  WorldFuture.DeliveryFuture (project c) (project d)
    ∧ Frozen c d
    ∧ Admits origin versionOf c (WorldFuture.observe (project c))
        (WorldFuture.observe (project d))

def ExtensionFuture {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    (origin : (α × Evidence.Source) → CausalOp)
    (versionOf : (α × Evidence.Source) → Version)
    (c d : Context α CausalOp Version HistoryOp H VH) : Prop :=
  WorldFuture.ExtensionFuture (project c) (project d)
    ∧ Extends c d
    ∧ Admits origin versionOf c (WorldFuture.observe (project c))
        (WorldFuture.observe (project d))

/-- Context delivery always projects. -/
theorem delivery_projects {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    {origin : (α × Evidence.Source) → CausalOp}
    {versionOf : (α × Evidence.Source) → Version}
    {c d : Context α CausalOp Version HistoryOp H VH}
    (h : DeliveryFuture origin versionOf c d) :
    WorldFuture.DeliveryFuture (project c) (project d) := h.1

/-- Context extension always projects. -/
theorem extension_projects {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    {origin : (α × Evidence.Source) → CausalOp}
    {versionOf : (α × Evidence.Source) → Version}
    {c d : Context α CausalOp Version HistoryOp H VH}
    (h : ExtensionFuture origin versionOf c d) :
    WorldFuture.ExtensionFuture (project c) (project d) := h.1

/-- The evidence-level delivery projection, through both world layers. -/
theorem delivery_projects_evidence {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    {origin : (α × Evidence.Source) → CausalOp}
    {versionOf : (α × Evidence.Source) → Version}
    {c d : Context α CausalOp Version HistoryOp H VH}
    (h : DeliveryFuture origin versionOf c d) :
    Evidence.DeliveryFuture (WorldFuture.pool (project c))
      (WorldFuture.observe (project c)) (WorldFuture.observe (project d)) :=
  WorldFuture.delivery_projects h.1

/-- **The exact converse.** A projected delivery lifts only together with a
frozen context and the three-axis admission proof. -/
theorem delivery_lifts {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    {origin : (α × Evidence.Source) → CausalOp}
    {versionOf : (α × Evidence.Source) → Version}
    {c d : Context α CausalOp Version HistoryOp H VH}
    (hworld : WorldFuture.DeliveryFuture (project c) (project d))
    (hfrozen : Frozen c d)
    (hadmits : Admits origin versionOf c (WorldFuture.observe (project c))
      (WorldFuture.observe (project d))) :
    DeliveryFuture origin versionOf c d :=
  ⟨hworld, hfrozen, hadmits⟩

/-- The exact extension converse. -/
theorem extension_lifts {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    {origin : (α × Evidence.Source) → CausalOp}
    {versionOf : (α × Evidence.Source) → Version}
    {c d : Context α CausalOp Version HistoryOp H VH}
    (hworld : WorldFuture.ExtensionFuture (project c) (project d))
    (hextends : Extends c d)
    (hadmits : Admits origin versionOf c (WorldFuture.observe (project c))
      (WorldFuture.observe (project d))) :
    ExtensionFuture origin versionOf c d :=
  ⟨hworld, hextends, hadmits⟩

/-- Delivery is an extension after the same context price is paid. -/
theorem delivery_is_extension {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    {origin : (α × Evidence.Source) → CausalOp}
    {versionOf : (α × Evidence.Source) → Version}
    {c d : Context α CausalOp Version HistoryOp H VH}
    (h : DeliveryFuture origin versionOf c d) :
    ExtensionFuture origin versionOf c d :=
  ⟨WorldFuture.delivery_is_extension h.1, frozen_extends h.2.1, h.2.2⟩

/-! ## 3. Bridges that need their hypotheses -/

/-- Known causal membership is downward closed because it is a `Cut`. -/
theorem causally_known_predecessor {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    {c : Context α CausalOp Version HistoryOp H VH}
    {origin : (α × Evidence.Source) → CausalOp}
    {event : α × Evidence.Source} {prior : CausalOp}
    (hknown : CausallyKnown origin c event)
    (hbefore : H.hb prior (origin event) = true) : c.known.mem prior = true :=
  c.known.down prior (origin event) hknown hbefore

/-- A known base becomes a state-level selected base only under the exact
history bridge: run-realized edges and common ancestry of the actual pair. -/
theorem known_base_selected_valid {α CausalOp Version HistoryOp : Type}
    {H : CausalReach.FinHistory CausalOp}
    {VH : Histories.History Version (Evidence.ResultEvidence α) HistoryOp}
    {c : Context α CausalOp Version HistoryOp H VH}
    {impl : Necessity.Impl (Evidence.ResultEvidence α) HistoryOp}
    (hrr : Histories.RunRealized VH impl) {x y : Version}
    (hcommon : Histories.CommonAncestor VH.dag x y c.base) :
    (MergeModel.BaseDecision.selected (VH.state c.base)).Valid impl
      (VH.state x) (VH.state y) :=
  Histories.selected_valid hrr hcommon

/-! ## 4. Concrete separations -/

inductive Version where
  | root
  | alternate
  | event
  | head
deriving DecidableEq, Repr

def versionParent : Version → Version → Bool
  | .root, .event => true
  | .event, .head => true
  | .alternate, .head => true
  | _, _ => false

def versionRank : Version → Nat
  | .root => 0
  | .alternate => 1
  | .event => 1
  | .head => 2

def versionDag : Histories.VersionDag Version where
  parent := versionParent
  rank := versionRank
  rank_lt := by
    intro p c h
    cases p <;> cases c <;> simp [versionParent, versionRank] at h ⊢

theorem root_reaches_event :
    Histories.Reaches versionDag .root .event :=
  Or.inr (.direct rfl)

theorem root_reaches_head :
    Histories.Reaches versionDag .root .head :=
  have h : Histories.Ancestry versionDag .root .event := .direct rfl
  Or.inr (.extend h rfl)

theorem alternate_reaches_head :
    Histories.Reaches versionDag .alternate .head :=
  Or.inr (.direct rfl)

theorem not_alternate_reaches_event :
    ¬ Histories.Reaches versionDag .alternate .event := by
  intro h
  rcases Histories.Reaches.eq_or_rank_lt h with heq | hlt
  · exact absurd heq (by decide)
  · exact Nat.lt_irrefl 1 hlt

/-- A labelled version history.  Only its DAG and labels are consumed here; no
coherence or run-realization claim is made for this witness. -/
def versionHistory :
    Histories.History Version (Evidence.ResultEvidence Holes.Val) Unit where
  dag := versionDag
  state
    | .root => Evidence.openW
    | .alternate => Evidence.openW
    | .event => Evidence.openForkW
    | .head => Evidence.openForkW
  origin
    | .root => .root
    | .alternate => .root
    | .event => .ran .root
    | .head => .ran .event
  root := .root

def causalHistory : CausalReach.FinHistory Bool := CausalReach.eqHistory Bool

def fullCut : CausalReach.Cut causalHistory where
  mem := fun _ => true
  down := fun _ _ _ _ => rfl

def emptyCut : CausalReach.Cut causalHistory where
  mem := fun _ => false
  down := fun _ _ h _ => Bool.noConfusion h

def authorityContext : Gated.GatedState :=
  (Authority.demoChain, Authority.noRevs, fun _ => false)

def delegateCapability : Authority.GrantSet :=
  fun grant => decide (grant = ((2 : Nat), (1 : Nat), (4 : Nat)))

def noCapabilities : Authority.GrantSet := fun _ => false

def eventOrigin (_ : Holes.Val × Evidence.Source) : Bool := false

def eventVersion (event : Holes.Val × Evidence.Source) : Version :=
  if event = (49, Evidence.bob) then .event else .head

abbrev DemoContext :=
  Context Holes.Val Bool Version Unit causalHistory versionHistory

def capRich : DemoContext where
  world := WorldFuture.wPending
  authority := authorityContext
  outstanding := delegateCapability
  known := fullCut
  base := .root
  head := .head
  base_reaches_head := root_reaches_head

def capRichDelivered : DemoContext where
  world := WorldFuture.wDelivered
  authority := authorityContext
  outstanding := delegateCapability
  known := fullCut
  base := .root
  head := .head
  base_reaches_head := root_reaches_head

def capPoor : DemoContext where
  world := WorldFuture.wPending
  authority := authorityContext
  outstanding := noCapabilities
  known := fullCut
  base := .root
  head := .head
  base_reaches_head := root_reaches_head

def capPoorDelivered : DemoContext where
  world := WorldFuture.wDelivered
  authority := authorityContext
  outstanding := noCapabilities
  known := fullCut
  base := .root
  head := .head
  base_reaches_head := root_reaches_head

def alternateBase : DemoContext where
  world := WorldFuture.wPending
  authority := authorityContext
  outstanding := delegateCapability
  known := fullCut
  base := .alternate
  head := .head
  base_reaches_head := alternate_reaches_head

def alternateBaseDelivered : DemoContext where
  world := WorldFuture.wDelivered
  authority := authorityContext
  outstanding := delegateCapability
  known := fullCut
  base := .alternate
  head := .head
  base_reaches_head := alternate_reaches_head

def historyUnknown : DemoContext where
  world := WorldFuture.wPending
  authority := authorityContext
  outstanding := delegateCapability
  known := emptyCut
  base := .root
  head := .head
  base_reaches_head := root_reaches_head

def historyUnknownDelivered : DemoContext where
  world := WorldFuture.wDelivered
  authority := authorityContext
  outstanding := delegateCapability
  known := emptyCut
  base := .root
  head := .head
  base_reaches_head := root_reaches_head

theorem added_candidate_is_bob {event : Holes.Val × Evidence.Source}
    (hbefore : Evidence.candidates (WorldFuture.observe WorldFuture.wPending) event = false)
    (hafter : Evidence.candidates (WorldFuture.observe WorldFuture.wDelivered) event = true) :
    event = (49, Evidence.bob) := by
  change Evidence.cand47 event = false at hbefore
  change Evidence.cand4749 event = true at hafter
  rcases of_decide_eq_true hafter with h | h
  · subst event
    exact absurd hbefore (by decide)
  · exact h

theorem capRich_admits :
    Admits eventOrigin eventVersion capRich
      (WorldFuture.observe (project capRich))
      (WorldFuture.observe (project capRichDelivered)) := by
  intro event hbefore hafter
  have hevent := added_candidate_is_bob hbefore hafter
  subst event
  refine ⟨⟨(2, 1, 4), by decide, Authority.demo_delegate_active, by decide⟩,
    rfl, ?_⟩
  simpa [eventVersion] using root_reaches_event

theorem frozen_capRich : Frozen capRich capRichDelivered :=
  ⟨rfl, rfl, fun _ => rfl, rfl, rfl⟩

theorem delivery_capRich :
    DeliveryFuture eventOrigin eventVersion capRich capRichDelivered :=
  delivery_lifts WorldFuture.delivery_wPending_wDelivered frozen_capRich capRich_admits

theorem capPoor_does_not_admit :
    ¬ Admits eventOrigin eventVersion capPoor
      (WorldFuture.observe (project capPoor))
      (WorldFuture.observe (project capPoorDelivered)) := by
  intro h
  obtain ⟨grant, hout, _⟩ := (h (49, Evidence.bob) (by decide) (by decide)).1
  exact Bool.noConfusion hout

theorem not_delivery_capPoor :
    ¬ DeliveryFuture eventOrigin eventVersion capPoor capPoorDelivered :=
  fun h => capPoor_does_not_admit h.2.2

theorem alternateBase_does_not_admit :
    ¬ Admits eventOrigin eventVersion alternateBase
      (WorldFuture.observe (project alternateBase))
      (WorldFuture.observe (project alternateBaseDelivered)) := by
  intro h
  have hb := (h (49, Evidence.bob) (by decide) (by decide)).2.2
  exact not_alternate_reaches_event (by simpa [eventVersion] using hb)

theorem not_delivery_alternateBase :
    ¬ DeliveryFuture eventOrigin eventVersion alternateBase alternateBaseDelivered :=
  fun h => alternateBase_does_not_admit h.2.2

theorem historyUnknown_does_not_admit :
    ¬ Admits eventOrigin eventVersion historyUnknown
      (WorldFuture.observe (project historyUnknown))
      (WorldFuture.observe (project historyUnknownDelivered)) := by
  intro h
  have hk := (h (49, Evidence.bob) (by decide) (by decide)).2.1
  exact Bool.noConfusion hk

theorem not_delivery_historyUnknown :
    ¬ DeliveryFuture eventOrigin eventVersion historyUnknown historyUnknownDelivered :=
  fun h => historyUnknown_does_not_admit h.2.2

/-- All axes visible to `WorldFuture` agree, while capability/base/cut context
differs. -/
theorem same_world_axes_hide_context :
    WorldFuture.observe (project capRich) = WorldFuture.observe (project capPoor)
      ∧ WorldFuture.pool (project capRich) = WorldFuture.pool (project capPoor)
      ∧ WorldFuture.frontier (project capRich) = WorldFuture.frontier (project capPoor)
      ∧ (project capRich).epoch = (project capPoor).epoch
      ∧ capRich.outstanding ≠ capPoor.outstanding
      ∧ WorldFuture.observe (project capRich) = WorldFuture.observe (project alternateBase)
      ∧ WorldFuture.pool (project capRich) = WorldFuture.pool (project alternateBase)
      ∧ capRich.base ≠ alternateBase.base
      ∧ capRich.known.mem false ≠ historyUnknown.known.mem false := by
  refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl, by decide, by decide⟩
  intro h
  exact absurd (congrFun h (2, 1, 4)) (by decide)

/-- **Capability is load-bearing.** Same projected source and target worlds;
opposite context-delivery verdicts. -/
theorem capability_changes_allowed_futures :
    project capRich = project capPoor
      ∧ project capRichDelivered = project capPoorDelivered
      ∧ DeliveryFuture eventOrigin eventVersion capRich capRichDelivered
      ∧ ¬ DeliveryFuture eventOrigin eventVersion capPoor capPoorDelivered :=
  ⟨rfl, rfl, delivery_capRich, not_delivery_capPoor⟩

/-- **Known base is load-bearing.** The root base reaches the event version;
the alternate base reaches the same head but not that event. -/
theorem known_base_changes_allowed_futures :
    project capRich = project alternateBase
      ∧ project capRichDelivered = project alternateBaseDelivered
      ∧ DeliveryFuture eventOrigin eventVersion capRich capRichDelivered
      ∧ ¬ DeliveryFuture eventOrigin eventVersion alternateBase alternateBaseDelivered :=
  ⟨rfl, rfl, delivery_capRich, not_delivery_alternateBase⟩

/-- **Known causal history is load-bearing.** Full and empty causal cuts sit
over the same world and base but permit opposite deliveries. -/
theorem known_cut_changes_allowed_futures :
    project capRich = project historyUnknown
      ∧ project capRichDelivered = project historyUnknownDelivered
      ∧ DeliveryFuture eventOrigin eventVersion capRich capRichDelivered
      ∧ ¬ DeliveryFuture eventOrigin eventVersion historyUnknown historyUnknownDelivered :=
  ⟨rfl, rfl, delivery_capRich, not_delivery_historyUnknown⟩

/-- The projected delivery alone cannot be lifted: this is the concrete
refutation of an overstrong converse to `delivery_projects`. -/
theorem projected_delivery_does_not_lift_without_context :
    WorldFuture.DeliveryFuture (project capPoor) (project capPoorDelivered)
      ∧ ¬ DeliveryFuture eventOrigin eventVersion capPoor capPoorDelivered :=
  ⟨WorldFuture.delivery_wPending_wDelivered, not_delivery_capPoor⟩

/-- The known-base witness agrees on every projected `WorldFuture` axis; its
different base is therefore genuinely hidden by projection. -/
theorem known_base_pair_same_world_axes :
    WorldFuture.observe (project capRich) =
        WorldFuture.observe (project alternateBase)
      ∧ WorldFuture.pool (project capRich) =
        WorldFuture.pool (project alternateBase)
      ∧ WorldFuture.frontier (project capRich) =
        WorldFuture.frontier (project alternateBase)
      ∧ (project capRich).epoch = (project alternateBase).epoch
      ∧ capRich.base ≠ alternateBase.base :=
  ⟨rfl, rfl, rfl, rfl, by decide⟩

/-- Nor can a projected extension be lifted without the context hypotheses. -/
theorem projected_extension_does_not_lift_without_context :
    WorldFuture.ExtensionFuture (project capPoor) (project capPoorDelivered)
      ∧ ¬ ExtensionFuture eventOrigin eventVersion capPoor capPoorDelivered :=
  ⟨WorldFuture.delivery_is_extension WorldFuture.delivery_wPending_wDelivered,
   fun h => capPoor_does_not_admit h.2.2⟩

end Uwueave.WorldContext
