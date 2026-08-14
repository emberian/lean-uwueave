/-
# Uwueave.Frontier — Timely-style antichain progress for open membership.

`Evidence.lean` deliberately prices its `obligations : GSet Source` as a flat
approximation to a Timely frontier.  This module pays that debt without
changing the evidence carrier.  A frontier is an antichain of partially
ordered `(source, timestamp)` points.  Its upward closure is exactly the set
of points at which an event may still arrive; a point is complete when it is
outside that closure.

The distinction matters.  A source can be complete at one timestamp while it
remains open at another, and incomparable timestamps can remain open at once.
No `GSet Source` can retain either fact.  `flat_frontier_loses_position` gives
two frontiers with the same flat open-source and closure bits but opposite
answers about timestamp zero.

The delivery theorems keep the two axes separate:

  * frontier advance shrinks the may-arrive closure and composes;
  * delivered events grow and delivery completeness is monotone in that set;
  * a delivery/advance step may advance only when its target is complete;
  * advance alone does **not** transport delivery completeness forward,
    because it creates newly-complete timestamps.  `advance_without_delivery_
    is_unsound` is the concrete counterexample.

The bridges to the existing modules are intentionally narrow.  Frontier
completeness is stated against the candidate pool that `Evidence.DeliveryFuture`
and `WorldFuture.World` already carry.  It is preserved by their delivery
relations, quiescence implies it, and completeness of every issued timestamp
licenses delivery-stability of `Evidence.values`.  Nothing here claims that a
frontier alone determines a world future or stabilizes `Evidence.render`:
`WorldFuture.frontier_and_epoch_do_not_separate` already refutes that stronger
claim because the unseen issued pool remains load-bearing.

## Honest boundary

⟨TERMINAL⟩ = a theorem of this model; ⟨UNDONE U-0048⟩ = deliberately outside it.

  * **Frontiers are genuine antichains in a partial order.** ⟨TERMINAL⟩ Their
    upward closures give may-arrive sets, and advance is reverse inclusion of
    those closures.  The two-dimensional witness below contains two
    incomparable points.
  * **Progress is authenticated by the proof-model successor, not generated.**
    ⟨DONE at the model boundary; ⟨PREMISE U-0049⟩ for runtime and deployment⟩
    `DeliveryAdvance` checks only the semantic price of an advance.
    `Uwueave.AuthenticatedFrontier` separately retains a received, accepted and
    genuinely issued signed progress event, binds its decoded issued/delivered
    sets to that event, and conjoins the lawful advance. No protocol here
    manufactures the message, instantiates deployed cryptography, or proves a
    runtime advances honestly.
  * **Timestamps label candidate events externally.** ⟨TERMINAL for the
    bridge, ⟨UNDONE U-0050⟩ for the old carrier⟩ `ResultEvidence` stores no timestamp,
    so a bridge takes `stamp : (alpha x Source) -> T`.  Smuggling a timestamp
    into `Source` would recreate the flat model rather than repair it.
  * **Candidate stability is not render stability.** ⟨TERMINAL⟩ The proved
    bridge freezes `Evidence.values`.  Obligations and certificates can still
    arrive, so no theorem silently upgrades it to stability of `render`.
  * **The issued pool remains world-indexed.** ⟨TERMINAL⟩ A frontier bounds
    timestamps; it does not reveal what has already been issued.  The module
    therefore consumes `World.issued` and does not contradict
    `WorldFuture.delivery_future_is_not_state_indexed`.
-/
import Uwueave.WorldFuture

namespace Uwueave.Frontier

open Uwueave Uwueave.Catalog

/-! ## 1. Antichains and their upward closures -/

/-- A partial order, kept local and explicit because Uwueave's kernel-only
dependency floor does not import a general-purpose order hierarchy. -/
class PartialOrder (T : Type) where
  le : T -> T -> Prop
  refl : forall t, le t t
  trans : forall {a b c}, le a b -> le b c -> le a c
  antisymm : forall {a b}, le a b -> le b a -> a = b

infix:50 " ≼ " => PartialOrder.le

theorem po_refl {T : Type} [PartialOrder T] (t : T) : t ≼ t :=
  PartialOrder.refl t

theorem po_trans {T : Type} [PartialOrder T] {a b c : T}
    (hab : a ≼ b) (hbc : b ≼ c) : a ≼ c :=
  PartialOrder.trans hab hbc

theorem po_antisymm {T : Type} [PartialOrder T] {a b : T}
    (hab : a ≼ b) (hba : b ≼ a) : a = b :=
  PartialOrder.antisymm hab hba

instance : PartialOrder Nat where
  le := Nat.le
  refl := Nat.le_refl
  trans := Nat.le_trans
  antisymm := Nat.le_antisymm

/-- A list is an antichain when comparable members are equal.  The definition
is representation-independent: duplicate equal entries are harmless, while
two distinct comparable entries are forbidden. -/
def IsAntichain {T : Type} [PartialOrder T] (xs : List T) : Prop :=
  forall {a}, a ∈ xs -> forall {b}, b ∈ xs -> a ≼ b -> a = b

/-- A finite Timely-style frontier: an antichain of minimal points at which
work may still occur. -/
structure Frontier (T : Type) [PartialOrder T] where
  points : List T
  antichain : IsAntichain points

/-- The empty frontier: no timestamp remains open. -/
def empty (T : Type) [PartialOrder T] : Frontier T where
  points := []
  antichain := by simp [IsAntichain]

/-- A one-point frontier. -/
def singleton {T : Type} [PartialOrder T] (t : T) : Frontier T where
  points := [t]
  antichain := by
    intro a ha b hb _
    simp only [List.mem_singleton] at ha hb
    exact ha.trans hb.symm

/-- `F` covers `t` when one minimal open point is at or before `t`.  This is
the upward closure represented by the antichain. -/
def Covers {T : Type} [PartialOrder T] (F : Frontier T) (t : T) : Prop :=
  exists f, f ∈ F.points ∧ f ≼ t

/-- A timestamp is complete exactly when the frontier does not cover it. -/
def CompleteAt {T : Type} [PartialOrder T] (F : Frontier T) (t : T) : Prop :=
  Not (Covers F t)

/-- Advancing from `F` to `G` may only shrink the may-arrive set.  The apparent
reversal is deliberate: a later frontier makes *more* timestamps complete. -/
def AdvancesTo {T : Type} [PartialOrder T] (F G : Frontier T) : Prop :=
  forall t, Covers G t -> Covers F t

theorem covers_singleton_iff {T : Type} [PartialOrder T] {f t : T} :
    Covers (singleton f) t ↔ f ≼ t := by
  simp [Covers, singleton]

theorem not_covers_empty {T : Type} [PartialOrder T] (t : T) :
    Not (Covers (empty T) t) := by
  simp [Covers, empty]

theorem complete_empty {T : Type} [PartialOrder T] (t : T) :
    CompleteAt (empty T) t := not_covers_empty t

theorem advances_refl {T : Type} [PartialOrder T] (F : Frontier T) :
    AdvancesTo F F := fun _ h => h

theorem advances_trans {T : Type} [PartialOrder T] {F G H : Frontier T}
    (hFG : AdvancesTo F G) (hGH : AdvancesTo G H) : AdvancesTo F H :=
  fun t ht => hFG t (hGH t ht)

/-- Coverage moves backward across an advance. -/
theorem covers_before_of_covers_after {T : Type} [PartialOrder T]
    {F G : Frontier T} (h : AdvancesTo F G) {t : T} (ht : Covers G t) :
    Covers F t := h t ht

/-- Completion moves forward across an advance. -/
theorem complete_after_of_complete_before {T : Type} [PartialOrder T]
    {F G : Frontier T} (h : AdvancesTo F G) {t : T} (ht : CompleteAt F t) :
    CompleteAt G t := fun hG => ht (h t hG)

/-! ## 2. Open membership is ordered per source -/

/-- A progress point is a timestamp belonging to one source.  Points from
different sources are incomparable; points of one source inherit the partial
order on timestamps. -/
structure Point (T : Type) where
  source : Evidence.Source
  time : T
deriving DecidableEq, Repr

instance {T : Type} [PartialOrder T] : PartialOrder (Point T) where
  le p q := p.source = q.source ∧ p.time ≼ q.time
  refl p := ⟨rfl, po_refl p.time⟩
  trans hpq hqr := ⟨hpq.1.trans hqr.1, po_trans hpq.2 hqr.2⟩
  antisymm := by
    intro p q hpq hqp
    cases p with
    | mk ps pt =>
      cases q with
      | mk qs qt =>
        cases hpq.1
        have ht : pt = qt := po_antisymm hpq.2 hqp.2
        cases ht
        rfl

/-- A source-aware progress frontier. -/
abbrev SourceFrontier (T : Type) [PartialOrder T] := Frontier (Point T)

/-- This source and timestamp may still produce an event. -/
def MayArrive {T : Type} [PartialOrder T] (F : SourceFrontier T)
    (source : Evidence.Source) (time : T) : Prop :=
  Covers F ⟨source, time⟩

/-- This source and timestamp are settled. -/
def Settled {T : Type} [PartialOrder T] (F : SourceFrontier T)
    (source : Evidence.Source) (time : T) : Prop :=
  CompleteAt F ⟨source, time⟩

/-- Forget every timestamp and retain only whether a source has a frontier
point.  This is the flat `GSet Source` approximation used by old obligations. -/
def flatOpenSources {T : Type} [PartialOrder T] (F : SourceFrontier T) :
    GSet Evidence.Source :=
  fun source => F.points.any (fun p => decide (p.source = source))

/-- The equally flat whole-source closure bit.  It says only that no frontier
point for the source remains; it cannot express closure of a timestamp range. -/
def flatClosure {T : Type} [PartialOrder T] (F : SourceFrontier T) :
    GSet Evidence.Source :=
  fun source => !(flatOpenSources F source)

/-- Erase an ordered frontier into the existing evidence shape.  This is an
explicit lossy projection, not an embedding. -/
def eraseToEvidence {alpha T : Type} [PartialOrder T]
    (candidates : GSet (alpha × Evidence.Source)) (F : SourceFrontier T) :
    Evidence.ResultEvidence alpha :=
  (candidates, flatOpenSources F, flatClosure F)

theorem erased_empty_is_evidenceClosed {alpha T : Type} [PartialOrder T]
    (candidates : GSet (alpha × Evidence.Source)) :
    Evidence.Closed (eraseToEvidence candidates (empty (Point T))) := by
  intro source h
  change List.any [] (fun p : Point T => decide (p.source = source)) = true at h
  exact Bool.noConfusion h

/-! ### A real partial-order frontier

The two coordinates below stand for two independently progressing inputs.
`(0,1)` and `(1,0)` are incomparable, so both legitimately survive in one
minimal frontier. -/

structure ProductTime where
  left : Nat
  right : Nat
deriving DecidableEq, Repr

instance : PartialOrder ProductTime where
  le p q := p.left <= q.left ∧ p.right <= q.right
  refl p := ⟨Nat.le_refl p.left, Nat.le_refl p.right⟩
  trans hpq hqr := ⟨Nat.le_trans hpq.1 hqr.1, Nat.le_trans hpq.2 hqr.2⟩
  antisymm := by
    intro p q hpq hqp
    cases p with
    | mk pl pr =>
      cases q with
      | mk ql qr =>
        have hl : pl = ql := Nat.le_antisymm hpq.1 hqp.1
        have hr : pr = qr := Nat.le_antisymm hpq.2 hqp.2
        cases hl
        cases hr
        rfl

def west : ProductTime := ⟨0, 1⟩
def east : ProductTime := ⟨1, 0⟩

def diamondFrontier : SourceFrontier ProductTime where
  points := [⟨0, west⟩, ⟨0, east⟩]
  antichain := by
    intro a ha b hb hab
    simp at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · rfl
    · exact False.elim (Nat.not_succ_le_zero 0 hab.2.2)
    · exact False.elim (Nat.not_succ_le_zero 0 hab.2.1)
    · rfl

theorem diamond_points_are_incomparable :
    Not ((Point.mk 0 west) ≼ Point.mk 0 east)
      ∧ Not ((Point.mk 0 east) ≼ Point.mk 0 west) := by
  constructor <;> intro h
  · exact Nat.not_succ_le_zero 0 h.2.2
  · exact Nat.not_succ_le_zero 0 h.2.1

theorem diamond_covers_both_points :
    Covers diamondFrontier ⟨0, west⟩ ∧ Covers diamondFrontier ⟨0, east⟩ := by
  constructor
  · exact ⟨⟨0, west⟩, by simp [diamondFrontier], po_refl _⟩
  · exact ⟨⟨0, east⟩, by simp [diamondFrontier], po_refl _⟩

/-! ### Flat source closure loses the frontier position -/

def sourceZeroAtZero : SourceFrontier Nat := singleton ⟨0, 0⟩
def sourceZeroAtOne : SourceFrontier Nat := singleton ⟨0, 1⟩

/-- The frontier can advance from zero to one. -/
theorem zero_advances_to_one : AdvancesTo sourceZeroAtZero sourceZeroAtOne := by
  intro p hp
  have h := (covers_singleton_iff.mp hp)
  apply covers_singleton_iff.mpr
  exact ⟨h.1, Nat.zero_le _⟩

/-- The two frontiers collapse to exactly the same pair of flat source bits. -/
theorem same_flat_source_bits :
    flatOpenSources sourceZeroAtZero = flatOpenSources sourceZeroAtOne
      ∧ flatClosure sourceZeroAtZero = flatClosure sourceZeroAtOne :=
  ⟨rfl, rfl⟩

/-- The *entire* old evidence projection is identical: candidates are held
fixed and both flat source components forget the timestamp. -/
theorem same_erased_evidence {alpha : Type}
    (candidates : GSet (alpha × Evidence.Source)) :
    eraseToEvidence candidates sourceZeroAtZero =
      eraseToEvidence candidates sourceZeroAtOne := rfl

/-- A nonempty frontier is not globally `Evidence.Closed` under the erasure.
This is the precise positive boundary: `Closed` can represent "the whole
source is done," not "this prefix of the source is done." -/
theorem erased_open_frontier_not_evidenceClosed {alpha : Type}
    (candidates : GSet (alpha × Evidence.Source)) :
    Not (Evidence.Closed (eraseToEvidence candidates sourceZeroAtZero)) := by
  intro h
  have hopen : Evidence.obligations
      (eraseToEvidence candidates sourceZeroAtZero) 0 = true := by
    change List.any [Point.mk 0 0]
      (fun p : Point Nat => decide (p.source = 0)) = true
    decide
  have hc := h 0 hopen
  change false = true at hc
  exact Bool.noConfusion hc

/-- ⚠ **INFORMATION LOSS.** The same flat `GSet Source` closure says opposite
things about whether source zero is settled at timestamp zero. -/
theorem flat_frontier_loses_position :
    flatOpenSources sourceZeroAtZero = flatOpenSources sourceZeroAtOne
      ∧ flatClosure sourceZeroAtZero = flatClosure sourceZeroAtOne
      ∧ Not (Settled sourceZeroAtZero 0 0)
      ∧ Settled sourceZeroAtOne 0 0 := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro h
    exact h (covers_singleton_iff.mpr ⟨rfl, Nat.le_refl 0⟩)
  · intro h
    have hp := covers_singleton_iff.mp h
    exact Nat.not_succ_le_zero 0 hp.2

/-! ## 3. Delivery completeness and lawful advance -/

/-- An attributed candidate event is complete relative to `F` when every
issued event at a settled point has been delivered.  Events at covered points
may still be in flight. -/
def DeliveryComplete {alpha T : Type} [PartialOrder T]
    (F : SourceFrontier T) (stamp : (alpha × Evidence.Source) -> T)
    (issued delivered : GSet (alpha × Evidence.Source)) : Prop :=
  forall event, issued event = true ->
    Settled F event.2 (stamp event) -> delivered event = true

/-- Delivering more events preserves completeness at a fixed frontier. -/
theorem deliveryComplete_mono {alpha T : Type} [PartialOrder T]
    {F : SourceFrontier T} {stamp : (alpha × Evidence.Source) -> T}
    {issued delivered delivered' : GSet (alpha × Evidence.Source)}
    (hcomplete : DeliveryComplete F stamp issued delivered)
    (hgrows : delivered ⊑ delivered') :
    DeliveryComplete F stamp issued delivered' := by
  intro event hi hs
  exact (Holes.gset_leq_iff_subset _ _).mp hgrows event (hcomplete event hi hs)

/-- Completeness at the later frontier implies completeness at the earlier
one.  This is the safe direction: the later frontier has more settled times. -/
theorem deliveryComplete_before_of_after {alpha T : Type} [PartialOrder T]
    {F G : SourceFrontier T} {stamp : (alpha × Evidence.Source) -> T}
    {issued delivered : GSet (alpha × Evidence.Source)}
    (hadvance : AdvancesTo F G)
    (hcomplete : DeliveryComplete G stamp issued delivered) :
    DeliveryComplete F stamp issued delivered := by
  intro event hi hs
  exact hcomplete event hi (complete_after_of_complete_before hadvance hs)

/-- A lawful combined step: delivery grows, the frontier advances, and every
issued event newly declared complete has in fact been delivered at the target. -/
structure DeliveryAdvance {alpha T : Type} [PartialOrder T]
    (stamp : (alpha × Evidence.Source) -> T)
    (issued : GSet (alpha × Evidence.Source))
    (F G : SourceFrontier T)
    (delivered delivered' : GSet (alpha × Evidence.Source)) : Prop where
  delivered_mono : delivered ⊑ delivered'
  frontier_advance : AdvancesTo F G
  complete_after : DeliveryComplete G stamp issued delivered'

theorem deliveryAdvance_refl {alpha T : Type} [PartialOrder T]
    {stamp : (alpha × Evidence.Source) -> T}
    {issued delivered : GSet (alpha × Evidence.Source)} {F : SourceFrontier T}
    (hcomplete : DeliveryComplete F stamp issued delivered) :
    DeliveryAdvance stamp issued F F delivered delivered :=
  ⟨leq_refl _, advances_refl F, hcomplete⟩

/-- Lawful delivery/advance steps compose. -/
theorem deliveryAdvance_trans {alpha T : Type} [PartialOrder T]
    {stamp : (alpha × Evidence.Source) -> T}
    {issued d0 d1 d2 : GSet (alpha × Evidence.Source)}
    {F G H : SourceFrontier T}
    (hFG : DeliveryAdvance stamp issued F G d0 d1)
    (hGH : DeliveryAdvance stamp issued G H d1 d2) :
    DeliveryAdvance stamp issued F H d0 d2 :=
  ⟨leq_trans hFG.delivered_mono hGH.delivered_mono,
   advances_trans hFG.frontier_advance hGH.frontier_advance,
   hGH.complete_after⟩

/-! ### Advance is not delivery -/

abbrev TinyEvent := Nat × Evidence.Source

def loneIssued : GSet TinyEvent := fun event => decide (event = (7, 0))
def noneDelivered : GSet TinyEvent := fun _ => false
def tinyStamp : TinyEvent -> Nat := fun _ => 0

theorem complete_before_advance :
    DeliveryComplete sourceZeroAtZero tinyStamp loneIssued noneDelivered := by
  intro event hi hs
  have he : event = (7, 0) := of_decide_eq_true hi
  subst event
  exact False.elim (hs (covers_singleton_iff.mpr ⟨rfl, Nat.le_refl 0⟩))

theorem not_complete_after_advance :
    Not (DeliveryComplete sourceZeroAtOne tinyStamp loneIssued noneDelivered) := by
  intro h
  have hs : Settled sourceZeroAtOne 0 (tinyStamp (7, 0)) := by
    intro hc
    have hp := covers_singleton_iff.mp hc
    exact Nat.not_succ_le_zero 0 hp.2
  have := h (7, 0) (by decide) hs
  exact Bool.noConfusion this

/-- ⚠ **THE OVERSTRONG TRANSPORT IS FALSE.** A valid frontier advance plus
completeness at the old frontier does not imply completeness at the new one.
Timestamp zero became settled, but its issued event was never delivered. -/
theorem advance_without_delivery_is_unsound :
    AdvancesTo sourceZeroAtZero sourceZeroAtOne
      ∧ DeliveryComplete sourceZeroAtZero tinyStamp loneIssued noneDelivered
      ∧ Not (DeliveryComplete sourceZeroAtOne tinyStamp loneIssued noneDelivered) :=
  ⟨zero_advances_to_one, complete_before_advance, not_complete_after_advance⟩

/-! ## 4. Exact bridges to `Evidence` and `WorldFuture` -/

/-- The frontier reading of an existing evidence pool/state pair. -/
def EvidenceComplete {alpha T : Type} [PartialOrder T]
    (F : SourceFrontier T) (stamp : (alpha × Evidence.Source) -> T)
    (pool state : Evidence.ResultEvidence alpha) : Prop :=
  DeliveryComplete F stamp (Evidence.candidates pool) (Evidence.candidates state)

/-- Candidate completeness is preserved by an `Evidence.DeliveryFuture`.
This is only the candidate axis; no obligation/certificate conclusion is
smuggled into it. -/
theorem evidence_delivery_preserves_complete {alpha T : Type} [PartialOrder T]
    {F : SourceFrontier T} {stamp : (alpha × Evidence.Source) -> T}
    {pool s t : Evidence.ResultEvidence alpha}
    (hcomplete : EvidenceComplete F stamp pool s)
    (hfuture : Evidence.DeliveryFuture pool s t) :
    EvidenceComplete F stamp pool t :=
  deliveryComplete_mono hcomplete (Evidence.candidates_mono hfuture.1)

/-- If every issued candidate lies at a settled timestamp and all such events
have been delivered, the value set is stable under every delivery future.
The explicit `s <= pool` premise is the usual wellformedness side condition. -/
theorem evidence_complete_values_stable {alpha T : Type} [PartialOrder T]
    {F : SourceFrontier T} {stamp : (alpha × Evidence.Source) -> T}
    {pool s : Evidence.ResultEvidence alpha}
    (hwellformed : s ⊑ pool)
    (hcomplete : EvidenceComplete F stamp pool s)
    (hall : forall event, Evidence.candidates pool event = true ->
      Settled F event.2 (stamp event)) :
    Evidence.FreeTermination (Evidence.DeliveryFuture pool) Evidence.values s := by
  have hpool_s : Evidence.candidates pool ⊑ Evidence.candidates s :=
    (Holes.gset_leq_iff_subset _ _).mpr (fun event he =>
      hcomplete event he (hall event he))
  have hs_pool : Evidence.candidates s ⊑ Evidence.candidates pool :=
    Evidence.candidates_mono hwellformed
  have hsp : Evidence.candidates s = Evidence.candidates pool :=
    leq_antisymm hs_pool hpool_s
  intro t ht
  apply Evidence.values_congr
  apply leq_antisymm
  · rw [hsp]
    exact Evidence.candidates_mono ht.2.1
  · exact Evidence.candidates_mono ht.1

/-- Frontier-relative completeness for an existing world, using the issued
pool that the world (and not its materialized state) knows. -/
def WorldComplete {alpha T : Type} [PartialOrder T]
    (F : SourceFrontier T) (stamp : (alpha × Evidence.Source) -> T)
    (w : WorldFuture.World alpha) : Prop :=
  DeliveryComplete F stamp w.issued (WorldFuture.delivered w)

/-- A quiesced world has delivered every issued candidate and is therefore
complete at every frontier. -/
theorem worldComplete_of_quiesced {alpha T : Type} [PartialOrder T]
    (F : SourceFrontier T) (stamp : (alpha × Evidence.Source) -> T)
    {w : WorldFuture.World alpha} (hq : WorldFuture.Quiesced w) :
    WorldComplete F stamp w := by
  intro event hi _
  have heq : WorldFuture.observe w = WorldFuture.pool w := hq
  have hc := congrArg Prod.fst heq
  have hcEvent := congrFun hc event
  exact hcEvent.trans hi

/-- World delivery preserves frontier-relative candidate completeness.  The
proof uses both parts that the state alone lacks: delivery grows the observed
candidates, while the world's issued pool stays fixed. -/
theorem world_delivery_preserves_complete {alpha T : Type} [PartialOrder T]
    {F : SourceFrontier T} {stamp : (alpha × Evidence.Source) -> T}
    {w v : WorldFuture.World alpha}
    (hcomplete : WorldComplete F stamp w)
    (hfuture : WorldFuture.DeliveryFuture w v) :
    WorldComplete F stamp v := by
  intro event hi hs
  have hp : v.issued = w.issued := congrArg Prod.fst hfuture.2.1
  have hiw : w.issued event = true := by rw [← hp]; exact hi
  exact Evidence.candidates_grow hfuture.1.1 (hcomplete event hiw hs)

/-- The world-level stability bridge.  It freezes `Evidence.values`, not
`Evidence.render`: every issued candidate is settled and delivered, while the
other two evidence components remain outside this theorem. -/
theorem world_complete_values_stable {alpha T : Type} [PartialOrder T]
    {F : SourceFrontier T} {stamp : (alpha × Evidence.Source) -> T}
    {w : WorldFuture.World alpha}
    (hwellformed : WorldFuture.Wf w)
    (hcomplete : WorldComplete F stamp w)
    (hall : forall event, w.issued event = true ->
      Settled F event.2 (stamp event)) :
    Evidence.FreeTermination WorldFuture.DeliveryFuture
      (fun v => Evidence.values (WorldFuture.observe v)) w := by
  have hs := evidence_complete_values_stable
    (F := F) (stamp := stamp) (pool := WorldFuture.pool w)
    (s := WorldFuture.observe w) hwellformed hcomplete hall
  intro v hv
  exact hs (WorldFuture.observe v) hv.1

/-! ## 5. What does not bridge

The frontier is a progress bound, not the pool.  The existing witness is
re-exported in the exact shape needed to stop a tempting overclaim: identical
flat frontiers, certificates, rosters and epochs do not determine delivery
futures when issued events differ. -/

theorem flat_frontier_and_epoch_do_not_determine_world_future :
    WorldFuture.frontier WorldFuture.wQuiesced =
        WorldFuture.frontier WorldFuture.wPending
      ∧ WorldFuture.held WorldFuture.wQuiesced =
        WorldFuture.held WorldFuture.wPending
      ∧ WorldFuture.wQuiesced.roster = WorldFuture.wPending.roster
      ∧ WorldFuture.wQuiesced.epoch = WorldFuture.wPending.epoch
      ∧ WorldFuture.pool WorldFuture.wQuiesced ≠
        WorldFuture.pool WorldFuture.wPending :=
  WorldFuture.frontier_and_epoch_do_not_separate

end Uwueave.Frontier
