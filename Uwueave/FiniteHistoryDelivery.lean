/-
# Uwueave.FiniteHistoryDelivery -- an authored finite history at the delivery edge

This leaf relates one explicitly enumerated `History` to the pure buffered
delivery runtime.  Stable identifiers, parent lists, replay success, and cursor
coherence are all premises: none is inferred from bytes, a host, or an
unbounded history.  Equality of delivered event sets yields only the existing
event-set view.  Semantic history views require the separate
`RecordDetermined`/`HistoryConvergent` premises from `HistoryPolicy`.
-/
import Uwueave.PersistentHistoryRuntime

namespace Uwueave.FiniteHistoryDelivery

open Uwueave.Histories Uwueave.HistoryPolicy
open Uwueave.HistoryRuntime Uwueave.PersistentRuntime
open Uwueave.PersistentHistoryRuntime
open Uwueave.Necessity
open Uwueave.Ancestral

set_option autoImplicit false

/-- A finite, authored presentation of a coherent history.  Event payloads are
the versions themselves; ids are equality keys, not authenticity claims. -/
structure FiniteGrowth {V S Op : Type} (P : HistoryMerge V S Op)
    (H : History V S Op) (impl : Impl S Op) (Id : Type)
    [DecidableEq Id] where
  idOf : V → Id
  events : List (Event Id V)
  versions : List V
  versions_eq : events.map Event.payload = versions
  versions_nodup : versions.Nodup
  versions_complete : ∀ version, version ∈ versions
  id_injective : ∀ {left right}, left ∈ versions → right ∈ versions →
    idOf left = idOf right → left = right
  id_exact : ∀ event, event ∈ events → event.id = idOf event.payload
  origin_exact : ∀ event, event ∈ events →
    match H.origin event.payload with
    | .root => event.parents = []
    | .ran parent => event.parents = [idOf parent]
    | .merged _ left right => event.parents = [idOf left, idOf right]
  parent_closed : ∀ event, event ∈ events → ∀ parent, parent ∈ event.parents →
    ∃ parentEvent, parentEvent ∈ events ∧ parentEvent.id = parent
  coherent : H.Coherent P.kernel impl
  selectsAncestors : SelectsAncestors P H
  policyGenerated : PolicyGenerated P H

namespace FiniteGrowth

variable {V S Op Id : Type} {P : HistoryMerge V S Op} {H : History V S Op}
  {impl : Impl S Op} [DecidableEq Id]

theorem event_payload_mem (growth : FiniteGrowth P H impl Id)
    {event : Event Id V} (member : event ∈ growth.events) :
    event.payload ∈ growth.versions := by
  rw [← growth.versions_eq]
  exact List.mem_map.mpr ⟨event, member, rfl⟩

theorem idOf_injective (growth : FiniteGrowth P H impl Id) :
    Function.Injective growth.idOf := by
  intro left right equal
  exact growth.id_injective (growth.versions_complete left)
    (growth.versions_complete right) equal

/-- The ordinary history view reproduces every authored state, but only
because coherence, ancestor selection, and policy generation are explicit
fields of the finite presentation. -/
theorem view_eq_state (growth : FiniteGrowth P H impl Id) (version : V) :
    viewOf P H version = H.state version :=
  HistoryPolicy.viewOf_eq_state growth.coherent growth.selectsAncestors
    growth.policyGenerated version

end FiniteGrowth

/-- One successful delivery of exactly a finite growth's events.  Arrival order
may differ, but the authoritative accepted list is pinned to that order and the
result is settled. -/
structure DeliveredGrowth {V S Op Id : Type} [DecidableEq V] [DecidableEq Id]
    {P : HistoryMerge V S Op} {H : History V S Op} {impl : Impl S Op}
    (growth : FiniteGrowth P H impl Id) (capacity : Nat) where
  arrivals : List (Event Id V)
  arrivals_perm : arrivals.Perm growth.events
  cursor : DeliveryCursor Id V
  replay_exact : replay (deliverySchema Id V)
    (emptyDeliveryCursor Id V capacity) arrivals = some cursor
  accepted_exact : cursor.accepted = arrivals
  coherent : DeliveryCursorCoherent cursor
  settled : cursor.state.pending = []

namespace DeliveredGrowth

variable {V S Op Id : Type} [DecidableEq V] [DecidableEq Id]
  {P : HistoryMerge V S Op} {H : History V S Op} {impl : Impl S Op}
  {growth : FiniteGrowth P H impl Id} {capacity : Nat}

theorem accepted_iff (delivery : DeliveredGrowth growth capacity)
    (event : Event Id V) :
    event ∈ delivery.cursor.accepted ↔ event ∈ growth.events := by
  rw [delivery.accepted_exact]
  exact delivery.arrivals_perm.mem_iff

theorem materialized_iff (delivery : DeliveredGrowth growth capacity)
    (event : Event Id V) :
    event ∈ delivery.cursor.state.materialized.accepted ↔
      event ∈ growth.events := by
  have cursorIff := delivery.coherent.2 event
  rw [delivery.settled] at cursorIff
  simp only [List.not_mem_nil, or_false] at cursorIff
  exact cursorIff.symm.trans (delivery.accepted_iff event)

theorem capacity_respected (delivery : DeliveredGrowth growth capacity) :
    delivery.cursor.state.pending.length ≤ delivery.cursor.state.capacity :=
  delivery.coherent.1

theorem sameEventSet {leftCapacity rightCapacity : Nat}
    (left : DeliveredGrowth growth leftCapacity)
    (right : DeliveredGrowth growth rightCapacity) :
    SameEventSet left.cursor.state.materialized right.cursor.state.materialized := by
  intro event
  exact (left.materialized_iff event).trans (right.materialized_iff event).symm

theorem settledSameEventSet {leftCapacity rightCapacity : Nat}
    (left : DeliveredGrowth growth leftCapacity)
    (right : DeliveredGrowth growth rightCapacity) :
    SettledSameEventSet left.cursor.state right.cursor.state :=
  ⟨left.settled, right.settled, left.sameEventSet right⟩

/-- Equality of the runtime's extensional event-set observation.  This theorem
does not identify that observation with a semantic history state. -/
theorem eventSetView_eq {leftCapacity rightCapacity : Nat}
    (left : DeliveredGrowth growth leftCapacity)
    (right : DeliveredGrowth growth rightCapacity) :
    eventSetView left.cursor.state.materialized =
      eventSetView right.cursor.state.materialized :=
  (left.settledSameEventSet right).view_eq

end DeliveredGrowth

/-! ## Semantic convergence remains a separate premise -/

theorem semantic_view_eq_of_convergent {V S Op : Type}
    {P : HistoryMerge V S Op} {left right : History V S Op}
    (convergent : HistoryConvergent P) (sameRecord : SameRecord left right)
    (version : V) :
    viewOf P left version = viewOf P right version :=
  convergent left right sameRecord version

theorem semantic_view_eq_of_recordDetermined {V S Op : Type}
    {P : HistoryMerge V S Op} {left right : History V S Op}
    (determined : RecordDetermined P) (sameRecord : SameRecord left right)
    (version : V) :
    viewOf P left version = viewOf P right version :=
  semantic_view_eq_of_convergent
    (HistoryPolicy.recordDetermined_converges determined) sameRecord version

end Uwueave.FiniteHistoryDelivery
