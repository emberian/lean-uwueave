/-
# FiniteHistoryDeliveryCommon — test-only repeated lock-history delivery

This finite six-version witness lives below tests so the public bridge remains
generic.  It supplies every authored ID/parent/coherence premise explicitly,
then replays the same proof-indexed history in causal and reverse order.
-/
import Uwueave.FiniteHistoryDelivery

namespace Canary.Wave29.FiniteHistoryDeliveryCommon

open Uwueave
open Uwueave.Histories Uwueave.HistoryPolicy Uwueave.HistoryRuntime
open Uwueave.PersistentRuntime Uwueave.PersistentHistoryRuntime
open Uwueave.FiniteHistoryDelivery

def lockId : LVer → Nat
  | .root => 0
  | .alice => 1
  | .bob => 2
  | .m1 => 3
  | .m2 => 4
  | .j => 5

def rootEvent : Event Nat LVer := ⟨0, [], .root⟩
def aliceEvent : Event Nat LVer := ⟨1, [0], .alice⟩
def bobEvent : Event Nat LVer := ⟨2, [0], .bob⟩
def m1Event : Event Nat LVer := ⟨3, [1, 2], .m1⟩
def m2Event : Event Nat LVer := ⟨4, [1, 2], .m2⟩
def joinEvent : Event Nat LVer := ⟨5, [3, 4], .j⟩

def events : List (Event Nat LVer) :=
  [rootEvent, aliceEvent, bobEvent, m1Event, m2Event, joinEvent]

def reverseEvents : List (Event Nat LVer) :=
  [joinEvent, m2Event, m1Event, bobEvent, aliceEvent, rootEvent]

def growth : FiniteGrowth lvExplicit lockHistory Ancestral.lockImpl Nat where
  idOf := lockId
  events := events
  versions := [.root, .alice, .bob, .m1, .m2, .j]
  versions_eq := rfl
  versions_nodup := by decide
  versions_complete := by intro version; cases version <;> decide
  id_injective := by
    intro left right _ _ equal
    cases left <;> cases right <;> simp_all [lockId]
  id_exact := by
    intro event member
    simp [events] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  origin_exact := by
    intro event member
    simp [events] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  parent_closed := by
    intro event member parent parentMember
    simp [events] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · simp [rootEvent] at parentMember
    · simp [aliceEvent] at parentMember
      subst parent
      exact ⟨rootEvent, by simp [events], rfl⟩
    · simp [bobEvent] at parentMember
      subst parent
      exact ⟨rootEvent, by simp [events], rfl⟩
    · simp [m1Event] at parentMember
      rcases parentMember with rfl | rfl
      · exact ⟨aliceEvent, by simp [events], rfl⟩
      · exact ⟨bobEvent, by simp [events], rfl⟩
    · simp [m2Event] at parentMember
      rcases parentMember with rfl | rfl
      · exact ⟨aliceEvent, by simp [events], rfl⟩
      · exact ⟨bobEvent, by simp [events], rfl⟩
    · simp [joinEvent] at parentMember
      rcases parentMember with rfl | rfl
      · exact ⟨m1Event, by simp [events], rfl⟩
      · exact ⟨m2Event, by simp [events], rfl⟩
  coherent := by
    simpa [HistoryPolicy.lvExplicit, HistoryPolicy.explicit] using
      lockHistory_coherent
  selectsAncestors := lvSelect_selectsAncestors lockHistory rfl
  policyGenerated := lockHistory_policyGenerated

def causalState : DeliveryState Nat LVer := ⟨⟨events⟩, [], 6⟩

def reverseState : DeliveryState Nat LVer :=
  ⟨⟨[rootEvent, bobEvent, aliceEvent, m2Event, m1Event, joinEvent]⟩, [], 6⟩

def causalCursor : DeliveryCursor Nat LVer := ⟨causalState, events⟩
def reverseCursor : DeliveryCursor Nat LVer := ⟨reverseState, reverseEvents⟩

set_option maxRecDepth 100000 in
theorem causal_replay_exact :
    replay (deliverySchema Nat LVer) (emptyDeliveryCursor Nat LVer 6) events =
      some causalCursor := by
  decide

set_option maxRecDepth 100000 in
theorem reverse_replay_exact :
    replay (deliverySchema Nat LVer) (emptyDeliveryCursor Nat LVer 6)
      reverseEvents = some reverseCursor := by
  decide

theorem causalCursor_coherent : DeliveryCursorCoherent causalCursor := by
  constructor
  · change 0 ≤ 6
    omega
  · intro event
    simp [causalCursor, causalState]

theorem reverseCursor_coherent : DeliveryCursorCoherent reverseCursor := by
  constructor
  · change 0 ≤ 6
    omega
  · intro event
    change event ∈ reverseEvents ↔
      event ∈ [rootEvent, bobEvent, aliceEvent, m2Event, m1Event, joinEvent] ∨
        event ∈ []
    simp only [List.not_mem_nil, or_false]
    exact (by decide : reverseEvents.Perm
      [rootEvent, bobEvent, aliceEvent, m2Event, m1Event, joinEvent]).mem_iff

def causalDelivery : DeliveredGrowth (impl := Ancestral.lockImpl) growth 6 where
  arrivals := events
  arrivals_perm := .refl _
  cursor := causalCursor
  replay_exact := causal_replay_exact
  accepted_exact := rfl
  coherent := causalCursor_coherent
  settled := rfl

def reverseDelivery : DeliveredGrowth (impl := Ancestral.lockImpl) growth 6 where
  arrivals := reverseEvents
  arrivals_perm := by decide
  cursor := reverseCursor
  replay_exact := reverse_replay_exact
  accepted_exact := rfl
  coherent := reverseCursor_coherent
  settled := rfl

set_option maxRecDepth 100000 in
theorem duplicate_retry :
    applyRecord (deliverySchema Nat LVer) causalCursor joinEvent =
      some causalCursor := by
  decide

def collisionEvent : Event Nat LVer := ⟨5, [3, 4], .m1⟩
def selfParentEvent : Event Nat LVer := ⟨8, [8], .j⟩
def duplicateParentEvent : Event Nat LVer := ⟨9, [0, 0], .j⟩

set_option maxRecDepth 100000 in
theorem collision_refused :
    applyRecord (deliverySchema Nat LVer) causalCursor collisionEvent = none := by
  decide

set_option maxRecDepth 100000 in
theorem self_parent_refused :
    applyRecord (deliverySchema Nat LVer) causalCursor selfParentEvent = none := by
  decide

set_option maxRecDepth 100000 in
theorem duplicate_parent_refused :
    applyRecord (deliverySchema Nat LVer) causalCursor duplicateParentEvent = none := by
  decide

end Canary.Wave29.FiniteHistoryDeliveryCommon
