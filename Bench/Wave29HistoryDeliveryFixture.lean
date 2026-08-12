import Uwueave.FiniteHistoryDelivery

namespace PreoBench.Wave29.HistoryDeliveryFixture

open Uwueave.Histories Uwueave.HistoryPolicy
open Uwueave.HistoryRuntime Uwueave.PersistentRuntime
open Uwueave.PersistentHistoryRuntime
open Uwueave.FiniteHistoryDelivery
open Uwueave.Necessity

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

def causalEvents : List (Event Nat LVer) :=
  [rootEvent, aliceEvent, bobEvent, m1Event, m2Event, joinEvent]

def reverseEvents : List (Event Nat LVer) :=
  [joinEvent, m2Event, m1Event, bobEvent, aliceEvent, rootEvent]

def growth : FiniteGrowth lvExplicit lockHistory Uwueave.Ancestral.lockImpl Nat where
  idOf := lockId
  events := causalEvents
  versions := [.root, .alice, .bob, .m1, .m2, .j]
  versions_eq := rfl
  versions_nodup := by decide
  versions_complete := by intro version; cases version <;> decide
  id_injective := by
    intro left right _ _ equal
    cases left <;> cases right <;> simp_all [lockId]
  id_exact := by
    intro event member
    simp [causalEvents] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  origin_exact := by
    intro event member
    simp [causalEvents] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  parent_closed := by
    intro event member parent parentMember
    simp [causalEvents] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    · simp_all [rootEvent]
    · simp [aliceEvent] at parentMember
      subst parent
      exact ⟨rootEvent, by simp [causalEvents], rfl⟩
    · simp [bobEvent] at parentMember
      subst parent
      exact ⟨rootEvent, by simp [causalEvents], rfl⟩
    · simp [m1Event] at parentMember
      rcases parentMember with rfl | rfl
      · exact ⟨aliceEvent, by simp [causalEvents], rfl⟩
      · exact ⟨bobEvent, by simp [causalEvents], rfl⟩
    · simp [m2Event] at parentMember
      rcases parentMember with rfl | rfl
      · exact ⟨aliceEvent, by simp [causalEvents], rfl⟩
      · exact ⟨bobEvent, by simp [causalEvents], rfl⟩
    · simp [joinEvent] at parentMember
      rcases parentMember with rfl | rfl
      · exact ⟨m1Event, by simp [causalEvents], rfl⟩
      · exact ⟨m2Event, by simp [causalEvents], rfl⟩
  coherent := by
    change lockHistory.Coherent Uwueave.Ancestral.lockAM
      Uwueave.Ancestral.lockImpl
    exact lockHistory_coherent
  selectsAncestors := lvSelect_selectsAncestors lockHistory rfl
  policyGenerated := lockHistory_policyGenerated

def causalState : DeliveryState Nat LVer := ⟨⟨causalEvents⟩, [], 6⟩

def reverseState : DeliveryState Nat LVer :=
  ⟨⟨[rootEvent, bobEvent, aliceEvent, m2Event, m1Event, joinEvent]⟩, [], 6⟩

def causalCursor : DeliveryCursor Nat LVer := ⟨causalState, causalEvents⟩
def reverseCursor : DeliveryCursor Nat LVer := ⟨reverseState, reverseEvents⟩

theorem causal_replay_exact :
    replay (deliverySchema Nat LVer) (emptyDeliveryCursor Nat LVer 6)
      causalEvents = some causalCursor := by decide

theorem reverse_replay_exact :
    replay (deliverySchema Nat LVer) (emptyDeliveryCursor Nat LVer 6)
      reverseEvents = some reverseCursor := by decide

theorem causalCursor_coherent : DeliveryCursorCoherent causalCursor := by
  constructor
  · change [].length ≤ 6
    decide
  · intro event
    simp [causalCursor, causalState]

theorem reverseCursor_coherent : DeliveryCursorCoherent reverseCursor := by
  constructor
  · change [].length ≤ 6
    decide
  · intro event
    simp [reverseCursor, reverseState, reverseEvents, rootEvent, aliceEvent,
      bobEvent, m1Event, m2Event, joinEvent, or_comm, or_left_comm, or_assoc]

def causalDelivery : @DeliveredGrowth LVer Uwueave.Ancestral.Lock
    Uwueave.Ancestral.LockOp Nat _ _ lvExplicit lockHistory
    Uwueave.Ancestral.lockImpl growth 6 where
  arrivals := causalEvents
  arrivals_perm := .refl _
  cursor := causalCursor
  replay_exact := causal_replay_exact
  accepted_exact := rfl
  coherent := causalCursor_coherent
  settled := rfl

def reverseDelivery : @DeliveredGrowth LVer Uwueave.Ancestral.Lock
    Uwueave.Ancestral.LockOp Nat _ _ lvExplicit lockHistory
    Uwueave.Ancestral.lockImpl growth 6 where
  arrivals := reverseEvents
  arrivals_perm := by decide
  cursor := reverseCursor
  replay_exact := reverse_replay_exact
  accepted_exact := rfl
  coherent := reverseCursor_coherent
  settled := rfl

def mkDelivery (_ : Unit) : @DeliveredGrowth LVer Uwueave.Ancestral.Lock
    Uwueave.Ancestral.LockOp Nat _ _ lvExplicit lockHistory
    Uwueave.Ancestral.lockImpl growth 6 := reverseDelivery

def forgedJoin : Event Nat LVer := ⟨5, [3, 4], .m1⟩

end PreoBench.Wave29.HistoryDeliveryFixture
