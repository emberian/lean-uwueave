/-
# Uwueave.ShippingContextCompiler — contexts derived from a finite shipping API.

A shipping surface exposes a finite list of packets and one public operation:
deliver an exposed packet into the current merge state.  `API.contexts`
enumerates every order-insensitive delivery history by enumerating subsets of
that packet list.  Arbitrary delivery histories may reorder and duplicate
packets; `Delta.same_deltas_same_state` proves that their result is still in
the enumeration.

The construction is deliberately finite.  Completeness is relative to the
packets exposed by this API; it does not claim that an external deployment has
no other operation or that an unbounded packet generator is enumerable.
-/
import Uwueave.ContextCompiler
import Uwueave.Delta
import Uwueave.FiniteProductSearch

namespace Uwueave.ShippingContextCompiler

open Uwueave

universe u v

/-- A finite public shipping surface.  Packets are merge-state deltas. -/
structure API (S : Type u) [MergeState S] where
  initial : S
  packets : List S

variable {S : Type u} [MergeState S]

/-- The only public transition: reject packets absent from the advertised
finite surface, otherwise merge the packet into the receiver state. -/
def API.deliver? [DecidableEq S] (api : API S) (state packet : S) : Option S :=
  if packet ∈ api.packets then some (state ⊔ packet) else none

/-- Reachability through a finite history of advertised public deliveries. -/
def API.Reachable (api : API S) (context : S) : Prop :=
  ∃ history : List S,
    (∀ packet ∈ history, packet ∈ api.packets) ∧
    Delta.joinAll api.initial history = context

theorem API.initial_reachable (api : API S) : api.Reachable api.initial :=
  ⟨[], by simp, rfl⟩

/-- A successful public delivery preserves the semantic reachability
judgement. -/
theorem API.reachable_deliver [DecidableEq S] (api : API S) {state packet : S}
    (hstate : api.Reachable state) (hpacket : packet ∈ api.packets) :
    api.Reachable (state ⊔ packet) := by
  obtain ⟨history, hpublic, hrun⟩ := hstate
  refine ⟨history ++ [packet], ?_, ?_⟩
  · intro candidate hcandidate
    rw [List.mem_append] at hcandidate
    rcases hcandidate with hcandidate | hcandidate
    · exact hpublic candidate hcandidate
    · simp only [List.mem_singleton] at hcandidate
      subst candidate
      exact hpacket
  · rw [Delta.joinAll_append, hrun]
    rfl

theorem API.deliver?_reachable [DecidableEq S] (api : API S) {state packet next : S}
    (hstate : api.Reachable state) (hdeliver : api.deliver? state packet = some next) :
    api.Reachable next := by
  unfold API.deliver? at hdeliver
  split at hdeliver
  next hpacket =>
    have hnext : state ⊔ packet = next := Option.some.inj hdeliver
    rw [← hnext]
    exact api.reachable_deliver hstate hpacket
  next => simp at hdeliver

/-- Canonical reachable contexts: one merge result per order-preserving subset
of the advertised packet list. -/
def API.contexts (api : API S) : List S :=
  (FiniteProductSearch.subsets api.packets).map
    (Delta.joinAll api.initial)

/-- Nothing invented: every enumerated context has an advertised delivery
history. -/
theorem API.contexts_sound (api : API S) {context : S}
    (hcontext : context ∈ api.contexts) : api.Reachable context := by
  obtain ⟨history, hsubset, rfl⟩ := List.mem_map.mp hcontext
  refine ⟨history, ?_, rfl⟩
  intro packet hpacket
  exact List.Sublist.mem hpacket
    (FiniteProductSearch.mem_subsets_iff_sublist.mp hsubset)

/-- **Shipping coverage.** Every state reachable through arbitrary successful
public deliveries occurs in the finite context enumeration.  Reordering and
redelivery disappear through the merge laws, not through an operational
assumption. -/
theorem API.reachable_mem_contexts [DecidableEq S] (api : API S) {context : S}
    (hcontext : api.Reachable context) : context ∈ api.contexts := by
  obtain ⟨history, hpublic, hrun⟩ := hcontext
  let canonical := api.packets.filter fun packet => decide (packet ∈ history)
  have hcanonical : canonical ∈ FiniteProductSearch.subsets api.packets :=
    FiniteProductSearch.mem_subsets_iff_sublist.mpr List.filter_sublist
  have hmembers : ∀ packet : S, packet ∈ canonical ↔ packet ∈ history := by
    intro packet
    simp only [canonical, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact And.right
    · intro hpacket
      exact ⟨hpublic packet hpacket, hpacket⟩
  have hsame : Delta.joinAll api.initial canonical =
      Delta.joinAll api.initial history :=
    Delta.same_deltas_same_state hmembers api.initial
  apply List.mem_map.mpr
  exact ⟨canonical, hcanonical, hsame.trans hrun⟩

/-- Query equivalence over exactly the contexts reachable through the public
shipping surface. -/
def API.QueryCtxEquiv (api : API S) (query : S → R) (left right : S) : Prop :=
  query left = query right ∧
    ∀ context, api.Reachable context →
      query (left ⊔ context) = query (right ⊔ context)

theorem API.queryCtxEquivOn_iff_reachable [DecidableEq S] (api : API S)
    (query : S → R) (left right : S) :
    ContextCompiler.QueryCtxEquivOn api.contexts query left right ↔
      api.QueryCtxEquiv query left right := by
  constructor
  · intro h
    exact ⟨h.1, fun context hreachable =>
      h.2 context (api.reachable_mem_contexts hreachable)⟩
  · intro h
    exact ⟨h.1, fun context hmember =>
      h.2 context (api.contexts_sound hmember)⟩

/-- A `ContextCompiler.Spec` whose contexts are derived from the public API
rather than supplied independently. -/
def API.spec [DecidableEq S] (api : API S) (states : List S)
    (queries : List (S → R)) : ContextCompiler.Spec S R where
  states := states
  contexts := api.contexts
  queries := queries

/-- `ContextCompiler.signature_eq_iff`, instantiated with the shipping
coverage theorem: signature equality is sound and complete for every
configured query over every and only publicly reachable context. -/
theorem API.signature_eq_iff_reachable [DecidableEq S] (api : API S)
    (states : List S) (queries : List (S → R)) (left right : S) :
    (api.spec states queries).signature left =
        (api.spec states queries).signature right ↔
      ∀ query ∈ queries, api.QueryCtxEquiv query left right := by
  rw [ContextCompiler.signature_eq_iff]
  constructor
  · intro h query hquery
    exact (api.queryCtxEquivOn_iff_reachable query left right).mp
      (h query hquery)
  · intro h query hquery
    exact (api.queryCtxEquivOn_iff_reachable query left right).mpr
      (h query hquery)

namespace Fixtures

open Uwueave.Catalog

def emptyBool : GSet Bool := fun _ => false

/-- The public G-Set shipping surface exposes exactly the two singleton
packets.  Arbitrary histories of those deliveries still have four contexts. -/
def boolMembershipAPI : API (GSet Bool) where
  initial := emptyBool
  packets := [Delta.addDelta false, Delta.addDelta true]

def boolMembershipSpec : ContextCompiler.Spec (GSet Bool) Bool :=
  boolMembershipAPI.spec ContextCompiler.Fixtures.boolStates
    [MinimalSummary.memQuery true]

theorem bool_membership_context_count : boolMembershipAPI.contexts.length = 4 := by
  decide

theorem bool_membership_two_classes : boolMembershipSpec.classKeys.length = 2 := by
  decide

theorem bool_membership_signature_exact (left right : GSet Bool) :
    boolMembershipSpec.signature left = boolMembershipSpec.signature right ↔
      boolMembershipAPI.QueryCtxEquiv (MinimalSummary.memQuery true) left right := by
  simpa [boolMembershipSpec] using
    boolMembershipAPI.signature_eq_iff_reachable
      ContextCompiler.Fixtures.boolStates [MinimalSummary.memQuery true] left right

end Fixtures

end Uwueave.ShippingContextCompiler
