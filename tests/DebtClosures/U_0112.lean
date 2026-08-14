import Uwueave.ShippingContextCompiler

open Uwueave
open Uwueave.ShippingContextCompiler

universe u v

theorem debtClosure_U_0112 :
    (∀ {S : Type u} [MergeState S] [DecidableEq S]
      (api : API S) (context : S), api.Reachable context →
        context ∈ api.contexts) ∧
    (∀ {S : Type u} [MergeState S]
      (api : API S) (context : S), context ∈ api.contexts →
        api.Reachable context) ∧
    (∀ {S : Type u} {R : Type v} [MergeState S] [DecidableEq S]
      (api : API S) (states : List S) (queries : List (S → R))
      (left right : S),
      (api.spec states queries).signature left =
          (api.spec states queries).signature right ↔
        ∀ query ∈ queries, api.QueryCtxEquiv query left right) ∧
    Fixtures.boolMembershipAPI.contexts.length = 4 ∧
    Fixtures.boolMembershipSpec.classKeys.length = 2 := by
  exact ⟨fun api context h => api.reachable_mem_contexts h,
    fun api context h => api.contexts_sound h,
    fun api states queries left right =>
      api.signature_eq_iff_reachable states queries left right,
    Fixtures.bool_membership_context_count,
    Fixtures.bool_membership_two_classes⟩
