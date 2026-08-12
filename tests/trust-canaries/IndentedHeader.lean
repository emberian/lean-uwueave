-- Regression: both Lean and the trust tooling must accept header whitespace.
  import Uwueave.TrustFloor

namespace Canary.IndentedHeader

theorem checked : (1 : Nat) = 1 := rfl

end Canary.IndentedHeader

#audit_floor_prefix Canary.IndentedHeader
