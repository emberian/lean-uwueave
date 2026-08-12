import Uwueave.TrustFloor

namespace Canary.NativeDecide

theorem compiledEvaluator : (List.range 8).length = 8 := by
  native_decide

end Canary.NativeDecide

#audit_floor_prefix Canary.NativeDecide
