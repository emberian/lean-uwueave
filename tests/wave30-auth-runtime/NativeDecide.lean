import Wave30AuthRuntimeCommon
import Uwueave.TrustFloor

namespace Canary.Wave30.NativeDecide
theorem compiledEvaluator : (List.range 8).length = 8 := by native_decide
end Canary.Wave30.NativeDecide

#audit_floor_prefix Canary.Wave30.NativeDecide
