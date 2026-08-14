import Uwueave.TrustFloor

-- A current declaration cannot hide by choosing a namespace unrelated to its
-- source module, matching the former Audit/Main ownership blind spot.
namespace Canary.ForeignNamespace

axiom unsoundCurrentForeignNamespace : False

end Canary.ForeignNamespace

#audit_floor_current
