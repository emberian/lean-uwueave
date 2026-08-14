import Uwueave.TrustFloor

-- An apparently-clean early audit cannot authorize declarations appended
-- later in the file.
#audit_floor_current

axiom unsoundAfterEarlyCurrentAudit : False
