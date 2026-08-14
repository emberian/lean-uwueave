import Uwueave.TrustFloor

-- Root declarations in the file currently being elaborated have no imported
-- module index yet, but must still be rejected.
axiom unsoundCurrentRoot : False

#audit_floor_current
