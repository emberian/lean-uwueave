import Uwueave.TrustFloor

-- A typo or absent downstream namespace must never produce a green audit.
#audit_floor_prefix Canary.NamespaceThatDoesNotExist
