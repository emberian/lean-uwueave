/-
# Uwueave.Preo.Elab.Certificate — named future-certificate command core.

No command elaborator is registered here.  The facade owns the single public
registration and delegates to `elabPreoCertificateCore`.
-/
import Uwueave.Preo.Elab.Internal
import Uwueave.Preo.Future

namespace Uwueave.Preo.Elab.Certificate

open Lean Elab Command Uwueave.Preo.Elab.Internal

/-- Non-registered implementation of `preo_certificate`. -/
def elabPreoCertificateCore : CommandElab := fun stx => withEnvTransaction do
  let `(command| preo_certificate $nm : $ty := $proof) := stx
    | throwError "preo_certificate: malformed declaration"
  unless ← isCheckedCertificateType ty do
    throwErrorAt ty "preo_certificate: the declared type must reduce to \
      `Uwueave.Preo.Future.CheckedCertificate ...`. Write the complete future, \
      answer, key, certificate predicate, and exact `WorldIndex`; this command \
      does not infer any of them from materialized state or from the proof."
  emitRequired (← `(command|
    /-- A named, proof-carrying certificate at its explicitly written world. -/
    def $nm : $ty := $proof))
  let ns ← getCurrNamespace
  floorCheck nm "named future certificate" (ns ++ nm.getId)

end Uwueave.Preo.Elab.Certificate
