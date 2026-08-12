/-
# AuthenticatedEraCertificateCommon — exact Wave-28 certificate fixture

The public production fixture keeps authentication, issuance, lawful frontier
advance, ERA announcement completeness, and exact-key reuse distinct.  These
test-only aliases give the subprocess canaries short, stable names without
adding anything to the public module tree.
-/
import Uwueave.AuthenticatedEraCertificate

namespace Canary.Wave28.AuthenticatedEraCertificateCommon

open Uwueave Uwueave.Catalog
open Uwueave.AuthenticatedEraCertificate

def verification : Verification Fixtures.advance := Fixtures.verification

def reusable : ReusableCertificate := verification.toReusableCertificate

def wrongKey : EraKey :=
  EraCertificate.eraKey EraCertificate.wAheadAll

theorem wrongKey_refused : ¬ reusable.Matches wrongKey := by
  intro hmatches
  apply EraCertificate.an_announcement_changes_the_name
  exact Eq.symm hmatches

end Canary.Wave28.AuthenticatedEraCertificateCommon
