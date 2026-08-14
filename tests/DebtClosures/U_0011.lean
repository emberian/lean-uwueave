import Uwueave.HistoryPolicy
import Uwueave.CertificateScope

open Uwueave

/-! Compile-only probes over the full evidence/world chain at `Type 1`. -/

#check Catalog.GSet Type
#check Holes.Partial Type
#check Holes.Positioned Type Type Type
#check Evidence.ResultEvidence Type
#check Evidence.View Type
#check Evidence.FreeTermination (S := Type) (β := Type)
#check Evidence.SoundEvaluator (S := Type) (β := Type)
#check WorldFuture.World Type
#check WorldFuture.StateCert Type
#check WorldFuture.WorldCert Type

#check Histories.VersionDag Type
#check Histories.Origin Type
#check Histories.History Type Type Type
#check @Histories.HistorySafeFrom.{1, 1, 1}
#check HistoryBase.ValidInHistory (V := Type) (S := Type) (Op := Type)
#check HistoryBase.BasedWorld Type Type
#check HistoryBase.VersionCertSound (α := Type) (V := Type)
#check HistoryPolicy.HistoryMerge Type Type Type

#check CertificateScope.freeTermination_iff_residual (W := Type) (R := Type)
#check CertificateScope.residualSet (W := Type) (R := Type)
#check CertificateScope.KeyCertSound (W := Type) (R := Type) (K := Type)
#check CertificateScope.reachedWorlds (α := Type) (V := Type)
#check CertificateScope.sufficient_for_every_evaluator_iff_injective.{1, 1, 1}
  (W := Type) (K := Type) (fun x => x)

/-! Mixed probes prevent a superficially polymorphic API from unifying carrier,
state, operation, result, or key universes behind one shared level. -/

#check Holes.Positioned Nat Type (ULift.{2} Type)
#check Evidence.FreeTermination (S := Nat) (β := Type)
#check Evidence.FreeTermination (S := Type) (β := Nat)
#check Evidence.SoundEvaluator (S := Nat) (β := Type)
#check Evidence.SoundEvaluator (S := Type) (β := Nat)
#check WorldFuture.extension_stable_implies_delivery_stable (α := Nat) (β := Type)
#check WorldFuture.extension_stable_implies_delivery_stable (α := Type) (β := Nat)

#check Histories.History Nat Type (ULift.{2} Type)
#check @Histories.HistorySafeFrom.{2, 1, 0}
#check HistoryBase.ValidInHistory (V := Nat) (S := Type) (Op := ULift.{2} Type)
#check HistoryBase.BasedWorld Type Nat
#check HistoryBase.VersionCertSound (α := Type) (V := Nat)
#check HistoryPolicy.HistoryMerge Nat Type (ULift.{2} Type)
#check HistoryPolicy.ctxEquiv_of_eq (S := Nat) (R := Type)
#check HistoryPolicy.BaseRobustAt
  (V := Nat) (S := Catalog.GSet Type) (Op := ULift.{2} Type) (R := ULift.{2} Type)

#check CertificateScope.freeTermination_iff_residual (W := Nat) (R := Type)
#check CertificateScope.freeTermination_iff_residual (W := Type) (R := Nat)
#check CertificateScope.residualSet (W := Nat) (R := Type)
#check CertificateScope.KeyCertSound (W := Nat) (R := Type) (K := ULift.{2} Type)
#check CertificateScope.reachedWorlds (α := Type) (V := Nat)
#check CertificateScope.deliveryKey_residual_sub (α := Nat) (R := Type)
#check CertificateScope.sufficient_for_every_evaluator_iff_injective.{1, 0, 2}
  (W := Type) (K := Nat) (fun _ => 0)

theorem debtClosure_U_0011 : True := True.intro
