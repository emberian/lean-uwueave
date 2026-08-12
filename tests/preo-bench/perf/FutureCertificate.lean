import Uwueave.Preo.Elab

namespace PreoBench.FutureCertificate

open Uwueave Uwueave.Preo

preo Subject where
  field marker : Counter
  future Delivered on (Future.evidenceWorldModel Holes.Val) :=
    Future.Delivery Holes.Val

preo_certificate Certificate :
    Future.CheckedCertificate Subject.Delivered (fun _ => ())
      (fun _ => ()) (fun _ => True) Future.quiescedIndex := by
  refine { accepted := True.intro, soundForAll := ?_ }
  intro _ _ _ _
  rfl

end PreoBench.FutureCertificate
