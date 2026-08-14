import Uwueave.BoundedEraAnnouncement

theorem debtClosure_U_0033 :
    (∀ {available : List Uwueave.Era.Cut}
        {w : Uwueave.EraCertificate.EraWorld}
        (_hwf : Uwueave.EraCertificate.Wf w),
      Uwueave.BoundedEraAnnouncement.traceStableB available w = true ↔
        Uwueave.Evidence.FreeTermination
          (Uwueave.BoundedEraAnnouncement.AnnouncementWithin available)
          Uwueave.BoundedEraAnnouncement.finalTrace
          w)
      ∧ (∀ {w : Uwueave.EraCertificate.EraWorld}
        (_hwf : Uwueave.EraCertificate.Wf w)
        (available : List Uwueave.Era.Cut),
      ¬ Uwueave.BoundedEraAnnouncement.CoversUnrestricted available w) := by
  constructor
  · intro available w hwf
    exact Uwueave.BoundedEraAnnouncement.traceStableB_iff_freeTermination hwf
  · intro w hwf available
    exact Uwueave.BoundedEraAnnouncement.no_finite_pool_covers_unrestricted hwf available
