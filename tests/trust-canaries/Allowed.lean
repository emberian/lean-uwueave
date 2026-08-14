import Uwueave.TrustFloor

namespace Canary.Allowed

theorem checked : True := True.intro

/-- Exercise the largest ordinary member of the allowed floor, not merely the
empty-axiom case. -/
noncomputable def choose {α : Type} (inhabited : Nonempty α) : α :=
  Classical.choice inhabited

theorem propositionExtensionality {left right : Prop}
    (equivalent : left ↔ right) : left = right :=
  propext equivalent

theorem quotientSound {α : Sort _} {relation : α → α → Prop} {left right : α}
    (related : relation left right) :
    Quot.mk relation left = Quot.mk relation right :=
  Quot.sound related

end Canary.Allowed

#audit_floor_prefix Canary.Allowed

#audit_floor_current

-- Effective EOF permits trailing comments.
