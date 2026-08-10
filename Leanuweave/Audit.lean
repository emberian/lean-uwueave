/-
# Leanuweave.Audit — the axiom ledger, enforced.

Every keystone theorem's axiom footprint is pinned with `#guard_msgs`: if a
future edit smuggles in `sorry` (the `sorryAx` axiom), `native_decide`
(`Lean.ofReduceBool`), or any other axiom, **the build fails** — this is a
gate, not a printout. The permitted floor is Lean's own three:
`propext`, `Classical.choice`, `Quot.sound`.

Two theorems are pinned axiom-FREE — the well-foundedness argument
(`grounded_acyclic`) and the derived-view SEC theorem (`derived_view_sec`)
are pure λ-calculus.
-/
import Leanuweave.Weave

/--
info: 'Leanuweave.Acyclicity.grounded_acyclic' does not depend on any axioms
-/
#guard_msgs in #print axioms Leanuweave.Acyclicity.grounded_acyclic

/--
info: 'Leanuweave.Move.derived_view_sec' does not depend on any axioms
-/
#guard_msgs in #print axioms Leanuweave.Move.derived_view_sec

/--
info: 'Leanuweave.escalation_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.escalation_witness

/--
info: 'Leanuweave.product_iconfluent' depends on axioms: [propext]
-/
#guard_msgs in #print axioms Leanuweave.product_iconfluent

/--
info: 'Leanuweave.pi_iconfluent' depends on axioms: [Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.pi_iconfluent

/--
info: 'Leanuweave.Catalog.gset_atMostOne_not_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Catalog.gset_atMostOne_not_iconfluent

/--
info: 'Leanuweave.Catalog.or_breaks_iconfluence' depends on axioms: [Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Catalog.or_breaks_iconfluence

/--
info: 'Leanuweave.Catalog.pncounter_nonneg_not_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Catalog.pncounter_nonneg_not_iconfluent

/--
info: 'Leanuweave.Catalog.lww_every_invariant_iconfluent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Catalog.lww_every_invariant_iconfluent

/--
info: 'Leanuweave.Catalog.lww_cross_field_not_iconfluent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Catalog.lww_cross_field_not_iconfluent

/--
info: 'Leanuweave.Catalog.escrow_local_bound_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Catalog.escrow_local_bound_iconfluent

/--
info: 'Leanuweave.Acyclicity.acyclicity_not_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Acyclicity.acyclicity_not_iconfluent

/--
info: 'Leanuweave.Acyclicity.grounded_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Acyclicity.grounded_iconfluent

/--
info: 'Leanuweave.Move.miniInterp_acyclic' depends on axioms: [propext]
-/
#guard_msgs in #print axioms Leanuweave.Move.miniInterp_acyclic

/--
info: 'Leanuweave.Move.view_not_stable' depends on axioms: [propext]
-/
#guard_msgs in #print axioms Leanuweave.Move.view_not_stable

/--
info: 'Leanuweave.Weave.active_path_not_iconfluent' depends on axioms: [Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Weave.active_path_not_iconfluent
