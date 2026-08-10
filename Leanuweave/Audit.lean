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
import Leanuweave.ORSet
import Leanuweave.Causality
import Leanuweave.MVRegister
import Leanuweave.Segmented
import Leanuweave.Undo
import Leanuweave.Delta

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

/-! ### Wave 2 — removable sets, causality, MV-register, segmentation -/

/--
info: 'Leanuweave.merge_le_iff' does not depend on any axioms
-/
#guard_msgs in #print axioms Leanuweave.merge_le_iff

/--
info: 'Leanuweave.leq_antisymm' does not depend on any axioms
-/
#guard_msgs in #print axioms Leanuweave.leq_antisymm

/--
info: 'Leanuweave.MVRegister.view_antichain' does not depend on any axioms
-/
#guard_msgs in #print axioms Leanuweave.MVRegister.view_antichain

/--
info: 'Leanuweave.Segmented.iconfluent_iff_trivially_segmented' does not depend on any axioms
-/
#guard_msgs in #print axioms Leanuweave.Segmented.iconfluent_iff_trivially_segmented

/--
info: 'Leanuweave.ORSet.orset_present_survives' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.ORSet.orset_present_survives

/--
info: 'Leanuweave.ORSet.orset_present_not_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.ORSet.orset_present_not_iconfluent

/--
info: 'Leanuweave.ORSet.clset_present_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.ORSet.clset_present_iconfluent

/--
info: 'Leanuweave.ORSet.clset_cross_element_not_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.ORSet.clset_cross_element_not_iconfluent

/--
info: 'Leanuweave.Causality.vclock_leq_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Causality.vclock_leq_iff

/--
info: 'Leanuweave.Causality.concurrent_merge_strict' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Causality.concurrent_merge_strict

/--
info: 'Leanuweave.Causality.fork_evidence_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Causality.fork_evidence_iconfluent

/--
info: 'Leanuweave.Causality.no_unilateral_evidence' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Causality.no_unilateral_evidence

/--
info: 'Leanuweave.MVRegister.conflict_surfaces' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.MVRegister.conflict_surfaces

/--
info: 'Leanuweave.MVRegister.resolution_is_a_write' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.MVRegister.resolution_is_a_write

/--
info: 'Leanuweave.Segmented.budget_not_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Segmented.budget_not_iconfluent

/--
info: 'Leanuweave.Segmented.budget_segmented' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Segmented.budget_segmented

/-! ### Wave 3 — undo/redo -/

/--
info: 'Leanuweave.Undo.mem_s01' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Undo.mem_s01

/--
info: 'Leanuweave.Undo.mem_s01u' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Undo.mem_s01u

/--
info: 'Leanuweave.Undo.mem_s01ur' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Undo.mem_s01ur

/--
info: 'Leanuweave.Undo.mem_s01uC' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Undo.mem_s01uC

/--
info: 'Leanuweave.Undo.overwrite_supersedes' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Undo.overwrite_supersedes

/--
info: 'Leanuweave.Undo.undo_restores' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Undo.undo_restores

/--
info: 'Leanuweave.Undo.redo_restores' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Undo.redo_restores

/--
info: 'Leanuweave.Undo.undo_conflicts_visibly' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Undo.undo_conflicts_visibly

/--
info: 'Leanuweave.Undo.undo_does_not_silently_lose' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Undo.undo_does_not_silently_lose

/--
info: 'Leanuweave.Undo.undo_preserves_history' depends on axioms: [Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Undo.undo_preserves_history

/--
info: 'Leanuweave.Undo.redo_preserves_history' depends on axioms: [Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Undo.redo_preserves_history

/-! ### Wave 3 — delta-state soundness -/

/--
info: 'Leanuweave.Delta.joinAll_append' does not depend on any axioms
-/
#guard_msgs in #print axioms Leanuweave.Delta.joinAll_append

/--
info: 'Leanuweave.Delta.merge_joinAll' does not depend on any axioms
-/
#guard_msgs in #print axioms Leanuweave.Delta.merge_joinAll

/--
info: 'Leanuweave.Delta.le_joinAll' does not depend on any axioms
-/
#guard_msgs in #print axioms Leanuweave.Delta.le_joinAll

/--
info: 'Leanuweave.Delta.mem_le_joinAll' does not depend on any axioms
-/
#guard_msgs in #print axioms Leanuweave.Delta.mem_le_joinAll

/--
info: 'Leanuweave.Delta.joinAll_le' does not depend on any axioms
-/
#guard_msgs in #print axioms Leanuweave.Delta.joinAll_le

/--
info: 'Leanuweave.Delta.joinAll_perm' does not depend on any axioms
-/
#guard_msgs in #print axioms Leanuweave.Delta.joinAll_perm

/--
info: 'Leanuweave.Delta.joinAll_dup' does not depend on any axioms
-/
#guard_msgs in #print axioms Leanuweave.Delta.joinAll_dup

/--
info: 'Leanuweave.Delta.joinAll_redeliver' does not depend on any axioms
-/
#guard_msgs in #print axioms Leanuweave.Delta.joinAll_redeliver

/--
info: 'Leanuweave.Delta.joinAll_group' does not depend on any axioms
-/
#guard_msgs in #print axioms Leanuweave.Delta.joinAll_group

/--
info: 'Leanuweave.Delta.joinAll_batch' does not depend on any axioms
-/
#guard_msgs in #print axioms Leanuweave.Delta.joinAll_batch

/--
info: 'Leanuweave.Delta.joinAll_append_merge' does not depend on any axioms
-/
#guard_msgs in #print axioms Leanuweave.Delta.joinAll_append_merge

/--
info: 'Leanuweave.Delta.same_deltas_same_state' does not depend on any axioms
-/
#guard_msgs in #print axioms Leanuweave.Delta.same_deltas_same_state

/--
info: 'Leanuweave.Delta.joinAll_packets' depends on axioms: [propext]
-/
#guard_msgs in #print axioms Leanuweave.Delta.joinAll_packets

/--
info: 'Leanuweave.Delta.addDelta_adds' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Delta.addDelta_adds

/--
info: 'Leanuweave.Delta.addDelta_frame' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Delta.addDelta_frame

/--
info: 'Leanuweave.Delta.addDelta_least' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Leanuweave.Delta.addDelta_least
