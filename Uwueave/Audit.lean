/-
# Uwueave.Audit — the axiom ledger, enforced.

Every keystone theorem's axiom footprint is pinned with `#guard_msgs`: if a
future edit smuggles in `sorry` (the `sorryAx` axiom), `native_decide`
(`Lean.ofReduceBool`), or any other axiom, **the build fails** — this is a
gate, not a printout. The permitted floor is Lean's own three:
`propext`, `Classical.choice`, `Quot.sound`.

Pins cover KEYSTONES — the theorems a reader would cite — not proof
scaffolding. Many are pinned axiom-FREE (pure λ-calculus); count them with
`grep -c "does not depend"` rather than trusting a number written here to rot.
-/
import Uwueave.Weave
import Uwueave.ORSet
import Uwueave.Causality
import Uwueave.MVRegister
import Uwueave.Segmented
import Uwueave.Undo
import Uwueave.Delta
import Uwueave.Sequence
import Uwueave.ORMap
import Uwueave.Automata
import Uwueave.Authority
import Uwueave.ExecRefine

/--
info: 'Uwueave.Acyclicity.grounded_acyclic' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Acyclicity.grounded_acyclic

/--
info: 'Uwueave.Move.derived_view_sec' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Move.derived_view_sec

/--
info: 'Uwueave.escalation_witness' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.escalation_witness

/--
info: 'Uwueave.product_iconfluent' depends on axioms: [propext]
-/
#guard_msgs in #print axioms Uwueave.product_iconfluent

/--
info: 'Uwueave.pi_iconfluent' depends on axioms: [Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.pi_iconfluent

/--
info: 'Uwueave.Catalog.gset_atMostOne_not_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Catalog.gset_atMostOne_not_iconfluent

/--
info: 'Uwueave.Catalog.or_breaks_iconfluence' depends on axioms: [Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Catalog.or_breaks_iconfluence

/--
info: 'Uwueave.Catalog.pncounter_nonneg_not_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Catalog.pncounter_nonneg_not_iconfluent

/--
info: 'Uwueave.Catalog.lww_every_invariant_iconfluent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Catalog.lww_every_invariant_iconfluent

/--
info: 'Uwueave.Catalog.lww_cross_field_not_iconfluent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Catalog.lww_cross_field_not_iconfluent

/--
info: 'Uwueave.Catalog.escrow_local_bound_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Catalog.escrow_local_bound_iconfluent

/--
info: 'Uwueave.Acyclicity.acyclicity_not_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Acyclicity.acyclicity_not_iconfluent

/--
info: 'Uwueave.Acyclicity.grounded_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Acyclicity.grounded_iconfluent

/--
info: 'Uwueave.Move.miniInterp_acyclic' depends on axioms: [propext]
-/
#guard_msgs in #print axioms Uwueave.Move.miniInterp_acyclic

/--
info: 'Uwueave.Move.view_not_stable' depends on axioms: [propext]
-/
#guard_msgs in #print axioms Uwueave.Move.view_not_stable

/--
info: 'Uwueave.Weave.active_path_not_iconfluent' depends on axioms: [Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Weave.active_path_not_iconfluent

/-! ### Wave 2 — removable sets, causality, MV-register, segmentation -/

/--
info: 'Uwueave.merge_le_iff' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.merge_le_iff

/--
info: 'Uwueave.leq_antisymm' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.leq_antisymm

/--
info: 'Uwueave.MVRegister.view_antichain' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.MVRegister.view_antichain

/--
info: 'Uwueave.Segmented.iconfluent_iff_trivially_segmented' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Segmented.iconfluent_iff_trivially_segmented

/--
info: 'Uwueave.ORSet.orset_present_survives' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.ORSet.orset_present_survives

/--
info: 'Uwueave.ORSet.orset_present_not_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.ORSet.orset_present_not_iconfluent

/--
info: 'Uwueave.ORSet.clset_present_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.ORSet.clset_present_iconfluent

/--
info: 'Uwueave.ORSet.clset_cross_element_not_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.ORSet.clset_cross_element_not_iconfluent

/--
info: 'Uwueave.Causality.vclock_leq_iff' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Causality.vclock_leq_iff

/--
info: 'Uwueave.Causality.concurrent_merge_strict' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Causality.concurrent_merge_strict

/--
info: 'Uwueave.Causality.fork_evidence_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Causality.fork_evidence_iconfluent

/--
info: 'Uwueave.Causality.no_unilateral_evidence' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Causality.no_unilateral_evidence

/--
info: 'Uwueave.MVRegister.conflict_surfaces' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.MVRegister.conflict_surfaces

/--
info: 'Uwueave.MVRegister.resolution_is_a_write' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.MVRegister.resolution_is_a_write

/--
info: 'Uwueave.Segmented.budget_not_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Segmented.budget_not_iconfluent

/--
info: 'Uwueave.Segmented.budget_segmented' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Segmented.budget_segmented

/-! ### Wave 3 — undo/redo -/





/--
info: 'Uwueave.Undo.overwrite_supersedes' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Undo.overwrite_supersedes

/--
info: 'Uwueave.Undo.undo_restores' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Undo.undo_restores

/--
info: 'Uwueave.Undo.redo_restores' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Undo.redo_restores

/--
info: 'Uwueave.Undo.undo_conflicts_visibly' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Undo.undo_conflicts_visibly

/--
info: 'Uwueave.Undo.undo_does_not_silently_lose' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Undo.undo_does_not_silently_lose

/--
info: 'Uwueave.Undo.undo_preserves_history' depends on axioms: [Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Undo.undo_preserves_history

/--
info: 'Uwueave.Undo.redo_preserves_history' depends on axioms: [Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Undo.redo_preserves_history

/-! ### Wave 3 — delta-state soundness -/

/--
info: 'Uwueave.Delta.joinAll_append' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Delta.joinAll_append

/--
info: 'Uwueave.Delta.merge_joinAll' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Delta.merge_joinAll

/--
info: 'Uwueave.Delta.le_joinAll' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Delta.le_joinAll

/--
info: 'Uwueave.Delta.mem_le_joinAll' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Delta.mem_le_joinAll

/--
info: 'Uwueave.Delta.joinAll_le' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Delta.joinAll_le

/--
info: 'Uwueave.Delta.joinAll_perm' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Delta.joinAll_perm

/--
info: 'Uwueave.Delta.joinAll_dup' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Delta.joinAll_dup

/--
info: 'Uwueave.Delta.joinAll_redeliver' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Delta.joinAll_redeliver

/--
info: 'Uwueave.Delta.joinAll_group' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Delta.joinAll_group

/--
info: 'Uwueave.Delta.joinAll_batch' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Delta.joinAll_batch

/--
info: 'Uwueave.Delta.joinAll_append_merge' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Delta.joinAll_append_merge

/--
info: 'Uwueave.Delta.same_deltas_same_state' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Delta.same_deltas_same_state

/--
info: 'Uwueave.Delta.joinAll_packets' depends on axioms: [propext]
-/
#guard_msgs in #print axioms Uwueave.Delta.joinAll_packets

/--
info: 'Uwueave.Delta.addDelta_adds' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Delta.addDelta_adds

/--
info: 'Uwueave.Delta.addDelta_frame' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Delta.addDelta_frame

/--
info: 'Uwueave.Delta.addDelta_least' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Delta.addDelta_least

/-! ### Wave 3 — sequences -/

/--
info: 'Uwueave.Sequence.wf_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Sequence.wf_iconfluent

/--
info: 'Uwueave.Sequence.wf_unique_anchor_not_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Sequence.wf_unique_anchor_not_iconfluent

/--
info: 'Uwueave.Sequence.sequence_view_sec' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Sequence.sequence_view_sec

/--
info: 'Uwueave.Sequence.linearize_mem' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Sequence.linearize_mem

/--
info: 'Uwueave.Sequence.dup_id_appears_twice' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Sequence.dup_id_appears_twice

/--
info: 'Uwueave.Sequence.linearize_anchor_precedes' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Sequence.linearize_anchor_precedes

/--
info: 'Uwueave.Sequence.interleaving_anomaly' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Sequence.interleaving_anomaly

/--
info: 'Uwueave.Sequence.run_order_by_id' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Sequence.run_order_by_id

/--
info: 'Uwueave.Sequence.linearize_count_one' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Sequence.linearize_count_one

/--
info: 'Uwueave.Sequence.merged_head_exactly_once' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Sequence.merged_head_exactly_once

/-! ### Wave 4 — OR-Map, automata, authority, DSL seams, kernel refinement -/

/--
info: 'Uwueave.ORMap.present_iff_orset' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.ORMap.present_iff_orset

/--
info: 'Uwueave.ORMap.ormap_policies_agree_without_removes' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.ORMap.ormap_policies_agree_without_removes

/--
info: 'Uwueave.Automata.exec_perm' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Automata.exec_perm

/--
info: 'Uwueave.Automata.exec_dup' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Automata.exec_dup

/--
info: 'Uwueave.Automata.exec_redeliver' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Automata.exec_redeliver

/--
info: 'Uwueave.Automata.run_is_exec' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Automata.run_is_exec

/--
info: 'Uwueave.Authority.scope_le_root' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Authority.scope_le_root

/--
info: 'Uwueave.Authority.chain_scope_descends' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Authority.chain_scope_descends

/--
info: 'Uwueave.Authority.active_monotone_grants' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Authority.active_monotone_grants

/--
info: 'Uwueave.Spec.SegVerdict.escalatesGlobally' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Spec.SegVerdict.escalatesGlobally

/--
info: 'Uwueave.Spec.SegVerdict.freeWithinSeam' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Spec.SegVerdict.freeWithinSeam

/--
info: 'Uwueave.Spec.SegVerdict.staysInSeam' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Spec.SegVerdict.staysInSeam

/--
info: 'Uwueave.Spec.SegVerdict.toClash' does not depend on any axioms
-/
#guard_msgs in #print axioms Uwueave.Spec.SegVerdict.toClash

/--
info: 'Uwueave.Automata.exec_same_letters' depends on axioms: [propext]
-/
#guard_msgs in #print axioms Uwueave.Automata.exec_same_letters

/--
info: 'Uwueave.Automata.run_append_merge' depends on axioms: [propext]
-/
#guard_msgs in #print axioms Uwueave.Automata.run_append_merge

/--
info: 'Uwueave.Authority.authority_view_antitone' depends on axioms: [propext]
-/
#guard_msgs in #print axioms Uwueave.Authority.authority_view_antitone

/--
info: 'Uwueave.Authority.revocation_is_forever' depends on axioms: [propext]
-/
#guard_msgs in #print axioms Uwueave.Authority.revocation_is_forever

/--
info: 'Uwueave.Authority.duelling_revocations_not_iconfluent' depends on axioms: [Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Authority.duelling_revocations_not_iconfluent

/--
info: 'Uwueave.Authority.duelling_admins_annihilate' depends on axioms: [Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Authority.duelling_admins_annihilate

/--
info: 'Uwueave.Spec.mutexClash' depends on axioms: [Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Spec.mutexClash

/--
info: 'Uwueave.Automata.run_same_inputs' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Automata.run_same_inputs

/--
info: 'Uwueave.Automata.determinism_not_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Automata.determinism_not_iconfluent

/--
info: 'Uwueave.Automata.token_firings_segmented' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Automata.token_firings_segmented

/--
info: 'Uwueave.Automata.token_reallocation_not_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Automata.token_reallocation_not_iconfluent

/--
info: 'Uwueave.Automata.concurrent_firings_merge_legal' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Automata.concurrent_firings_merge_legal

/--
info: 'Uwueave.Authority.wf_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Authority.wf_iconfluent

/--
info: 'Uwueave.Authority.sole_admin_not_iconfluent' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Authority.sole_admin_not_iconfluent

/--
info: 'Uwueave.Authority.merge_only_revokes' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Authority.merge_only_revokes

/--
info: 'Uwueave.Spec.Verdict.keyedClash' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Spec.Verdict.keyedClash

/--
info: 'Uwueave.Spec.budgetSegVerdict' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Spec.budgetSegVerdict

/--
info: 'Uwueave.Spec.atMostOneClash' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Spec.atMostOneClash

/--
info: 'Uwueave.Exec.size_absReplay' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Exec.size_absReplay

/--
info: 'Uwueave.Exec.getWord_pushWord' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Exec.getWord_pushWord

/--
info: 'Uwueave.Exec.getWord_encodeView' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Exec.getWord_encodeView

/--
info: 'Uwueave.Exec.toI_ofI' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Exec.toI_ofI

/--
info: 'Uwueave.Exec.decode_encode_id' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Exec.decode_encode_id

/--
info: 'Uwueave.Exec.replay' depends on axioms: [propext, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Exec.replay

/--
info: 'Uwueave.ORMap.proj_merge' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.ORMap.proj_merge

/--
info: 'Uwueave.ORMap.ormap_get_survives' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.ORMap.ormap_get_survives

/--
info: 'Uwueave.ORMap.ormap_present_not_iconfluent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.ORMap.ormap_present_not_iconfluent

/--
info: 'Uwueave.ORMap.ormap_doomed_update' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.ORMap.ormap_doomed_update

/--
info: 'Uwueave.ORMap.ormap_policy_divergence' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.ORMap.ormap_policy_divergence

/--
info: 'Uwueave.Authority.wf_unique_not_iconfluent' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Authority.wf_unique_not_iconfluent

/--
info: 'Uwueave.Exec.absReplay_terminates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Exec.absReplay_terminates

/--
info: 'Uwueave.Exec.absReplay_acyclic' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Exec.absReplay_acyclic

/--
info: 'Uwueave.Exec.absReplay_chain_nodup' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Exec.absReplay_chain_nodup

/--
info: 'Uwueave.Exec.chainHits_decides' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in #print axioms Uwueave.Exec.chainHits_decides
