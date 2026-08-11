# TRANSPORTS

> **The library is a map of judgements and the exact hypotheses under which
> evidence transports between them.**

That sentence is not ours. An external reviewer (codex) read four findings we
had reported as four unrelated surprises and gave them one diagnosis:

> *Each is a transport theorem that everyone expected to hold, but whose missing
> hypothesis became visible only when two previously separate models were
> composed.*

This file is that map. Every row names a **source judgement**, a **target
judgement**, the **transport** between them, the **hypothesis** the transport
rests on, and — the part that makes a row worth writing — the **counterexample
without that hypothesis**. A row with no counterexample is a row we have not
finished.

Read it as the answer to *"is this one thing?"*. It is one thing **exactly
when these crossings are first-class**.

**Ledger total: 108 numbered transport rows.**

---

## How to read a row

| field | meaning |
|---|---|
| **transport** | the theorem, if the crossing holds |
| **needs** | the load-bearing hypothesis — remove it and the row is false |
| **without it** | the concrete refutation, in this tree, checkable |
| **status** | ✅ proved · ⚠ refuted-and-repaired · ✗ refuted, no repair yet · ◻ unbuilt |

A ⚠ row is the most valuable kind: something everyone assumed, refuted, then
recovered under a named condition.

---

## I. The core judgement and its execution model

**1. I-confluence → coordination-freedom** ✅
*transport* `Necessity.iconfluent_implies_cfcs` · *needs* nothing beyond the
model · *without it* — n/a; this direction is unconditional.

**2. Clash → no coordination-free implementation** ⚠
*transport* `Necessity.necessity` · *needs* **reachability** — the clash must be
attained by a causal history · *without it* a lattice-only pair refutes nothing;
`CausalReach.orset_reachability_depends_on_remove_shape` shows the same lattice
pair is Live under tag-scoped removes and **unreachable** under element-wide
ones, so the op vocabulary decides.

**3. Coordination-freedom ⟷ local safety + no reachable clash** ✅
*transport* `ForkGrade.cfcs_iff_locallySafe_and_no_reachableClash` · both
directions · *needs* nothing; it is the definitional unfolding nobody had
written.

**4. Sequential clash → concurrent clash** ✅
*transport* `Bounds.reachableClash_of_clashBlock` (idle one replica) · **no
converse** — an inflationary step admits concurrent clashes and no sequential
ones, which is row 9's whole story.

**4a. Outcome-valued coordination-freedom → its two exact components** ⚠
*source* `Specification.CoordinationFree R P` · *target*
`Specification.HistoryMonotone R P ∧ Specification.FiberDirected R P` ·
*transport* `Specification.coordinationFree_iff_historyMonotone_and_fiberDirected`
· *needs* **`Specification.Total P`**, only in the source-to-history-monotone
direction; the converse and the fiber-directed projection need no totality ·
*without it* `Specification.zeroAbsent_iconfluent` transports through
`invariant_coordinationFree_iff` while
`zeroAbsent_not_historyMonotone` refutes history monotonicity at the concrete
extension `emptyNatSet ⊑ zeroNatSet`. Independently, total, refinement-closed,
history-monotone `branchingBoolSpec` is not coordination-free
(`branchingBoolSpec_not_coordinationFree`), so the fiber-directed conjunct is
also load-bearing; `emptySpec_coordinationFree` /
`emptySpec_not_nonvacuous` records the separate vacuity failure.

---

## II. Quantitative ⟷ modal

**5. Per-stream floor zero → coordination-freedom available** ✗ **REFUTED**
*would-be transport* "the forced floor is 0, so no coordination is needed" ·
*without it* `Bounds.zero_floor_does_not_imply_cfcs` — `pinStep` is
inflationary, so **every** clash decomposition of **every** pin stream is empty
and no positive floor exists, yet **no implementation capable of the two pins is
CFCS**. Our own documents invited this misreading.

**6. Fork-scenario optimum zero ⟷ no live clash** ⚠ **the repair for row 5**
*transport* `ForkGrade.liveScenario_optimum_eq_zero_iff_no_live_clash` · *needs*
the constant seam to be admissible — **only for the reverse direction**; the
forward holds over every strategy space · *without it*
`ForkGrade.const_seam_live_but_not_global` — a live strategy paying 0 that is
not a global seam.

**7. Coordination-freedom ⟷ every finite scenario costs zero** ✅
*transport* `ForkGrade.cfcs_iff_locallySafe_and_all_finite_scenarios_zero` ·
*needs* nothing on the reverse — a reachable clash replays as a two-branch
scenario. The honest quantitative degeneration of the modal judgement, and the
resolution of row 5: `ForkGrade.the_disagreement_resolved` puts per-stream 0
and fork-aware 1 on one carrier, one step, one start.

**8. Modal + quantitative, composed** ✅
*transport* `Bounds.coordination_necessary_and_costly` · *needs*
`Realizes impl step s b` — the implementation can commit the block · *without
it* the two models quantify over different things;
`Bounds.totalImpl_realizes` discharges it for every stream.

---

## III. Cost and its operational meaning

**9. Legal workload → operationally meaningful workload** ⚠
*would-be transport* "a `Budget.Workload` prices a real execution" · *without
it* `Bounds.ew_rejected_at_zero_over_unreachable_pair` — a legal workload
carries `ForcedFloor 1` whose accused pair is the element-wide OR-Set clash
**proved unreachable**, and `Budget.rejected_sound` then says *no plan fits, in
any universe*. `RunLegal` checks occupied states are **legal**; nothing checked
they were **reachable**.

**10. `Cost` floor → live floor** ⚠ **the repair for row 9**
*transport* `LiveCost.cost_floor_becomes_live` · *needs* **`Grounds P step`** —
a total simulation of the abstract step by the model · *without it*
`LiveCost.ewTeleport_not_grounded`: source judgement holds, hypothesis refuted,
no target object exists.
⚠ *and the honest note*: `LiveCost.totalModel_grounds_everything` — transporting
into the total-state model buys **nothing**. The hypothesis has teeth only
against a model that **refuses** transitions. The repair's content is that the
model is now a declared parameter.

**10a. Carrier-global verdict → live verdict** ⚠ **row 10 at the level the
operator reads**
*transport* `LiveBudget.carrierGlobal_promotes`, and
`LiveBudget.LiveObligation.closedByReachability` at the verdict level · *needs*
**`LiveBudget.ReachabilityComplete P awl`** — `LiveCost.Grounds P awl.step` plus a
start world observing `awl.start` (the extra field is forced by `World` being
permitted to be richer than the state) · *without it*
`LiveBudget.carrier_global_rejection_is_not_live` refutes the unconditional claim
outright at `ewModel` / `ewWorkloadOR4`: the source judgement holds
(`ewOR4_forced_floor_one`), the hypothesis is refuted
(`ew_not_reachabilityComplete`), and the target object **cannot exist** —
`ew_no_live_realization`, whence `ew_verdicts_are_never_live`: no verdict for that
deployment is a live rejection or an acceptance, at any budget.
⚠ *and what the split buys*: `Bounds.ewRejectedAtZero` is a
`BudgetVerdict.rejected` reading *no plan fits, in any universe*;
`LiveBudget.ewCarrierGlobalAtZero` is a different constructor reading *the
abstract lattice model charges this path; operational realizability not
established* (`LiveBudget.claim_sound` proves each report's own claim, totally).
⚠ *and the honest note*, inherited from row 10:
`LiveBudget.totalModel_reachability_complete` — every workload is
reachability-complete for its own total-state model, so promoting there is free.

**11. Global seam → live seam** ⚠ **the second hole**
*source* carrier-global `SegmentedIConfluent σ I` · *target*
protocol-relative `LiveSegmented P σ I` · *transport*
`LiveSegmented.segmented_implies_liveSegmented` (one line) · *needs* no extra
hypothesis because the source quantifies over strictly more pairs · *without
the converse*
`LiveSegmented.witness_one_latticeOnly_clash` — a seam that is live-valid and
globally refuted, refuted **exactly** at an unreachable pair. And it costs:
`live_optimum_strictly_below_global_optimum` — live width **2**, global width
**3**, both least, with `the_third_domain_is_charged_for_an_unreachable_pair` as
the audit trail.
⚠ *the exact crossing gap is now inhabited too*:
`CliqueLive.atMostTwo_live_global_crossing_gap` gives one three-branch scenario
where an honest live strategy costs **0**, every global seam into the same
`Fin 3` costs at least **1**, and `sigmaTwoOneCross_segmented` attains **1**.
Its concrete failure is `atMostTwo_generators_do_not_clash`: all generator
pairs merge legally, but their triple join is illegal, so global fiber closure
charges a crossing the live pairwise world graph cannot see.
⚠ *and*: `workload_crossings_coincide` + `clashBlocks_head_coReachable` prove
**the crossings floors were never the hole** — the hole was the strategy space.

**12. Seam algebra → live seam algebra** ⚠ ten rows, each a theorem
Product, `linked_segmented`, `seam_substitute`, `absorb_free_field` survive —
three with **weakened** hypotheses. Refinement **fails** live as it does
globally (with a stronger witness: the refuting pair is a genuine fork).
`left_only_seam_iff` **fails** if you keep the global `IConfluent`
(`live_left_only_seam_iff_needs_liveIConfluent`). Full table in
`LiveSegmented.lean` §8.

**13. Colouring → segmentation** ⚠
*transport* `SeamColoring.segmented_iff_properColoring` · characterizes the
**safety clause exactly** and the closure clause **not at all** · *without the
residual* `coloring_alone_does_not_segment` — an edgeless graph where every
projection is proper and the invariant still is not segmented.
⚠ *and the live version improves*: `LiveSegmented.liveSegmented_iff_liveProperColoring`
needs **no covering pool**, because the live vertex set is the quantifier's own
domain.

**13a. Carrier-global clique → live clique, width, and scenario floor** ⚠
*transport* `CliqueLive.liveClique_of_clique` turns a global clique of observed
states into a `LiveClique`; from there `live_clique_forces_live_width` gives the
domain lower bound, while `live_clique_forces_scenario_floor` charges
`k - 1` to a fork scenario whose endpoints form the clique · *needs*
**pairwise `CoReachable` from one base** for the global-to-live step (scenario
endpoints get this for free from `liveClique_of_stream_clique`), and an
`Admissible` live-strategy space to state the optimum · *without it*
`slot_global_clique_three` coexists with `no_live_triangle`: the global clique
has size 3 while the two-operation protocol has live width 2, and
`no_three_stream_clique` proves the globally priced three-branch workload cannot
be run. `the_third_op_restores_the_third_domain` supplies the missing operation
and raises both the live clique and live optimum back to 3.

**13b. Universal crossing floor + certified predictive seam → exact optimum** ⚠
*source* the lower bound `Cost.unlinked_floor_is_two` plus a concrete seam ·
*target* an attained exact crossing optimum for the unlinked two-field workload
· *transport* `Cost.unlinked_optimum_is_two` · *needs*
`Cost.unlinkedPredictive_segmented` and the executable, decidable segment
carrier `Vector Bool 10 × Nat`; the legacy window records exactly values
`11 … 20`, while the allocation component records the independently moving
quota share · *without that predictive certificate* the canonical
`(version, allocation)` seam pays **4** (`Cost.linked_halves_the_crossings`),
although `Cost.unlinkedPredictive_cost` pays **2**. Thus a proved floor alone
does not identify an achieving plan, and the obvious seam is a concrete
non-optimum witness.

---

## IV. Merge models

**14. Two-way I-confluence → ancestral confluence** ✗ **REFUTED, both ways**
*without it* `Ancestral.iconfluent_does_not_imply_ancestral` — `n ≤ 1` passes
two-way under `max` because max **drops a committed spend**. The missing
notion is **effect-faithfulness**: I-confluence is a property of the merge, not
of the semantics. Converse also refuted:
`Ancestral.lock_ancestral_confluent` + `lock_no_update_preserving_join`.

**15. Resurrection clash → repairable by an ancestor** ⚠
*transport* `Recoverable.faithful_stepConfluent_iff_legalSerialization` — an
**iff**, with the merge **constructed** · *needs* delta-recoverability + a legal
serialization + a symmetric chooser · *without the last*
`comm_forces_symmetric_chooser` shows it is **entailed** by `AncestralMerge.comm`,
not assumed · *boundary* `Recoverable.budget_boundary` — the counter satisfies
**every** hypothesis and fails only `LegalSerialization`.

**15a. Costed delta recovery → executable constructed merge with a work bound** ⚠
*source* `Recoverable.CostedDeltaRecoveryOn g Step`, whose `program_correct`
executes the inherited recovery and whose `work_eq_program_length` ties cost to
the actual instruction list · *target* `costedAncestralMergeOf D C`, its
executable `constructedMergeProgram`, and a bound on
`constructedMergeWork` · *transport*
`Recoverable.executeConstructedMerge_eq`,
`constructedMergeProgram_length`, and `constructedMergeWork_le_max`; a uniform
recovery bound crosses via `constructedMergeWork_le_of_recovery_bound`, while
semantic correctness is retained by `costedAncestralMergeOf_serializing` and,
under the invariant premises, `costedAncestralMergeOf_stepConfluent` · *needs*
`[DecidableEq S]` and a `SymmetricChooser S`; the invariant target additionally
needs `Discerning D.erase C I` and `LegalSerialization g I` · *without the
program certificate* correctness supplies no cost at all:
`Recoverable.lockRecovery_arbitrarily_expensive` pads the **same** semantic
lock recovery to every requested lower bound, and
`paddedLockConstructedMerge_both_moved_work` transports the padding unchanged
to the concrete both-moved merge (`n + 1` work). Thus no cost-free reading can
be inferred from delta-recovery correctness alone.

**16. One fork-and-join → repeated history** ✗ **REFUTED**
*without it* `Histories.repeated_merge_breaks_the_invariant` — a *coherent*
history with a legal root and an illegal node. Diagnosed:
`AncestralConfluentFrom` **holds** while `MergeClosedFrom` **fails**, because a
merge **result** is not op-reachable from the base. **The break is the closure,
not the merge.**
⚠ *partial repair* `Histories.History.Coherent.sound` (sufficient, not proved
necessary) and `HistoryBase.coherent_sound_of_runRealized` (needs **no** merge
law, no closure, no confluence).

**16a. Local extension safety → safety of every coherent history node** ✅
*source* `Histories.HistorySafeFrom M impl I rho`, the origin-indexed
`ExtensionSafe` obligation over every coherent history rooted at `rho` ·
*target* legality of every node of every such history · *transport*
`Histories.historySafeFrom_iff`, an exact iff · *needs* the recorded root
equality and `H.Coherent M impl`; no reachability-closure or confluence premise
appears in the iff. The older sufficient route is precisely
`mergeClosed_implies_historySafeFrom` · *without exact extension safety*
`Histories.counter_not_historySafeFrom` gives the concrete coherent
criss-cross history whose `joinLeft` node is `5 > 4`, while
`base_accident_is_exact_step` shows the alternate recorded base passes.
`counter_historySafe_true_and_not_mergeClosed` is the complementary inhabited
counterexample: `MergeClosedFrom` fails although exact history safety holds, so
the old closure package is load-bearing only for that sufficient route, not for
the target judgement itself.

**17. State-level base validity → history-level** ⚠
*transport* `HistoryBase.ValidInHistory` · *without it* three witnesses in both
directions, incl. `state_unavailable_fires_where_the_dag_hands_a_base` — the
state-level `unavailable` is valid while the DAG hands you a **direct parent of
both**. The two obligations are **logically independent**.
✅ *and* `HistoryBase.coherent_never_unavailable`: `unavailable` is a
**cross-history** answer, never satisfiable while walking one coherent history.

**17a. Explicit finite DAG enumeration → certified base search and policy check** ⚠
*source* a duplicate-free, covering `FiniteHistory.Enumeration D` · *target*
decidable `Histories.Reaches`, proof-carrying `Histories.BaseSelection` answers
with an exhaustive common-ancestor list, and exact all-pairs legality for a raw
`MergeModel.BaseDecision` selector · *transport*
`FiniteHistory.reaches_iff_bounded` justifies the rank-bounded backward search,
`mem_commonCandidates_iff` makes the filtered candidate list exact, and
`policyAccepted_iff` specifies `checkPolicy` on every enumerated ordered pair.
`toDecision_valid` separately erases a certified `BaseSelection` to the raw
decision while preserving exact lowest/maximal/unavailable legality; the
explicit sweep covers every carrier pair by `sweepEntries_complete` · *needs*
`[DecidableEq V]`, the supplied covering list, its `Nodup` proof, and the
existing rank-grounded `VersionDag`; rank is a search bound, not an algorithm
for discovering the graph. The executable branches are exact:
`cc_root_pair_decision` returns `.selected .root`,
`cc_merge_pair_decision` retains `.ambiguous .left .right`, and
`two_pair_decision` returns `.unavailable` only for the edgeless pair ·
*without a certified constructor* `searchCertified` returns `none` rather than
relabelling failure as unavailable, and
`cc_nonlowest_selected_rejected` refuses an arbitrary one of two criss-cross
maximal bases. This is finite and policy-relative: it does not enumerate an
arbitrary or infinite DAG, construct a `HistoryPolicy.HistoryMerge`, or prove
the separate `BaseRobust`/`SelectorSafe` semantic judgements.

**18. Invariant safety → convergence** ✗ **REFUTED**
*without it* `Histories.swap_never_converges` — an eternal two-cycle under a
base policy `MergeModel.BaseDecision.Valid` fully licenses. Safety is not
agreement.

**18a. Same append-only record → same derived view** ⚠ **the convergence
repair**
*transport* `HistoryPolicy.recordDetermined_converges` proves
`HistoryConvergent P` · *needs* exactly **`RecordDetermined P`**: the selector
must be a function of the record rather than of a previously materialized merge
result · *without it* `HistoryPolicy.nosy_diverges` gives two `SameRecord`
histories with unequal views and proves both `¬ HistoryConvergent ccNosy` and
`¬ RecordDetermined ccNosy`.
⚠ *separate order crossing*: `HistoryPolicy.replicas_agree_on_order` needs
both `SelectorSymmetric P` **and** `ReconcileSymmetric P`; these are not
hypotheses of `recordDetermined_converges`, and merge commutativity does not
supply them for an arbitrary policy. `the_swap_is_order_dependence` /
`self_base_selector_not_symmetric` witness the failure, while
`the_self_base_policy_is_not_history_licensed` shows `ValidInHistory` rejects
the very self-base decisions the state-level licence admitted.

---

## V. Computation

**19. Monotone summary → mergeable summary** ✗ **REFUTED**
*without it* `JoinHom.monotone_not_joinHom` (cardinality) and, quantified over
**every** binary combiner, `no_count_merge_without_provenance`: the pair `(1,1)`
must mean 1 when replicas saw the same element and 2 when they saw different
ones.
⚠ *the correct transport* `JoinHom.summaryFold_iff_joinHom` — folding shipped
summaries agrees with the truth **iff** the summary is a join homomorphism.

**20. Result invariant → source invariant (pullback)** ⚠
*transport* `JoinHom.iconfluent_pullback_of_joinHom` · *needs* `JoinHom` —
**or**, weaker and often enough, upward-closure of the result invariant
(`iconfluent_pullback_of_monotone`) · *without either*
`monotone_pullback_can_fail`: `(· ≤ 1)` is I-confluent on `Nat`-under-max and
its pullback along monotone `card` is not.

**20a. Typed expression structure → sufficient dependencies and semantic laws** ⚠
*source* an intrinsically typed `Preo.Expr.Term Γ t`, its structural holes,
or a proof-carrying `MergeSafe`/`MonotoneSafe` certificate · *target* exact
field-dependency sufficiency, `PreservesMerge`, or semantic `Monotone`
respectively · *transport* `Preo.Expr.Term.eval_ext` proves environments that
agree on `Term.reads` evaluate equally;
`Term.dependency_iff_positional_hole` makes every reported dependency exactly
a positional field or declared opaque hole. `MergeSafe.sound` and
`MonotoneSafe.sound` erase the structural certificates to their semantic laws
· *needs* the typed schema and constructor rules; an opaque `CustomNode` must
declare dependencies and prove read-extensionality, and any positive algebraic
classification of it must be supplied explicitly · *without a sound
constructor* `negatedMembership_not_monotone` and
`summedFields_not_preservesMerge` separate tempting Boolean/addition forms;
`malformed_not_classified` rejects an ill-typed raw negation, while
`opaque_not_auto_mergeSafe` refuses to infer a hidden homomorphism. The positive
analyses are intentionally incomplete, and this is not yet a surface-language
transport: `Preo.Syntax` and `Preo.Elab` do not import or elaborate these terms.

**21. Evidence → coarsest sufficient summary** ✅
*transport* `MinimalSummary.ctxQuot_coarsest_sufficient` — universal property
**proved** · *needs* `ctxEquiv_join` (congruence under adding context), which is
what makes the quotient carry a `MergeState` so **sufficiency and mergeability
never trade off**.

**22. Merge-context sufficiency → future-context sufficiency** ⚠ **same shape,
different observation**
*transport* both are kernels of an observation
(`CertificateScope.sufficientKey_iff_sufficientFor`), which is why the universal
property is cheap here · *without the analogue*
`residual_is_not_a_join_congruence` refutes `ctxEquiv_join`'s counterpart, so
the residual quotient carries **no merge** and the no-trade-off property
**fails** at the future index.

**22a. Rendered text → result-mergeable summary** ✗ **REFUTED**
*would-be transport* “the visible string is derived, so replicas may gossip and
merge it” · *needs* result-determinacy / incremental mergeability (equivalently
a suitable combiner; folding through a target lattice additionally needs a
`JoinHom`) · *without it* `TextSummary.no_text_merge_without_provenance`
hands every combiner the same two rendered inputs and requires two different
merged outputs, `ba` and `ab`; `witnesses_wf` proves the states and merges are
well formed. Thus `text_not_incrementallyMergeable`, `text_not_resultDetermined`,
and `text_not_joinHom` rule out all three readings.
⚠ *the repair* `text_architecture_is_forced`: retain and replicate the op-set
evidence (`opset_sufficient`) and derive the view; the evidence architecture is
free while merging rendered results is impossible.

**22b. Live elements after tombstone GC → sufficient text evidence** ✗
**REFUTED**
*would-be transport* any summary factoring through `garbageCollected 5` is
sufficient for `text 5` · *needs* a restriction on admissible future contexts,
such as causal stability; that restriction is **not modelled here** · *without
it* `TextSummary.no_gc_summary_sufficient`, powered by
`tombstones_are_load_bearing`, gives two currently identical, well-formed,
anchor-closed replicas that a normal peer later separates: dropping the
tombstone resurrects the deleted character. The partial converse is exact but
narrower: `tombstoned_content_never_read` permits dropping a deleted glyph's
content, not its positional identity.

**22c. Separating witness under an order policy → `needsEvidence`** ✅
*transport* `TextSummary.rendered_order_requiresEvidence` · *needs* a pair that
renders the same now and a context whose merges render differently · *without
the separating context* the conclusion is false in general (a constant renderer
is incrementally mergeable by the constant combiner). The worked theorem
`verdict_order_policy_invariant` instantiates the schema for **two concrete
cores**, RGA and Fugue: they choose opposite merged orders and both require
evidence. It is not a universal theorem over every order policy.

---

## VI. Evidence, futures, certificates

**23. Extension-stable → delivery-stable** ✅
*transport* `Evidence.extension_stable_implies_delivery_stable`, because
delivery ⊆ extension · **converse refuted**
(`Evidence.futures_not_interchangeable`).

**24. Exact under a larger future → exact under a smaller** ✅
*transport* `ResultStatus.exact_weakens` — from bare relation inclusion, **zero
axioms**; `Evidence`'s own theorem is *recovered* as an instance · **converse
refuted** with an inhabited witness (`exact_does_not_strengthen`).

**25. State-indexed certificate → reusable certificate** ✗ **REFUTED**
*without it* `WorldFuture.no_sound_state_cert_accepts_openW` — every sound
state-indexed certificate must **refuse** the state at which a replica correctly
verified settlement, because another world over the same state is unsettled.
⚠ *the repair* `CertificateScope.key_licenses_reuse` — a **future-sufficient
key**. And which keys work is not a matter of taste:
`frontierEpoch_not_sufficient` (our own refutation of codex's first remedy),
`pool_not_sufficient`, `deliveryKey_sufficient` = **observation with pool, epoch
droppable**, `root_scope_not_sufficient`, `base_scope_sufficient`.

**26. `Evidence.Closed` → sound delivery certificate** ✗ **REFUTED for the view**
*without it* `CertificateScope.closed_is_not_a_sound_delivery_certificate` — a
closed world renders `exact 47` and **one delivery later** renders
`provisional 47`, because the roster lives in the pool. Sound for the **values**;
unsound for the **view**.
⚠ *the repaired transport* `CertificateScope.closed_and_rosterKnown_licenses_render`
· *needs* both `Evidence.Closed (observe w)` and `RosterKnown w`; the first
freezes candidate values and the second proves every delivery future has the
same closure bit. `Evidence.render_congr` then transports the rendered view.
The counterexample above proves neither premise may be silently read as the
other.

**27. Capability declaration → property of the computation** ✗ **REFUTED**
*without it* `ResultStatus.declaration_is_relative_to_the_reach` — the same
evaluator and the same declaration, satisfied over one reachable set and refuted
over that set closed under a **single** admissible extension. A capability is a
property of a computation **over a reach**.

**27a. Abstract collapse licence → Era finalisation certificate** ⚠
*transport* `EraCertificate.era_cut_licenses_the_collapse` gives
`Holes.Stable (arriving w u) (roleAnswer u w)`, and
`era_finalisation_is_a_sound_certificate` states the same delivery-only result
as `CertificateScope.KeyCertSound` · *needs* **`Settled w`** — every event the
arbiter named has arrived — and the **delivery axis only** · *without
settlement* `delivery_alone_does_not_license_the_finalised_view` gives an
announced-but-undelivered event that moves `finalView` under delivery.
⚠ *axes not transported*: `the_cut_axis_breaks_the_seal` shows an announcement
moves the finalised view even at a quiesced, settled world;
`backdated_cut_rewrites_the_finalised_view` refutes dishonest/backdated cut
growth; and `an_event_born_finalised_rewrites_the_view` shows issuance with a
forged already-announced id rewrites the prefix despite an honest arbiter. These
are not failures of the delivery theorem: they name the honest-extension and
event-id-unforgeability premises required to cross those other axes.

**27b. Ordered frontier completeness → delivery-stable candidate values** ⚠
*source* `Frontier.WorldComplete F stamp w` · *target*
`Evidence.FreeTermination WorldFuture.DeliveryFuture` for the candidate-value
observation · *transport* `Frontier.world_complete_values_stable` · *needs*
`WorldFuture.Wf w`, the issued pool retained by the world, and the `hall`
premise settling every issued event at its stamped point · *without complete
delivery* `Frontier.advance_without_delivery_is_unsound` advances the concrete
nonempty `loneIssued` frontier from timestamp zero to one while delivering
nothing: completeness holds before and fails after. And without ordered
positions, `flat_frontier_loses_position` gives identical flat source bits with
opposite answers at timestamp zero; `flat_frontier_and_epoch_do_not_determine_world_future`
keeps frontier bits, certificates, roster and epoch equal while the issued pools
differ.

**27c. EUF-style trace premise → authentic issuer** ⚠
*source* `Authenticity.EUFStylePremise scheme keys revoked issued received` ·
*target* `Authenticity.AuthenticIssuer scheme keys revoked issued received` ·
*transport* `Authenticity.eufStyle_implies_authenticIssuer`, with the converse
and constructive failure handoff in
`authenticIssuer_iff_no_received_forgery` /
`authenticity_violation_extracts_forgery` · *needs* the exact registered key,
non-revocation, issuance transcript, and domain-separated `signingMessage`;
`grant_event_domain_separated`, `move_domain_separated`, and
`signingMessage_move_injective` make grant/event/move domains and every signed
move field explicit;
the theorem transports a trace-relative security premise and does **not** prove
cryptographic hardness · *without it* `Authenticity.attack_not_authentic` and
`attack_extracts_forgery` exhibit an accepted grant that issuer 7 never issued;
`toy_euf_style_refuted` proves the deliberately insecure scheme fails the
premise on that nonempty trace.

**27d. Fork evidence → attributable equivocation** ⚠
*source* `Causality.ForkEvidence B p` · *target*
`Byzantine.Equivocated issued p` · *transport*
`Byzantine.fork_evidence_attributes_author` · *needs*
`Byzantine.SignatureAuthentic B issued`, because a grow-only receive buffer
proves only that two shaped records arrived · *without it*
`Byzantine.forged_branch_can_frame_without_authentication` assembles concrete
fork evidence for peer 17 while `honest_issuance_did_not_equivocate` proves that
peer issued only the left branch. The orthogonal failure is inhabited too:
`authenticity_and_delivery_are_independent` pairs authentic-but-withheld data
with quiesced-but-forged data, so delivery cannot discharge this hypothesis.

**27e. Context-aware delivery/extension → projected world future** ⚠
*source* `WorldContext.DeliveryFuture origin versionOf c d` or
`WorldContext.ExtensionFuture origin versionOf c d` · *target* the matching
`WorldFuture` relation on `project c` and `project d` · *transport*
`WorldContext.delivery_projects` / `extension_projects`, with the evidence-level
projection `delivery_projects_evidence`; the exact converses are
`delivery_lifts` and `extension_lifts` · *needs*, for a converse lift, the
projected future plus `Frozen c d` or `Extends c d` and `Admits`: every newly
materialized candidate must have an outstanding active covering grant, an
origin in the downward-closed causal cut, and a version reachable from the
known base · *without that context*
`WorldContext.projected_delivery_does_not_lift_without_context` gives a real
projected delivery rejected by the capability-poor context. The stronger
separations `capability_changes_allowed_futures`,
`known_base_changes_allowed_futures`, and `known_cut_changes_allowed_futures`
hold the projected source and target worlds fixed while each hidden axis alone
flips the context-delivery verdict; `same_world_axes_hide_context` records the
equal state, pool, frontier, and epoch explicitly.

**27f. Authenticated settled ERA issuance → unchanged final view** ⚠
*source* `EraCertificate.Settled w`, `Byzantine.AnnouncementsGrounded w`,
`Byzantine.IdAuthentic t.pool`, and `EraCertificate.Issuance w t` · *target*
`EraCertificate.finalView t = EraCertificate.finalView w` · *transport*
`Byzantine.authentic_issuance_preserves_finality` · *needs* both authenticity
halves exactly where stated: every announced id is grounded in the old issued
pool, and one id denotes only one payload throughout the new pool. Settlement
then ensures every already-finalised issued event is present; issuance freezes
cuts while extending pool and log · *without `IdAuthentic`*
`Byzantine.forged_announced_id_breaks_era_finality` is a nonempty exact
refutation: both worlds are quiesced, the old world is settled and grounded,
and the transition is a valid issuance, yet a different payload born under
announced id 5 changes Alice from reader to admin and changes `finalView`.
`finality_failure_refutes_id_authenticity` packages the corresponding
contrapositive under settlement, grounding, and issuance.

**27g. Authentic signed-event trace → attributable fork observations** ⚠
*source* `Authenticity.AuthenticIssuer scheme keys keyRevocations issued
(AuthenticatedAdmission.receivedEvents events)` · *target*
`Byzantine.SignatureAuthentic (AuthenticatedAdmission.observations codec events)
(AuthenticatedAdmission.issuedEntries codec issued)` · *transport*
`AuthenticatedAdmission.authenticIssuer_to_signatureAuthentic` · *needs* each
`AcceptedEvent` to retain its exact event payload equality and acceptance under
the indexed key/revocation views, plus the explicit `EventTripleCodec` binding
signed events to the sequence/id coordinates · *without authentic admission*
`AuthenticatedAdmission.omitted_authenticity_permits_framing` preserves the
concrete fork evidence while refuting both attribution and
`SignatureAuthentic`. The positive path is nonempty:
`honest_equivocation_attributes_author` derives blame for the two accepted,
genuinely issued signed events rather than assuming it.

**27h. Accepted signed move → authenticated and capability-authorized operation** ⚠
*source* a received and accepted signed `Authenticity.MoveClaim`, together with
`Authenticity.AuthenticIssuer`, `AuthenticatedAdmission.GrantHolder`, and
`Gated.gatedOps` · *target*
`AuthenticatedAdmission.AuthenticatedGatedOp` · *transport*
`AuthenticatedGatedOp.ofAuthenticIssuer`, with projections `authentic` and
`authorized` · *needs* all three independent axes: genuine issuance derives
from issuer authenticity, holder binding says the signer may cite that grant,
and the ordinary gate checks the live capability chain · *without holder
binding* `mallory_fails_holder_even_when_gate_passes` has a valid signature and
an old-gate acceptance for Mallory's borrowed grant; *without live authority*
`valid_signature_over_revoked_grant_fails_authorization` gives Bob an accepted,
genuinely issued, holder-bound record whose revoked grant still fails the gate;
*without issuer authenticity* `forged_as_alice_breaks_authenticity` extracts
the accepted unissued forgery. This is the abstract admission conjunction, not
a FORMAT-v3/FFI signature lane.

---

## VII. Rendering

**28. Five-status contract → honest finality** ✗ **REFUTED**
*without it* `RenderSix.spinner_is_an_honest_five_status_renderer` — the
five-status contract is **satisfied** by a renderer that spins forever on a
definitively empty result. Both lies live in *finality*, the only thing the fold
erases.
⚠ *the repair* the six-status carrier, with `five_handlers_cannot_separate`
(every five-handler consumer at every display type agrees on the two
zero-candidate evidences) against `six_carrier_separates`.

**29. Escapability → epistemic truth** ✗ **REFUTED**
*without it* `RenderProgress.statusOf_pending_escapable_by_sealing` — the clause
is discharged **by giving up**: `sealAll` certifies every owed source, delivers
nothing, and satisfies it for every value type. A clause a spinner meets by
abandoning every peer is neither truth nor liveness.
⚠ *the repair* three contracts: `PendingSound` (no future quantifier at all),
`PendingProgress` (temporal, environmental premises), `PendingActionable`
(a discharge offer carrying an authorization proof).

**30. Closed emptiness → merge-safe badge** ⚠ **and it cuts both ways**
*transport* `RenderSix.absence_is_the_more_defensible_badge` — two definitive
absences merge to definitive absence, while two independently **exact** closed
evidences merge to a **closed fork** · *narrowed*
`RenderProgress.closed_emptiness_merges_arbitrary_determinacy_does_not`: some
exact badges **are** merge-safe (`anyCandidate_true_iconfluent` — and safe
**unilaterally**, one replica suffices) · *and*
`absence_is_not_unilaterally_merge_closed` — `absent` needs **both** replicas.
On the merge axis absence is not even the strongest badge.

**31. Scoped absence → global absence** ⚠
*transport* `RenderProgress.absentOn_covering_is_global` · *needs* the scope to
cover the obligations **and** the attributions · *without it*
`scoped_absence_does_not_reach_global` — two definitively-empty epochs compose,
and the global status is **`pending`** because a third source is owed and
neither scope names him.

**32. Semantic status → visual honesty** ⚠ **partial, and the limit is proved**
*transport* `RenderProgress.no_honest_widget_loads_at_absent`, and the one that
beats salience: `constant_widget_is_not_honest` — a **constant** widget
assignment is excluded outright · *what survives unenforceable*
`salience_is_still_not_enforceable_after_the_widget`: the last hop to pixels is
a function into an arbitrary type, and constant functions exist.

---

## VIII. Repairs and menus

**33. Repair chain → the original promise** ⚠
*transport* `Repair.comp_delivers` · *needs* the composed `PromiseRelation` to
be non-weakening · *without it* `weakened_chain_is_not_the_original` — the flag
is clear **and** the chain provably does not deliver.

**34. Scalar price → the design space** ✗ **REFUTED**
*without it* `Repair.crossings_cannot_see_the_difference` — read through the
crossing count alone, arbitration, fork and retain-evidence are **equal and
free**, while their `Price` records are pairwise distinct. And
`no_free_arbitration`, quantified over every repair by anyone: *"arbitration
costs nothing"* is not a report the type can print.

**35. Independent minima → composed optimum** ✗ **REFUTED**
*without it* `CoordEffect.pin_indep_min_unpayable` — positive at **every**
strategy, any segment type, any universe; `pin_session_costs_exactly_one` pins
achievement at 1 while independent minima sum to 0.
⚠ *the correct transport* `opt_compose_ge_sum_opt`, with
`opt_compose_eq_sum_opt_of_common_optimum` naming the hypothesis the scalar
grade was silently assuming — refuted on the same witness by
`pin_no_common_optimum`.
✅ *and the consolation* `forced_le_optimum_compose` — forced **floors** *are*
additive across composed streams even though optima are not.

**35a. Seam crossings → peer meetings** ✗ **REFUTED, both directions**
*without it* `Scheduling.no_crossing_count_determines_least_meetings` and
`no_least_meeting_count_determines_crossings` — two compatible crossing demands
coalesce (2 crossings → least 1 meeting), while an ambient barrier costs one
meeting at 0 crossings. `one_crossing_can_need_two_rounds` additionally refutes
the old unconditional “crossings upper-bound any coalescing schedule” wording:
one crossing may emit two incompatible round-tagged demands.
⚠ *the exact transport retained* `SessionProfile.crossingProfile_comp` forgets
the coeffects and recovers `CoordEffect.Profile.comp`; `composed_plan_uses_one_strategy`
keeps one admissible strategy after pointwise composition. A `Schedule` then
supplies the missing witness — participants, scope, epoch, evidence, round,
barrier, and separate currencies — and `least_le_upper` transports its proved
upper bound. No transport from `Budget.ForcedFloor` to a meeting floor exists.

**35b. One real plan → five-currency profile acceptance** ⚠
*source* `Scheduling.Plan s` plus the pointwise inequalities
`∀ currency, plan.profile currency ≤ limits currency` · *target*
`Scheduling.ProfileUpperBound s limits` · *transport*
`Plan.profileUpperBound`; `Plan.exactProfileUpperBound` supplies the exact
achieved profile, `ProfileUpperBound.comp` appends two witnessed plans and adds
every limit coordinate, and `ProfileUpperBound.toUpperBound` forgets everything
but the peer-barrier coordinate · *needs* **one and the same real plan** to
satisfy all five inequalities; five independently chosen witnesses are not a
profile acceptance · *without the other coordinates*
`least_meetings_do_not_decide_profile_acceptance` gives two sessions with the
same exact least peer count while a required network action makes only one fit
the peer-only profile. Stronger still,
`meeting_floor_does_not_entail_profile_acceptance` exhibits a proved peer floor
within allowance and refutes full acceptance.

**35c. Finite plan catalog → witnessed acceptance or catalog-relative refusal** ⚠
*source* caller-supplied `List (Scheduling.Plan s)` and five currency limits ·
*target* `ScheduleSynthesis.SearchResult s limits catalog` · *transport*
`ScheduleSynthesis.searchCatalog`; `SearchResult.bound_exists_of_isFound`
recovers a catalog member and its full `ProfileUpperBound`, while
`exhaustive_of_not_isFound` names a violating currency for every supplied plan
· *needs* the catalog itself—every candidate already carries schedule coverage,
but no theorem says the list enumerates all schedules · *without a crossing-only
shortcut* `same_crossings_opposite_catalog_verdicts` gives equal crossing counts
and opposite executable results at the same limits. The ranked variant
`selectLeast` additionally needs an explicit caller `OrderPolicy` and catalog
tie order; `selection_is_policy_dependent` makes two policies choose opposite
peer/network profiles from the same feasible catalog. Refusal and leastness
remain catalog-relative, and no catalog generator is claimed.

**36. Lower bound → acceptance** ✗ **REFUTED**
*without it* `Budget.lower_bound_does_not_license_acceptance` — and the reason
is deeper than the statement: **"the floor" is not a function.** There is a
family, one per carving, and a checker holds one member; a coarse carving fits
a budget that a finer one puts every plan over.

**37. Uniqueness ceiling → a seam exists** ✗ **REFUTED at every finite segment**
*without it* `MenuTotality.atMostOne_seam_row_refuted_at_every_finite_segment` —
"at most one element of `Nat`" has cliques of every size, so it admits **no**
seam into **any** finite segment type · *and*
`the_element_type_decides_the_seam_row`: the same ceiling over `Bool` **does**
take a two-fiber seam. Availability turns on the largest clique and nothing
else.
⚠ *and a bound the block calculus cannot see*: `clique_forces_joint_crossings`
gives `k−1` where `coordination_forced` gives `0`
(`the_clique_floor_is_invisible_to_the_block_calculus`).

**37b. A hand `Exits` row → a generated `RepairMenu` row** ⚠
*transport* `RepairMenu.transport` / `RepairMenu.transport_preserves_the_hand_number`
— the formal transport is exactly the projection `Price.seamCrossings`: given
any hand row, target promise, and typed repair whose crossing count equals the
hand row's `Nat`, the generated row displays the repair's full seven-currency
price and recovers that `Nat`.
*needs* only **`r.price.seamCrossings = e.exit.price`**. The theorem does **not**
relate the hand `Exit` tag or `Exit.Applies` witness to the repair's semantics.
*without the equality in the forced-seam lane*
`RepairMenu.the_ceiling_seam_hand_price_has_no_forced_backing` shows the hand
seam row's `0` differs from the clique-forced `SeamFloor.floor = 1`, so no row
priced from that forced floor can be its backing.
⚠ *and crossing equality is deliberately weaker than semantic backing*:
`RepairMenu.no_free_pin_arbitration` does **not** refute the transport premise
— `pinArbitrate` has zero seam crossings and therefore matches the hand
arbitration row's `0`. It instead proves that every such repair has a non-free
full `Price` and nonempty assumptions. Thus the scalar survives projection while
the hand row's implied “free” reading does not.
✅ *and the direction that now cannot fail*: `RepairMenu.menu_price_is_projection`
and `menu_delta_is_projection` — every price and delta a generated menu shows is
the `price`/`relation` field of a `Repair`, or of an obligation that agrees with
every repair it discharges to. There is no constructor through which an
independent `Nat` enters a menu, and the `Exit` display tag moves neither
(`tag_and_label_cannot_move_the_price`). `Exit.price` and
`MenuEntry.consequence` are retired as authorities and kept as vocabulary;
`consequence_is_free_data` is why the sentence field had to go.

**37c. Typed escrow repair → explicit reachability restriction** ⚠
*source* `RepairMenu.balanceEscrow`, a typed repair from the shared-balance
promise to the per-replica escrow promise · *target*
`Repair.RestrictsReachability balanceEscrow` together with its distinct price
currency · *transport* `RepairMenu.balanceEscrow_price_and_delta` · *needs* the
actual escrow invariant/transform and the source-to-target promise relation;
zero seam crossings are not evidence that admission was preserved · *without
the separate currency* `Repair.crossings_cannot_see_the_difference` makes
`restrictionPrice`, arbitration, forking and retained evidence all project to
crossing count zero. The nonempty semantic witness is `Exits.balX`:
`Exits.balX_legal` admits one device spending the whole budget in the source,
while `RepairMenu.escrow_forbids_balX` proves the split target rejects it.

**37d. Explicit repair catalog → least applicable repair or exhaustive catalog refusal** ⚠
*source* a `RepairSynthesis.Catalog P` whose entries retain stable IDs,
decidable residual applicability, typed repair constructors, and complete
`Repair.Price` records, plus a caller `Catalog.Valuation : Price → Nat` ·
*target* `RepairSynthesis.Catalog.Result catalog valuation` · *transport*
`Catalog.synthesize`; the found branch exposes the actual repair through
`Catalog.Found.repair`, preserves its full price by `Found.repair_price`, and
proves caller-valued leastness by `Catalog.minimum_le_of_applicable`; the
refusal branch is exhaustive by `minimum_none_exhaustive` and
`Result.exhaustive_of_isFound_false` · *needs* an explicit `Decidable` for each
residual (the bridge from `RepairMenu.RepairObligation` is
`Candidate.ofObligation`) and an explicit catalog/valuation—neither is library
policy · *without catalog completeness* `Examples.refusedCatalog` refuses both
of its supplied rows (`refusal_is_exhaustive_for_catalog`) while applicable
repairs such as `Examples.fullTwo` exist outside that list. Thus refusal is not
"no repair exists", and this search neither enumerates seam projections nor
synthesizes an escrow partition.

---

## IX. Structure and documents

**38. Two well-formed documents → a well-formed document** ✅
*transport* `Wellformed.merge_preserves_wellformed` — **unconditional**: no
agreement premise, no application invariant, no reachability · *the design call
that made it true* `UniqueAnchor` is **excluded** from well-formedness, because
including it makes the theorem false. Consequence, stated as ⟨TERMINAL⟩: a
merged document may show one id twice and still be a document.

**39. Well-formed → renderable** ✅
*transport* `Wellformed.no_crash` — quantified over **every** reader total on
well-formed documents, with a witness whose `none` branch is provably
unreachable.

**40. Acyclicity under arbitrary edges** ✗ **REFUTED**
⚠ *the repair* `Acyclicity.grounded_iconfluent` — rank-groundedness *is*
I-confluent and implies acyclicity, and content-addressing supplies the rank for
free.

**40a. Result evidence ↔ evidence document** ✅
*transport* `DerivedDocument.encodeEvidence_iso`: `encodeEvidence` and
`decodeEvidence` are join homomorphisms and mutual inverses, so the source and
target are the same mergeable state at different indices · *needs* no external
hypothesis for these carriers; the encoding has one constructor for each of the
three grow-only evidence components · *without that full encoding*
`value_only_encoding_is_not_faithful` gives equal candidate values for distinct
open/exact evidences that render `provisional 47` and `exact 47`. This refutes
fidelity of the coarser encoding, not its merge preservation.

**40b. Set-image derivation → mergeable derived document** ⚠
*transport* `DerivedDocument.deriveDoc_hom` / `deriveDoc_ships` · *needs* the
actual construction `encodeEvidence ∘ evidenceOf`; `evidenceOf_joinHom` is
unconditional in the deterministic `f` when obligations and certificates are
fixed, and `encodeEvidence` is the homomorphism from row 40a · *without that
construction* merely returning a document proves nothing:
`tallyDoc_not_joinHom` and `tallyDoc_requires_evidence` show a document-valued
count that no result combiner can merge.

**40c. Count result → result-mergeable document** ✗ **REFUTED**
*would-be transport* encoding the scalar count as an `EvidenceDoc` makes it
mergeable from document results · *needs* provenance distinguishing which
elements contributed · *without it* `DerivedDocument.tallyDoc_requires_evidence`
ranges over every binary combiner on documents: `tallyDoc sawA` and
`tallyDoc sawB` are identical inputs, while the same-element and
different-element merges require different output documents.

**40d. Count-derived document → sufficient summary** ✗ **REFUTED**
*would-be transport* document shape makes a count-derived result sufficient ·
*needs* retained evidence; formally, `deriveDoc_not_hom D` assumes
`D = k ∘ JoinHom.card` and proves such a factorization is **insufficient** ·
*without provenance* `tallyDoc_not_sufficient` is the concrete instance. This
is a sufficiency refutation, distinct from row 40b's mergeability refutation.

**40e. Mergeable count document → retained provenance** ⚠
*transport* `DerivedDocument.mergeable_count_document_must_retain_the_evidence`
· *needs* both `JoinHom g` **and** a factorization
`JoinHom.card = k ∘ g` · *without the hom premise*, the count-only
`tallyDoc` still factors the count but has
`tallyDoc sawA = tallyDoc sawB` and is not mergeable; *without factorization*, a
constant join homomorphism need not distinguish those replicas because no count
can be decoded from it. The positive target is inhabited by
`seenDoc_retains_the_evidence`:
`seenDoc` is a homomorphism, the count factors through it, and it separates the
two one-element replicas.

**40f. Shared-rank pipeline → merged pipeline terminates uniquely** ⚠
*transport* `DerivedDocument.pipelines_merge_coordination_free` · *needs*
`[Inhabited D]`, a full `P : Stratified D`, and the arriving dependency graph
grounded under **the same `P.rank`** · *without the shared grounded discipline*
`Acyclicity.acyclicity_not_iconfluent` shows acyclic graphs can merge cyclic,
while `acyclic_pipelines_are_not_all_grounded` gives an acyclic infinite chain
with no `Nat` rank, so “acyclic” cannot silently replace “stratified”.

**40g. Sound evidence evaluator → sound derived-document evaluator** ✅
*transport* the general `DerivedDocument.sound6_transport`; the specialization
is `docStatus_sound6` · *needs* maps `φ` and `ψ` with the right-inverse law
`∀ t, φ (ψ t) = t`; at this carrier `decode_encode` discharges it
unconditionally · *without it* — n/a for the specialized isomorphism, and the
source proves no general no-section counterexample, so none is asserted here.
The worked `one_renderer_serves_both` is a consequence of the isomorphism, not
of document shape alone.

**40h. Canonical crash-prefix bytes → exact recovered journal** ⚠
*source* `Durable.encodeJournal tag records ++ torn` · *target* the logical
record list `records` · *transport* `Durable.recover_crashPrefix`, with prefix
monotonicity in `recover_crashPrefix_monotone` · *needs* the complete prefix to
be the canonical `encodeJournal` image and the suffix to carry an explicit
`Durable.TornFrame tag next torn` witness. Real storage must separately supply
`DeploymentAssumptions`; this module manufactures none · *without the torn
suffix premise* `Durable.recover_append` is the concrete opposite case: a
complete nonempty next frame recovers `records ++ [payload]`, not `records`.
At the codec boundary, `decodeFor_encodeFrame_ne` also refuses every complete
frame under a distinct version/domain tag, so the format identity is
load-bearing rather than display metadata.

**40i. Result evidence → typed evidence graph → flat evidence document** ⚠
*source* `Evidence.ResultEvidence α` · *target* first
`EvidenceGraph.Graph α`, then `DerivedDocument.EvidenceDoc α` · *transport*
`EvidenceGraph.encodeEvidenceGraph_merge` / `encodeEvidenceGraph_joinHom` and
the exact factorization `EvidenceGraph.flat_encodeEvidence_is_projection`;
the forgetful map itself is certified by `forgetEvidenceGraph_joinHom` ·
*needs* graph endpoint integrity, discharged for every encoded value by
`encodeEvidenceGraph_wellFormed`; candidate-source support is the explicit
noncomputable projection over arbitrary `α` · *without wellformedness*
`EvidenceGraph.danglingAttribution_is_malformed` gives a present attribution
edge with no candidate endpoint. The positive structure is nonempty:
`forked_evidence_has_two_sourced_branches` and
`forked_evidence_has_explicit_discharges` exhibit distinct candidate branches,
source vertices, and certificate-to-obligation edges.

**40j. Globally non-glueable one-shot guard → exact owner-fiber gluing** ⚠
*source* `Gluing.AtMostOneFill` on the total `oneShotHole` · *target*
`Gluing.GluesWithin oneShotHole oneShotOwner` paired with the global rejection
`¬ Gluing.Glues oneShotHole` · *transport*
`Gluing.oneShotHole_partially_glues`, whose positive certificate is
`oneShotOwner_segmented` through `guardGluingSeam_iff_segmented` · *needs*
same `oneShotOwner` fiber and two locally legal one-shot states; the owner is
proof-level (`Classical.choose`) because a general `Nat → Bool` has no finite
emptiness search · *without the seam* `Gluing.oneShotHole_never_glues` is the
concrete global clash. Moreover `oneShot_seam_separates_singletons` and its
`GluesWithin` corollary prove every valid seam must separate each distinct pair
of singleton fills, so the coordination boundary cannot be collapsed.

---

## X. Verification conditions

**41. RA-linearizability → application safety** ✗ **REFUTED**
*without it* `RALin.ra_linearizable_but_unsafe` — a merge correct against its
own sequential specification, on branches legal at every prefix, that overdraws.
Converse also refuted: `maxctr_every_invariant_iconfluent` — a counter that
**loses updates** makes every invariant safe. All four quadrants inhabited.
⚠ *what RA-lin does buy* `ra_lin_preserves_inductive_invariants` (axiom-free) ·
*and the entanglement* `guarding_moves_the_bug`: guard an operation and the same
merge (`rfl`-unchanged) stops being RA-linearizable.

**42. Abstract gate → shipping kernel gate** ✅
*transport* `Gated.kernel_gate_agrees_gatedOps` (iff under `WF` + `UniqueGrant`)
and `kernel_admits_only_authorised` (**hypothesis-free** safety direction) ·
*without the premises* first-match search can only admit **less**, which is why
safety needs nothing.

**42a. Typed request lanes → canonical FORMAT v3 bytes** ⚠
*source* four Lean-owned `Array UInt64` lanes for base parents, five-word move
records, three-word grants, and revocations · *target* the single canonical
`ByteArray` produced by `Exec.encodeRequest` · *transport*
`Exec.encodeRequestKernel_eq`: the exported entry point reconstructs typed
`Op`/`Grant` values and definitionally delegates all magic, counts, block
order, signed-word interpretation, and little-endian encoding to Lean · *needs*
the residual typed ABI/shim contract: owned arrays must cross Rust/C/Lean with
their words intact, and the shim must supply exact-width op quintuples and
grant triples. This theorem removes a second wire encoder; it does not verify
the C generator, runtime, shim, FFI, or host construction of those lanes ·
*without that typed entrance* malformed bytes remain only a refusal boundary,
not a typed semantic source. Concretely, the executable
`Exec.requestCanonicalKernel` returns the one-byte refusal code `0` for a
wrong-magic request (including `ByteArray.empty`), while `Exec.replay` returns
an empty response; and the total `opsOfTypedWords` / `grantsOfTypedWords`
definitions ignore a trailing partial record, making the shim's exact-width
promise load-bearing. No theorem here upgrades arbitrary bytes into a typed
request.

**43. Growing revocations → shrinking applied set** ✗ **REFUTED**
*without it* `Exec.applied_set_not_antitone` — revoking a grant can **add** an
applied move, because the cycle rule is not monotone in the log. Antitonicity is
about the **feed**.
✅ *what does hold* `Exec.gated_unauthorised_is_forever`.

**44. Antitone permission rule → a usable system** ✗ **REFUTED**
*without it* `GatedEra.antitone_forbids_enabling` — **any** rule antitone in
event growth makes promotion impossible. Fail-closed guarantees shrinkage and
pays with both duellists; arbitration guarantees agreement and pays the sign
table.

---

## XI. Preoscript: evidence entering the language

**44a. Field-scale confluence → declared-state confluence** ⚠
*transport* `Preo.proj_iconfluent`, emitted as `<invariant>.onState` after the
field verdict reduces to FREE · *needs* the field projection `π` to preserve
join · *without it* monotonicity is insufficient:
`JoinHom.monotone_pullback_can_fail` is the existing counterexample from row 20.
A field-scale CLASH is intentionally not transported by this theorem; that
needs the section in row 44b.

**44b. Field-scale seam verdict → declared-state seam verdict** ⚠
*transport* `Preo.seamAlong`, emitted as `<invariant>.seamOnState` · *needs* a
join-homomorphic projection **and a section** `ι` satisfying
`π (ι a) = a` and `π (ι a ⊔ ι b) = a ⊔ b`; the section plants the
field verdict's concrete clash in a legal document · *without it* a constant
projection onto one legal field state can have a coordination-free pullback
even when the field invariant clashes outside its image, so no document-scale
`SegVerdict` can carry that clash. Fragment 1's recorded refusal was exactly
the absence of this plant; fragment 2 emits it with legal defaults.

**44c. Field `fromResults` verdict → declared-state `fromResults` verdict** ⚠
*transport* `Preo.mergeability_comp` · *needs in its present signature* both a
join-homomorphic `π` and a surjectivity witness; its `.fromResults` proof branch
uses only preservation of join, but no split public theorem currently removes
the unused surjectivity argument · *without join preservation* cardinality is
the concrete failure: `JoinHom.monotone_not_joinHom` and
`no_count_merge_without_provenance` show a monotone field projection whose
results cannot be merged. The surface therefore emits an actual field
projection, not an arbitrary read.

**44d. Field `needsEvidence` verdict → declared-state `needsEvidence` verdict** ⚠
*transport* `Preo.not_incrementallyMergeable_comp`, packaged by
`mergeability_comp` · *needs* `π` to preserve join **and be surjective**; the
generated `<field>.surj` is a document with that field value and legal defaults
elsewhere · *without surjectivity* the conclusion is false: take a constant
projection into a proper sub-image on which `g` is constant. Then `g` may fail
to be incrementally mergeable on its whole carrier while `g ∘ π` is merged by
the constant combiner.

**44e. Registry route order → certified semantic answer** ⚠
*transport* `Preo.run_answer_congr` (and permutation corollary
`run_answer_of_perm`) · *needs* membership-equivalent registries;
`answerOf_congr` states the weaker exact condition that the same global/seam
facet kinds were reached · *without that condition* an empty registry answers
`none`, while adding a seam rule answers `some false`
(`run_answer_of_seam`). Explanation order is **not** transported: the facet
lists remain ordered report-policy data. Merge-answer uniqueness is the
separate theorem `run_mergeAnswer_unique` and needs no registry equality once
both answers exist.

**44f. Two field seam verdicts → one document seam verdict** ⚠
*transport* the elaborator's emitted `N.documentSeam`, built with
`seamAlong` through arbitrary right-nested paths, `andSeams`, and a checked
`absorbFree` fold. `TwinQuota.documentSeam` is the existing `prodSeams` value;
`NestedSurface.documentSeam = documentSeamFree6` proves all six FREE rows were
absorbed, both by `rfl`. At the general algebra layer, `SegVerdict.selfSeam`
for pins plus `prependFree` reconstructs
`Preo.Demo.weaveDocViaAlgebra = WeaveState.weaveDocSeamVerdict` by `rfl`
· *needs* exactly two certified seam rows on distinct fields and each absorbed
FREE row to hold at both carried clash documents · *without the second seam*
there is no pair of fibers; without a checked legal side condition the FREE row
is omitted. The former grouped-carrier obstruction is discharged narrowly:
`Preo.Demo.groupedCarrierSurface_state_is_weaveDoc` identifies the generated
state with `WeaveState.WeaveDoc`, while
`groupedCarrierSurface_core_seed_is_core₀` identifies its explicitly supplied
legal core seed. `groupedCarrierSurface_core_plant_proj` checks the generated
carrier projection. The elaborator still does not infer a merge or seed: the
custom field supplies both via an existing `MergeState` and an explicit term;
the built-in quota seed is zero and cannot replace the legal `quota₀` at
budget ten.

**44g. Joint cross verdict → keyed cross verdict** ⚠
*transport* `Confluence.keyed_cross_iconfluent`, emitted by the keyed-cross-FK
route for `field bookmarks per K : GrowSet Nat`; the acceptance check is
`Preo.Demo.KeyedDoc.fk.verdict = WeaveState.bookmarksVerdict` by `rfl`
· *needs* a real `IConfluent` proof against the joint `A × B` merge and applies
it pointwise to the shared `A × (K → B)` carrier · *without that joint proof*
no per-field lift is valid: `Catalog.lww_cross_field_not_iconfluent` refutes the
generic componentwise shortcut, and an unsupported keyed predicate remains an
`Obligation`. Automatic keyed clash seams additionally need a concrete key and
legal default family; the surface does not invent them.

**44h. Protocol AST → checked scheduling plan under one strategy** ⚠
*source* `Protocol.Term Strategy` plus one selected admissible strategy ·
*target* `Scheduling.SessionProfile`, `Schedule`, `Plan`, and witnessed
peer-only `UpperBound` plus five-currency `ProfileUpperBound` data · *transport* `Protocol.elaborate`,
`elaborateProfilePlan`, and the audit theorem
`elaborated_composition_uses_one_strategy`; `Elaboration.exactProfileUpperBound`
retains the exact achieved profile and `elaborate_exactProfileUpperBound_plan`
pins it to the elaboration's one checked plan. The standalone `preo_budget`
surface accepts only such a `ProfileUpperBound`:
`Preo.Demo.coalescedProfileBudget_is_hand_witness` identifies the generated
value with the existing five-currency witness and
`coalescedProfileBudget_retains_five_currencies` observes every coordinate.
`Annotation.axes_retained` proves all seven demand axes survive elaboration ·
*needs* a single global `strategy`
and its membership proof in `CoordEffect.Admissible`; parallel or sequential
subterms do not choose independent optima · *without the full scheduling
artifact* `Protocol.no_ast_crossing_count_determines_least_meetings` gives two
inhabited ASTs with equal crossing counts and distinct exact meeting counts,
while `ast_one_crossing_can_need_two_rounds` shows one crossing can require two
incompatible rounds. At the surface boundary,
`Preo.Demo.no_crossing_count_accepts_profile_budget` and
`meeting_floor_does_not_accept_profile_budget` reject the corresponding scalar
acceptance shortcuts. Thus elaboration transports annotations and proofs, not
a scalar conversion.

**44i. Broad future certificate → contained-future certificate** ⚠
*source* `CertificateScope.KeyCertSound key answer broad.future C` · *target*
soundness for `narrow.future` · *transport*
`Preo.Future.certificate_sound_restrict`, with artifact-level forms
`CheckedStability.restrict` and `CheckedCertificate.restrict` · *needs*
`Preo.Future.FutureDecl.IncludedIn narrow broad`; the concrete declaration is
`delivery_le_extension`, so soundness is contravariant from extension to
delivery · *without inclusion in that direction*
`Preo.Future.quiescedRenderStability` exists but
`delivery_artifact_does_not_promote_to_extension`, and
`quiescedWorldCertificate` is sound for delivery while
`quiescence_certificate_not_sound_for_extension`. Separately,
`same_state_different_worlds_block_certificate_reuse` is the nonempty
world-indexing counterexample: equal materialized state does not license a
state-only checked certificate because the issued pools differ.

**44j. Checked semantic declaration → canonical first-order artifact** ⚠
*source* private checked terms such as `Preo.Artifact.CheckedInvariant I` and
`CheckedPlan checkedSession plan` · *target* the public first-order
`Preo.Artifact.ArtifactEncoding` with a structural roundtrip · *transport*
the `Checked*.toArtifact` projections and
`Preo.Artifact.ArtifactEncoding.decode_canonicalEncoding` · *needs* the checked
constructors to originate semantic meaning: an invariant source carries an
actual `Spec.Verdict` and witness codec, and a plan source carries an actual
`Scheduling.Plan`. The wire roundtrip itself needs no semantic hypothesis and
is deliberately **not** a verifier · *without the checked source* the reverse
transport is false by construction: public `ArtifactEncoding.decode` returns
only an `Artifact`, never a `Spec.Verdict` or `Scheduling.Plan`. The concrete
nonempty boundary is `Preo.Artifact.Examples.bundle`; it contains every list, a
real plan, and both verdict tags, while `Examples.atMostOneBoolVerdict` is the
actual two-witness clash that an arbitrarily authored wire `.free` tag cannot
replace.

**44k. Proof-indexed declaration bundle → one artifact and canonical wire image** ⚠
*source* `Preo.Export.DeclarationBundle State`, populated only through its
checked field, verdict, future-certificate, and protocol-elaboration builders ·
*target* one `Preo.Artifact.Artifact` paired with its canonical
`ArtifactEncoding` in `DeclarationBundle.Projection` · *transport*
`DeclarationBundle.project`, with exact roundtrip
`DeclarationBundle.Projection.decode_encoding`; the nonempty whole-language
instance is pinned by `Examples.whole_artifact_is_hand_composition`,
`whole_encoding_is_hand_composition`, and `whole_export_roundtrips` · *needs*
the private proof-indexed bundle/projection constructors and the checked inputs
at each builder call: actual verdict, exact-world future certificate, and one
protocol elaboration whose plan remains indexed by its session. Stable IDs and
the witness codec remain explicit; only after these types constrain the build
are proofs erased · *without that checked source* an arbitrary wire verdict is
only first-order data: `Preo.Export.arbitrary_free_tag_decodes_only_as_data`
roundtrips the concrete host-authored `arbitraryFreeWire` tagged `.free`, while
`decoded_verdicts_are_only_wire_data` exposes a codomain with no invariant
index. It therefore cannot reverse the projection into a `Spec.Verdict`.
`Examples.every_export_surface_is_nonempty` and
`protocol_export_is_nontrivial` ensure the positive artifact contains all five
row classes and a real two-action protocol plan.

**44l. Finite choreography → guarded recursive embedding and sound approximants** ⚠
*source* a finite `Choreo R S`, or an accepted `ChoreoRec.RecChoreo R S` at a
chosen fuel · *target* an ordinary finite choreography together with its global
denotation and endpoint projection · *transport* `ChoreoRec.approximate_embed`
is exact at every fuel, `embed_wellGuarded` admits every finite source, and
`denoteApprox_embed` / `projectApprox_embed` preserve its meanings;
`projection_sound_approx` then reuses the finite projection theorem · *needs*
`[DecidableEq R]` for the semantic layer and exactly
`Choreo.ReadsAgree roster (approximate fuel term) initial` for projection
soundness. `WellGuarded` is the recursive-language admission boundary, not an
extra premise smuggled into `projection_sound_approx`; bounded approximation
does not manufacture branch agreement · *without guardedness*
`ChoreoRec.unguardedLoop_is_rejected` rejects the concrete immediate
self-reference `.mu .var`. And guarded syntax alone is no liveness theorem:
`mismatched_barrier_is_deadlocked` gives a nonempty two-replica runtime where
one endpoint waits and the other has terminated;
`unguarded_and_deadlocked_refutations` packages both failures, while
`guardedBarrierLoop_progresses` is only the positive one-step, fuel-one case.

**44m. Answered classification → checked verdict artifact** ⚠
*source* `classification : Preo.Classification I f` plus the licence
`classification.answer = some answer` · *target* first a `Spec.Verdict I`, then
an invariant row in `Preo.Export.DeclarationBundle` · *transport*
`Preo.Classification.checkedVerdict`, whose
`checkedVerdict_isFree` pins the verdict to the licensed Boolean, followed by
`DeclarationBundle.addClassification` · *needs* the answer equality and the
same explicit first-order witness codec required by direct verdict export;
report strings, route labels, and seam readings are not consulted · *without a
licence* `no_checkedVerdict_licence_of_answer_none` blocks every unresolved
classification and `Preo.Export.unresolved_classification_has_no_export_licence`
instantiates the boundary. The two positive branches are exact:
`addClassification_free_agrees_with_addVerdict` and
`addClassification_seam_agrees_with_addVerdict` reduce classification export
to direct checked-verdict export.

**44n. Neutral artifact encoding → canonical durable frame** ⚠
*source* `Preo.Artifact.ArtifactEncoding` · *target* canonical `List UInt8`
inside the version/domain-separated `Durable` frame · *transport*
`Preo.ArtifactDurable.decodeProjection_projectionBytes_append`, preserving
arbitrary following journal bytes; `decodeProjection_projectionBytes` is the
exact one-frame form · *needs* the compositional `WireCodec` roundtrip, exact
consumption and re-encoding in `canonicalCodecOfWire`, and the exact
`artifactFormat` — explicitly **format v2**, whose product adds witnessed
five-currency budgets and therefore refuses superseded v1 bytes · *without exact acceptance* the raw prefix parser retains
surplus bytes (`parseArtifact_encode_append`) while
`Examples.overlong_artifact_refused` rejects the same surplus as one artifact;
*without the exact tag* `wrong_version_refused` and `wrong_domain_refused`
fail closed. `Examples.two_frames_then_torn_third` adds logical journal recovery
under an explicit `Durable.TornFrame`; it is not a filesystem or flush
refinement, and decoded bytes remain first-order data rather than proof.

**44o. Untrusted projection → bounded validated projection** ⚠
*source* `Preo.ProjectionV1.Projection` plus a caller
`ValidationConfig` · *target* the privately constructible
`Preo.ProjectionV1.ValidatedProjectionV1` · *transport*
`Preo.ProjectionV1.validate` · *needs* the exact V1 schema, explicit limits for
every variable-length collection, unique stable IDs, matching declaration and
plan/session references, in-range crossing origins, and the exact ordered
five-currency plan-profile shape — **plus an empty budget list**. V1 is the
exact legacy schema, not a compatibility alias for budget-bearing artifacts;
nonempty budgets return `budgetsNotSupported actual` · *without each check* the named executable
refusals include `duplicate_field_refused`,
`wrong_field_declaration_refused`, `dangling_plan_session_refused`,
`out_of_range_crossing_refused`, `noncanonical_profile_refused`, the resource
bound refusals, `nonempty_budgets_refused`, and `wrong_schema_refused`.
Positive acceptances `artifact_example_validates` and
`export_example_validates` are deliberately budget-empty. Validation
transports structural well-shapedness only: its public encoding still contains
no `Spec.Verdict`, authorization, admission token, or permit.

**44p. Validated projection → deterministic data-only Rust source** ⚠
*source* the privately constructible
`Preo.ProjectionV1.ValidatedProjectionV1` · *target* a Rust source `String`
containing only first-order projection data · *transport*
`Preo.ProjectionV1.renderRustSource`; the raw-input convenience boundary
`validateAndRender` first performs row 44o's validation. Output is a pure
function of the validated encoding by `renderRustSource_eq_of_encoding_eq`,
and `validateAndRender_error` preserves every validation refusal · *needs* the
private validated type, deterministic list order, Rust string escaping, and
arbitrary-precision decimal rendering of Lean naturals;
`Examples.unbounded_decimal_fixture` checks a value beyond machine-word range
and `Examples.empty_projection_rust_fixture` pins one complete source file ·
*without validation* no renderer theorem accepts an arbitrary projection.
This is a data renderer only: there is no theorem that the emitted Rust
compiles, reconstructs semantic proofs, or issues authorization or a permit,
and caller-local validation limits are intentionally not serialized.

**44q. Budget-bearing neutral projection → privately validated V2 projection** ⚠
*source* `Preo.ProjectionV2.Projection` plus a caller-supplied
`ValidationConfig` · *target* the private
`Preo.ProjectionV2.ValidatedProjectionV2` · *transport*
`Preo.ProjectionV2.validate` · *needs* all V1 declaration/reference/resource
checks on the budget-cleared base, then exact action histograms, coverage of
every session obligation by the referenced plan, unique budget IDs, existing
session and plan references, plan/session agreement, canonical five-currency
limits and realized profiles, equality with the plan profile, and pointwise
realized ≤ promised limits. `Examples.full_export_validates` accepts the
nonempty proof-originated export · *without those hypotheses* the concrete
refusals include `action_profile_lie_refused`,
`uncovered_obligation_refused`, `duplicate_budget_refused`, the dangling and
mismatched budget-reference fixtures, `noncanonical_budget_limits_refused`,
`mismatched_budget_profile_refused`, and `exceeded_budget_limit_refused`.
V2 validation still transports only bounded first-order consistency; it does
not reconstruct the checked plan, budget proof, verdict, permit, or authority.

**44r. Explicit `preo_export` manifest → one checked durable, validated host value** ⚠
*source* a `preo_export` declaration whose rows name already elaborated fields,
answered classifications, exact-world certificates, protocol elaborations,
and exact-plan `preo_budget` witnesses · *target* the generated
`Bundle`, `Artifact`, canonical `Encoding`, format-v2 `ArtifactDurableBytes`,
V2 `Validated`, and data-only `Rendered` constants · *transport* the
`elabPreoExport` builder fold invokes `DeclarationBundle.addField`,
`addClassification`, `addCertifiedFuture`, `addElaboration`, or
`addElaborationWithBudget` at each row, then requires the generated
`validation_ok` theorem before extracting the private validated value · *needs*
literal stable/type/kind/relation IDs, an explicit witness codec, the
classification answer equality, the certificate's full dependent type, an
actual generated `Protocol.Elaboration`, the budget's exact plan equality, and
an explicit V2 host config. The whole positive value is
`Preo.Demo.SemanticExport`: `semanticExport_bundle_is_hand_builder`,
`semanticExport_exact_manifest_rows`, `semanticExport_durable_roundtrip`, and
`semanticExport_validated_and_rendered` pin construction, bytes, validation,
and rendering · *without a row licence* unresolved classifications are blocked
by `Preo.Export.unresolved_classification_has_no_export_licence`, wrong
certificate/plan terms fail elaboration, composed profile plans are explicitly
refused because no checked single-session builder exists, and duplicate IDs,
bad references, dishonest profiles, or exceeded limits make row 44q's whole
`validation_ok` obligation false. No report text or source-name hash enters the
manifest value.

**44s. Conservative typed environment delta → correct differential result** ⚠
*source* a proof-carrying `Preo.Incremental.EnvDelta`, a cache tied to its base
environment, and a typed `Preo.Expr.Term` · *target* a `Result` equal to fresh
evaluation at the new environment · *transport*
`Preo.Incremental.incremental_correct`; `off_dependency_zero` additionally
transports a false structural touch test to exact cached reuse with zero counted
root evaluations · *needs* `EnvDelta.unchanged`, which proves every field
reported unchanged really is equal, and the cache's own correctness proof ·
*without an explicit extension law* `custom_without_law_recomputes` forces
every opaque `CustomNode` down the one-full-evaluation path regardless of its
declared reads. `withLaw_correct` permits a cheaper custom path only when the
author returns a result carrying equality to `Term.eval`; no subterm work,
allocation, or reduction-cost bound is transported.

**44t. Observer-selected Boolean → sound remote choreography branch** ⚠
*source* a finite `ChoreoChoice.Program` built from read-free ordinary
`Choreo` blocks · *target* equality between global denotation and every
endpoint's accepted local run · *transport* `ChoreoChoice.projection_sound` ·
*needs* the observer's selected label in the generated `Delivery` and each
block's stored `Choreo.ReadFree` proof; remotes consume the communicated label
rather than reevaluating the predicate on stale state · *without label
delivery* `twoParty_remote_missing_label` returns `none`, and
`twoParty_observer_rejects_wrong_label` rejects a label inconsistent with the
observer's value. `fixture_observations_disagree` proves the repair is not
silent local-read agreement. No authenticity, fairness, recursion, or eventual
delivery follows.

**44u. Explicit finite simple graph → exact singleton clash graph and width floor** ⚠
*source* `ClashGraph.FiniteSimpleGraph V` with a complete duplicate-free vertex
list, symmetry, and irreflexivity · *target* the clash relation of its
independent-set invariant on singleton grow-only states · *transport*
`ClashGraph.FiniteSimpleGraph.singleton_clashes_iff` is an iff, so it preserves
edges and non-edges exactly · *needs* the supplied finite coverage and simple
graph laws. The instantiated `c5_cycle_edges` and `c5_has_no_chords` form an
induced five-cycle, while `c5_singletons_have_no_triangle` rules out a hidden
three-clique; nevertheless `c5_forces_three_domains` proves every global seam
needs at least three domains. Separately,
`LeaveOneOutObstruction.forces_domains` needs a finite list of legal leaves,
pairwise joins to one illegal full state, and transports only that supplied
list's length — it does not discover an obstruction or enumerate an arbitrary
carrier.

**44v. Admitted finite operation patches → ancestral-confluence legality** ⚠
*source* a guarded operation system, ancestral merge, and arbitrary explicit
finite patches · *target* preservation of the invariant by every ancestral
merge of admitted branch results · *transport*
`CompositeDelta.legalUnderComposition_iff_ancestralConfluent` · *needs*
`LegalUnderComposition`, the run-level law quantifying over both admitted
patches. A stronger `CompositeDelta.Algebra` additionally supplies residual
patches with diamond, merge-identification, and legality proofs, from which
`Algebra.ancestralConfluent` follows · *without the composite law* the existing
length-two counter satisfies the older stepwise premise but
`counter_not_legalUnderComposition` and
`counter_has_no_composite_algebra` reject the transport. The positive
`cheapLockAlgebra_ancestralConfluent` uses a real one-instruction recovery;
no patch is reconstructed from state endpoints.

**44w. Finite query/context family → executable contextual quotient** ⚠
*source* a `ContextCompiler.Spec` containing explicit state, merge-context, and
homogeneous-query lists · *target* an executable signature class with a
choice-free representative · *transport* `ContextCompiler.signature_eq_iff`
makes signature equality exactly the specified multi-query contextual relation,
`encode_decode_exact` returns a representative equivalent under that relation,
and `sufficient_refines_signature` proves every sufficient caller key refines
the compiler key · *needs* only the supplied finite lists for the restricted
result, but a coverage proof is required by
`signature_eq_iff_all_ctxEquiv_of_complete` before identifying it with
carrier-wide contextual equivalence · *without complete contexts*
`restricted_contexts_can_coarsen` merges two states the global quotient
distinguishes. No globally canonical or bit-optimal encoding follows.

**44x. Finite six-status reach → least honest status effect** ⚠
*source* a finite reachable-state list and a status evaluator · *target* the
least downward-closed `StatusEffects.Effect` supporting every observed shape ·
*transport* `StatusEffects.infer_is_least`; `fromLegacy_matches` separately
embeds the historical three-flag capability exactly on every status · *needs*
the explicit finite reach, because inference claims nothing outside it. For
semantic soundness, `statusOf_totalSound6` inhabits
`TotalSoundEvaluator6`, whose clauses cover all six cells · *without the total
contract* `closedForkAsOpen_old_sound` accepts a concrete evaluator that calls
a settled fork open, while `closedForkAsOpen_not_total` rejects it. And without
an explicit resolution constructor, `explicit_resolution_is_load_bearing`
shows preserve-fork and select-one descriptors differ; no hidden Boolean
resolution policy is transported.

**44y. Continuous enabledness plus weak fairness → eventual action occurrence** ⚠
*source* an infinite action-labelled trace satisfying `Temporal.WeakFair` and
an action continuously enabled from some index · *target* eventual occurrence
of that action · *transport*
`Temporal.continuously_enabled_eventually_occurs`, with
`StrongFair.weakFair` deriving the scheduler premise from strong fairness ·
*needs* fairness as an explicit trace predicate; adjacency through a valid step
relation supplies safety, not progress · *without fairness*
`WorldAdapter.starvedPendingTrace_adjacent` proves the constant pending trace
uses only valid reflexive deliveries, while
`starvedPendingTrace_not_weakFair` refutes weak fairness for the genuine pending
delivery. The concrete positive adapter `fair_bob_delivery_exits_pending`
reaches a non-pending render after Bob's admitted delivery; no wall-clock bound
or automatic fairness of every execution follows.

**44z. Checked local edit or command script → well-formed woven document** ⚠
*source* a `WovenEdit.Edit n root d`, or an untrusted command list accepted by
the state-indexed checker from a `WellFormed n root d` source · *target*
`WellFormed n root` of the resulting document · *transport*
`WovenEdit.apply_preserves` for one typed edit and
`runCommands_preserves` for a finite raw script · *needs* exactly the
constructor/checker premises: fresh nodes, existing bookmark/update targets,
horizon-bounded clocks, and separation between ordinary writes and the reserved
tombstone value · *without them* `outsideHorizonUpdate_rejected`,
`outsideHorizonTombstone_rejected`, `danglingReference_rejected`, and
`disguisedTombstoneUpdate_rejected` return `none`. `demoCommands_wellFormed`
is the nonempty accepted four-operation path. The transport covers neither
physical deletion/GC nor text, pin, grant, horizon-advance, or cross-tree-hole
edits.

---

## The meta-row

**45. Proved module → covered by the gate** ✗ **was REFUTED, now repaired**
*without it* `Choreo` — 1305 lines, 53 theorems, four ledger rows — sat in the
root and **outside `#audit_floor`** for a full wave, beneath four
"total by construction" claims, while the vacuity tripwire cleared by a factor
of twelve.
⚠ *the repair* `#gate_covers_root` **reads `Uwueave.lean` from disk** and fails
the build on any root module the gate cannot reach. The root cannot be imported
(it imports the gate), so coverage is *checked*, never inherited. Verified
refutable.

---

## What this file is for

Three uses, in order of how much they matter:

1. **A reader arriving cold** should read *this*, not the module list. The
   question "is this one thing?" is answered by whether these crossings hold,
   not by whether the files cite each other.
2. **The next coherence audit should check transports, not names.**
   `docs/COHERENCE.md` verified 756 citations resolve. That is necessary and
   weak. The stronger audit asks: for every adjacent pair of judgements, is
   there a transport theorem or a runnable witness that no unconditional
   transport exists?
3. **A new module owes a row.** Adding a judgement without saying how evidence
   enters and leaves it is how the four surprises happened.

The standing ambition, stated so it can be measured:

> **Every judgement crossing has a transport theorem with exact hypotheses, or a
> runnable witness proving that no such unconditional transport exists.**

Rows currently ✗ with no complete repair: 5 *(superseded by 6–7)*,
16 *(exactly characterized by 16a; the older closure route is only
sufficient)*, 18 *(repaired under record determination by 18a)*, 22b
*(causal-stability contexts unmodelled)*, 27, and 40 *(repaired at the
grounded judgement)*. Row 26 is repaired under `Closed ∧ RosterKnown` while
retaining the single-premise refutation. Preoscript now has the projection,
seam, mergeability, route-invariance, nested document-seam, keyed-cross,
protocol, future-variance, first-order artifact, checked-bundle projection, and
recursive-choreography transports, plus classification export, durable bytes,
exact V1/V2 host validation, deterministic data-only Rust rendering, and the
whole checked export manifest in rows 44a–44r. Rows 44s–44z add conservative
incremental evaluation, communicated choice, finite clash-graph realization,
composite residual patches, finite contextual compilation, six-status effects,
temporal fairness, and checked woven edits. What remains is different work:
declarations still carry no operation vocabulary from which to derive
reachability, no Preo rule produces a typed
`Repair P Q`, multi-field derives and three-or-more-field invariants are
refused.
