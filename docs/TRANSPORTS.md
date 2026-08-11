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

**11. Global seam → live seam** ⚠ **the second hole**
*transport* `LiveSegmented.segmented_implies_liveSegmented` (one line) ·
*strictly* stronger source · *without the converse*
`LiveSegmented.witness_one_latticeOnly_clash` — a seam that is live-valid and
globally refuted, refuted **exactly** at an unreachable pair. And it costs:
`live_optimum_strictly_below_global_optimum` — live width **2**, global width
**3**, both least, with `the_third_domain_is_charged_for_an_unreachable_pair` as
the audit trail.
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

**16. One fork-and-join → repeated history** ✗ **REFUTED**
*without it* `Histories.repeated_merge_breaks_the_invariant` — a *coherent*
history with a legal root and an illegal node. Diagnosed:
`AncestralConfluentFrom` **holds** while `MergeClosedFrom` **fails**, because a
merge **result** is not op-reachable from the base. **The break is the closure,
not the merge.**
⚠ *partial repair* `Histories.History.Coherent.sound` (sufficient, not proved
necessary) and `HistoryBase.coherent_sound_of_runRealized` (needs **no** merge
law, no closure, no confluence).

**17. State-level base validity → history-level** ⚠
*transport* `HistoryBase.ValidInHistory` · *without it* three witnesses in both
directions, incl. `state_unavailable_fires_where_the_dag_hands_a_base` — the
state-level `unavailable` is valid while the DAG hands you a **direct parent of
both**. The two obligations are **logically independent**.
✅ *and* `HistoryBase.coherent_never_unavailable`: `unavailable` is a
**cross-history** answer, never satisfiable while walking one coherent history.

**18. Invariant safety → convergence** ✗ **REFUTED**
*without it* `Histories.swap_never_converges` — an eternal two-cycle under a
base policy `MergeModel.BaseDecision.Valid` fully licenses. Safety is not
agreement.

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
unsound for the **view**. ◻ `Closed ∧ RosterKnown` unbuilt (needs a `render`
congruence `Evidence.lean` lacks).

**27. Capability declaration → property of the computation** ✗ **REFUTED**
*without it* `ResultStatus.declaration_is_relative_to_the_reach` — the same
evaluator and the same declaration, satisfied over one reachable set and refuted
over that set closed under a **single** admissible extension. A capability is a
property of a computation **over a reach**.

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

Rows currently ✗ with no repair: 5 *(superseded by 6–7)*, 16 *(partial)*, 18,
26, 27, 40 *(repaired at a different judgement)*. Rows ◻ unbuilt: the
`Closed ∧ RosterKnown` certificate, and every crossing into `Preo` — the
language has verdict rows but no transport rows, which is the next thing this
file will be embarrassed about.
