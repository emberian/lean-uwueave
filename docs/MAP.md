# The map — the classified modules, and what each settles

The theorem-by-file guide. Each row names its keystone theorems so the claims
are checkable rather than vibes. Trust is enforced wholesale, not per-name:
`Uwueave/Audit.lean`'s `#audit_floor` walks every constant in the namespace
and fails the build on any axiom outside Lean's floor — a stray `sorry` or
`native_decide` anywhere in the tree goes red, zero-lag, no list to maintain.
(That total coverage is a fact about the **gate**, not about this table; the
[ledger](#keystone-ledger) below is a reading aid, not a trust mechanism.)

✅ **Coverage, 2026-08-11.** The file table below has one row for each of the
78 tracked Lean module files under `Uwueave/`, including the nested `Preo` and
`Tactics` modules. This is a documentation invariant rather than a trust
mechanism: the root aggregator and `#gate_covers_root` remain the authorities
for transitive gate coverage. Re-derive the table's coverage instead of
trusting this prose after adding or moving a module:

```sh
for f in $(git ls-files 'Uwueave/*.lean'); do
  grep -q "\`$f\` |" docs/MAP.md || echo "$f"
done
```

⚠ **Novelty claims, 2026-08-11.** An external review found eight claims of ours
that the literature refutes or narrows; they are retracted where they were made
and indexed in `FORCODEX.md` §0.5, with the papers annotated in
`docs/BIBLIOGRAPHY.md`. Two of them touch rows in this table and are folded into
them below: the choreography × CRDT junction is **not** empty (Kuhn–Melgratti–
Tuosto, ECOOP 2023, project swarm protocols to local-first peers), and
typed holes × replicated collaborative editing is **not** unclaimed (Grove,
POPL 2025, represents merge conflicts as holes over a CmRDT edit log). The
theorems in those rows are unaffected — what changed is the size of the claim
around them. **A theorem's truth and a project's priority are different
questions, and only the first one is machine-checked here.**

Two axes qualify every keystone (the [ledger](#keystone-ledger) below carries
them per theorem). **Generality** reads the actual statement: *∀-general*
quantifies over a type, an arbitrary invariant/interpreter/action family, or
arbitrary input data (any log, any op array, any word); *parametric* is a fixed
concrete structure with parameters (a rank, a quota, a bound `n`, a root
scope) — a family of facts about one structure, including structure-fixed laws
over all its states; *finite-story* is pinned to concrete constants, usually
`decide`-checked. A refutation being finite-story is normal, not a defect — one
witness kills the general claim — which is why negative results get the second
axis instead. **Reachability** (negative results only: clashes and anomaly
exhibits) asks whether the bad pair is *operationally* reachable, and is
derived **only from the modules' own docstring honesty notes**: *Live* — the
module narrates concurrent op traces from a common ancestor (the strongest
gift: the scenario will actually happen); *LatticeOnly* — the module warns the
state pair may not be jointly reachable under causal delivery (the anomaly
bounds the lattice, not necessarily a deployment); *Unknown* — the module's
docstring does not settle it and this table refuses to guess. (An earlier
*Audit-pinned* column recorded per-theorem axiom pins; audit v2 deleted the
pins in favour of the total gate, so the column was claiming a mechanism that
no longer exists and is gone. `#print axioms <name>` answers per-theorem
curiosity.)

| File | What it settles |
|---|---|
| `Uwueave/Confluence.lean` | The judgement itself: `MergeState`, `IConfluent`, and `escalation_witness` — a failed invariant *always* yields a runnable two-replica repro. Plus the product, Pi, and keyed-cross transports that let document verdicts be computed structurally without pretending separate field proofs establish a relation. |
| `Uwueave/Catalog.lean` | The classic structures — G-Set, counters, LWW, escrow — with merge laws proved and keystone invariants classified. The pattern worth internalizing: ceilings, uniqueness, and mutual exclusion escalate; grow-only facts and per-replica quotas run free; a lone LWW register can never merge-break anything (`lww_every_invariant_iconfluent`) while two LWW registers can break any invariant *relating* them (`lww_cross_field_not_iconfluent`). |
| `Uwueave/Acyclicity.lean` | The DAG dichotomy of part 2 above: `acyclicity_not_iconfluent`, `grounded_iconfluent`, `grounded_acyclic` — packaged as `causal_dag_free`. |
| `Uwueave/Move.lean` | The op-log pattern's guarantee, once and generically (`derived_view_sec`), and its price on a concrete miniature (`view_not_stable`). |
| `Uwueave/ORSet.lean` | Removable sets, both honest ways: add-wins correctly scoped (`orset_present_survives`), unscoped presence refuted (`orset_present_not_iconfluent`), and the causal-length set free per-element (`clset_present_iconfluent`). §3 is the module's other half and the reason the refutation is not the whole story: the **remove-shape dichotomy**. The clash needs a replica to tombstone one tag while keeping another, which the element-wide "remove all observed tags" op (`removeAll`) cannot do — so on *that* protocol class the same invariant is I-confluent (`orset_ew_present_iconfluent`), and `CausalReach.lean` §6 settles it causally (`ew_clashL_unreachable`, `orset_reachability_depends_on_remove_shape`). Verdict follows the remove, not the set. |
| `Uwueave/Causality.lean` | Vector clocks: the clock order *is* the merge's order (`vclock_leq_iff`) — and fork evidence is forever (`fork_evidence_iconfluent`): a peer caught equivocating cannot gossip its way back to innocence. |
| `Uwueave/MVRegister.lean` | The multi-value register: keep the fork, show the fork. Concurrent writes both surface (`conflict_surfaces`); resolving is just another write (`resolution_is_a_write`). For a loom this isn't conflict *handling* — forks are the product. |
| `Uwueave/Undo.lean` | Multi-user undo/redo as ordinary writes at fresh clocks — the view restores (`undo_restores`), history is never rewritten (`undo_preserves_history`), and a concurrent undo conflicts *visibly* instead of losing silently. |
| `Uwueave/Delta.lean` | Why shipping deltas instead of states is sound: `joinAll` is exactly the least upper bound, and `same_deltas_same_state` — same delta-set, any order, any duplication, any batching, same replica. Twelve of its sixteen theorems use no axioms at all. |
| `Uwueave/Sequence.lean` | The text layer, with its boundary drawn precisely: membership and anchor-order hold from well-formedness alone; exactly-once needs an id-uniqueness premise *and we prove that premise isn't free* — nor is it hash injectivity (no finite hash has that): `uniqueAnchor_violation_extracts_collision` reads any violation as a constructive hash-collision exhibit, the computational-CR handoff; and the centerpiece is a concrete interleaving-anomaly witness — two runs merging to `[4,3,2,1]`, strictly alternated. No-interleaving is explicitly *not* claimed; that's what real sequence CRDTs (loro, Fugue) are for. |
| `Uwueave/Segmented.lean` | The gentlest verdict: some invariants that fail globally are free *within a seam* (`budget_segmented` vs `budget_not_iconfluent` — same invariant, both verdicts). Spend freely inside your quota; coordinate only to re-divide it. |
| `Uwueave/Spec.lean` | A composition DSL where verdicts carry their evidence: a schema's answer is either a proof or a counterexample transported up from the exact field that caused it. |
| `Uwueave/Seams.lean` | Seams two and three, so `SegmentedIConfluent` is a design recipe rather than one museum piece: the **epoch seam** (`epoch_sole_not_iconfluent` / `epoch_segmented` — duelling admins clash across the boundary, merge freely within it; plus the proved dead end `sole_unpinned_not_segmented`: the epoch *alone* fixes nothing) and the **schema-version seam** (`schema_tightening_not_iconfluent` / `schema_segmented` — a tightening migration is a flag day; `schema_widening_iconfluent` — widening needs no seam at all, the proof-shaped expand/contract asymmetry). Both packaged as `SegVerdict`s beside the budget. ⚠ Read §1 with `Era.lean`'s four corrections: the docstrings' original protocol reading (named-winner arbiter, per-replica epoch, coordinated boundary crossing) was guessed from the paper's abstract and corrected by the implementation — the carrier's theorems stand; the mechanism story is Era's. |
| `Uwueave/Weave.lean` | A real weave library's feature list classified feature-by-feature — including the loom-specific theorem that a *shared* replicated active path is not a CRDT (`active_path_not_iconfluent`); make it per-user, which is better UX anyway. |
| `Uwueave/Exec.lean` | The executable kernel: the move-replay decision procedure, authored in Lean, exported to C, and linked into the Rust crate — factored so `replay` is *by definition* decode → `gatedReplayFull` → encode, leaving no bytes-vs-decision gap to prove. **Format v3**, and v2 requests no longer parse: a magic word makes the flag day loud, and bytes without it get an *empty* response rather than a guess. v3 gives the request an authority substrate, so the op gate `Uwueave/Gated.lean` models runs *inside the shipping kernel*, and the per-op trace carries four codes — applied, skipped (cycle rule), skipped (invalid index), and `3` = skipped (unauthorised) — which is what makes `view_not_stable`'s priced anomaly visible to UIs. **Two** opens, stated in its header and neither of them terminal: (a) the Rust marshaller's byte-for-byte agreement with `encodeRequest`, differentially checked against the proven canonical encoder but through a `debug_assert!`, so compiled out of release builds; (b) everything downstream of the C backend — which is not one boundary but **nine named obligations with named next steps**, decomposed in [`docs/TRUST.md`](TRUST.md) Ledger 2 (ten rows: zero PREMISE, nine OBLIGATION, one absent component). CakeML is the existence proof for the codegen half; CompCert covers exactly one row, the C compiler, and does **not** reach Lean's IR→C step. |
| `Uwueave/ExecRefine.lean` | The kernel's theorems: **`absReplay_acyclic`** — for a grounded base and *arbitrary* op arrays (any order, duplicates, junk indices), the replayed view has no cycle; fuel adequacy (`chainHits_decides`, from-scratch pigeonhole); the output codec round-trip capped by `decode_encode_id`. `miniInterp_acyclic`, generalized from the two-op toy to the real kernel. Wave 5 closed the rest: **`kernel_derived_view_sec`** (SEC's three clauses for `absReplay` itself) via **`absReplay_ext_mem`** (the kernel is a function of the op *set*), the miniInterp bridge (`miniReplay_eq_miniInterp` + `absReplay_matches_miniInterp` — same rule, two presentations, machine-checked), and the input codec (`replay_encodeRequest`). |
| `Uwueave/Audit.lean` | The trust gate, total: `#audit_floor` audits **every** constant in the `Uwueave` namespace against the axiom floor `{propext, Classical.choice, Quot.sound}` — `sorry` (`sorryAx`) and `native_decide` (`ofReduceBool`) are build failures everywhere, with a vacuity tripwire so the gate itself cannot pass on an empty walk. Replaced 113 per-theorem pins on 2026-08-10; the file's header carries the honest accounting. |
| `Uwueave/ORMap.lean` | The observed-remove map — documents are maps. Add-wins scoped (`ormap_get_survives`), the **doomed-update anomaly** as a theorem (a nested write concurrent with its key's removal survives the merge but is masked by the view), and the centerpiece: remove-wins and update-wins views provably *disagree on the same merged state* (`ormap_policy_divergence`) — the merge is policy-neutral; the choice is yours and visible. |
| `Uwueave/Automata.lean` | Replicated automata sorted by the same verdicts: semilattice-action runs converge as instances of the delta laws (`run_same_inputs`); commuting inputs may be replayed in any order (`exec_perm`, axiom-free — the seed of the Mazurkiewicz/Zielonka connection, cited not claimed); DFA determinism is the uniqueness ceiling (concrete clash), with LWW-arbitration vs accept-the-NFA priced as exits; token firing under escrow reads the segmented theorems as Petri nets. |
| `Uwueave/Authority.lean` | Local-first permissions: delegation chains as a grounded CRDT — issuing narrowed grants is coordination-free (`wf_iconfluent`), authority provably only narrows (`scope_le_root`), sole-admin escalates (the duelling-admins clash), revocation's late arrivals only ever *shrink* authority (`authority_view_antitone`) — the derived view's instability points fail-closed, the security dual of `view_not_stable` — and the per-id uniqueness premise is priced like Sequence's: `uniqueGrant_violation_extracts_collision` turns any violation into a hash-collision exhibit (collision resistance, not injectivity, is what a deployment supplies). |
| `Uwueave/SeqKernel.lean` | The sequence CRDT, **implemented** the house way: RGA-with-tombstones order decision authored in Lean, exported as `uwueave_seq_kernel` beside the move kernel. Proved: every visible element appears (`linearizeK_mem`), exactly once (`linearizeK_nodup` — groundedness alone), ancestors precede (`linearizeK_ancestor_precedes`), and deletes filter without reordering (`linearizeK_sublist_emitAll`). The brief's index-ordered hypothesis was refuted by the lane as vacuous-for-real-inputs and replaced by rank-groundedness. Non-claims: `interleaving_anomaly` still governs (reproduced through the shipping kernel in a Rust test); Fugue cited, not implemented. |
| `Uwueave/Holes.lean` | **The hole calculus** — replicated computation with multi-candidate results. Worlds carry correlations (the set monad's phantom candidates proved both directions on one witness), and the headline `evalSet_hom` needs *no hypothesis on the program*: compute-then-merge = merge-then-compute, unconditionally — images are free; the whole price sits in wanting one answer (`determinate_result_not_iconfluent`, the ceiling pulled back through evaluation). `stable_inputs_seal_the_result` transports input stability to result stability along the hom in one rewrite; provenance rides by type into `MVReg`. ⚠ Read the header's three retractions: the hom holds because *images* distribute over unions, not because machinery "transfers unchanged" (monotone ≠ join-preserving — see `JoinHom.lean`); a monotone expression's holes fill by gossip **only** under a finite closed scope with fair complete delivery (Power–Koutris–Hellerstein 2025); and a freeze, a causal cut and an arbiter cut play one role with three different evidentiary meanings. Prior art: Hazel-style holes over replicated collaborative editing is Grove (POPL 2025); a generic partial-value calculus is λ∨ (Rioux–Zdancewic 2025). |
| `Uwueave/Gluing.lean` | **`guardGluing_iff_iconfluent`** — named four times in a sibling repo's design study and never built there (its kernel forbade partial cones). Guarded holes with delta-shaped fills; divergent fills glue iff the guard is I-confluent, under `Spanning` — and `stampedHole` proves the iff is *not a renaming* — `Spanning` is **not removable** (`stampedHole_glues` + `excl_not_iconfluent`: a non-spanning hole that glues while its guard clashes), so `Glues` and `IConfluent` are genuinely different predicates. ⚠ Read the direction: `Spanning` is *sufficient*, not proved necessary — the ⟸ half of `guardGluing_iff_iconfluent` never touches it. Consequences: the sheaf-shaped `glue_eq_merged_fill`, a hole verdict `Spec.Verdict` cannot express, partially-glueable holes via seams, and one-shot *sharpened*: gluing licenses local double-fill. |
| `Uwueave/Cost.lean` | **Coordination frequency is real and has a floor**: `crossings` counts σ-changes along a workload, and `coordination_forced` shows clash blocks in the *spec* force the count for every seam in every universe. Tight instance: three budget re-divisions cost exactly 3. Self-correction included: linking seams did **not** lower the document's floor — it made the obvious seam optimal. The undercounting verdict is proved and stated as the measure's domain of validity. |
| `Uwueave/Choreo.lean` | **The verdict moves onto the program**: choreographies over replica-owned CRDT state, endpoint projection with `projection_sound` as pointwise state equality (no bisimulation — the channel *is* the lattice), and `coordination_free_iff_iconfluent`, iff-shaped with neither direction `Iff.rfl`. The seam refinement the in-house prior art never had: `seam_coordination_free` — barriers exactly at σ-changes, free within fibers, no global `IConfluent` hypothesis anywhere. ⚠ Retracted with the file: the choreography × CRDT junction is **not** empty — Kuhn–Melgratti–Tuosto (ECOOP 2023) project swarm protocols to local-first peer machines with progress under unavailability. The defensible claim is narrower: an I-confluence-derived coordination verdict **plus** a seam refinement over it is what we could not find elsewhere. |
| `Uwueave/Scheduling.lean` | **Crossings are effects; meetings discharge coeffects.** `Session.comp` adds crossing counts while reindexing proof-carrying obligation origins, and `SessionProfile.comp` retains one shared strategy until a `ProfilePlan` chooses it. Schedules witness coverage and retain five separate currencies. The exact 2-crossings→1-meeting, 0→1, and 1→2 examples prove neither scalar determines the other; `no_crossing_count_determines_least_meetings` is the explicit non-function. No `Budget.ForcedFloor`→meeting-floor or unannotated `Choreo` extraction is claimed. |
| `Uwueave/RALin.lean` | **Correctness ≠ safety**, against Sal (arXiv:2603.27202): `ra_linearizable_but_unsafe` — Sal's own Table-2 PN-counter, RA-linearizable for any fork and branches, every branch legal at every prefix, and the merge overdraws. Converse: the max-counter loses updates, making *every* invariant I-confluent while failing RA-lin — safety bought by data loss. `quadrants` inhabits all four cells; `ra_lin_preserves_inductive_invariants` (axiom-free) is what RA-lin *does* buy; `guarding_moves_the_bug` shows the verdicts entangled through op preconditions. |
| `Uwueave/Ancestral.lean` | **The LCA question, answered: incomparable.** Two-way I-confluence can be bought by a join that drops a committed op (effect-faithfulness is the honesty condition); mutual exclusion under hand-off is free with an ancestor (`lock_ancestral_confluent`) and provably beyond every two-way join; the bounded counter is beyond every honest merge (`budget_defeats_every_faithful_merge`) — escrow stands. `clash_dichotomy` names the rule: **resurrection** clashes an LCA repairs; **accumulation** clashes nothing repairs. |
| `Uwueave/SeamAlgebra.lean` | The calculus segmented confluence lacked: product/pi/and lifts hold; refinement REFUTED (a conjunctive observation over grow-only fields is not a seam); free-riding refuted with stability pinned necessary and sufficient; the dividing line as an iff (`left_only_seam_iff`); and the prize, `linked_segmented` — two seams collapse into one exactly where well-formedness makes one seam a function of the other. `selfSeam` turns an already-certified clash into the conservative identity seam, while `prependFree` supplies the conjunction-order mirror needed to reconstruct the hand weave seam. |
| `Uwueave/GatedEra.lean` | Arbitrated authority composed with the op gate: `ge_deterministic`, `ge_duel_resolved` (the survivor's op stands where fail-closed denied both), `ge_finalised_stable`. The finding: `antitone_forbids_enabling` — any permission rule antitone in event growth makes promotion impossible. Fail-closed guarantees shrinkage; arbitration guarantees agreement; the trade is a theorem. |
| `Uwueave/Tactics.lean` | `classify` — five kernel-checked routes to a verdict; failure is loud and carries the clash, and "no clash found" is explicitly **NO VERDICT**. Adversarially verified against false goals. Plus the idiom kit with a measured ~161→25-line shrink list beside a measured not-replaceable list. |
| `Uwueave/Era.lean` | The ERA protocol core, **implemented** from the paper (cuts, epochs, the four-op grammar, authorised execution, sorted-insert canonicalisation): delivery-independence by the set-function route (`resolve_same_sets`), rollback-immunity of the finalised prefix (`final_view_immune`), and the payoff — `duelling_admins_resolved`: one deterministic survivor at every replica, where `Authority.duelling_admins_annihilate` killed both. Corrects four guesses in `Seams.lean` (headline: the arbiter never names a winner, only orders events — and nobody coordinates; the epoch boundary is a trusted announcement priced in rollback). |
| `Uwueave/Necessity.lean` | **Bailis necessity, modeled** (delivered by grok via `GROKJOB.md`): an execution model where coordination-freedom is definitional (`Impl.tryApply` sees local state only), and the theorem the library previously only cited — a *reachable* clash refutes coordination-free-convergent-safety (`necessity`, axiom-free core), with sufficiency back (`iconfluent_implies_cfcs`). Satisfiable (`gset_true_is_cfcs`) and refutable (`atMostOneBit_necessity`) per the job's falsifiability bar; the MAP's Live/LatticeOnly axis is now a formal hypothesis (`ReachableClash`). |
| `Uwueave/CausalReach.lean` | **Op-based causal cuts** (JOB 2 + residuals): `FinHistory` / `Cut` / `Joint`; clash states are definitionally cut interpretations. Tag-scoped rem-after-add ⇒ OR-Set presence clash **Live** (`orset_clash_joint`); **element-wide rem after both adds** ⇒ same lattice pair **unreachable** (`ew_clashL_unreachable` / `orset_reachability_depends_on_remove_shape` — protocol dichotomy). Concurrent miniatures Live; free-id dup fragments Live; illegal cuts rejected. Content-addressing out of band. |
| `Uwueave/Liveness.lean` | **SEC liveness half** (JOB 4): finite-covering fairness `FairOn` + `fair_converges` lands every listed replica at `joinAll base issued` (rides `Delta.same_deltas_same_state`); G-Set `unfair_starvation` witness; two-replica `pair_exchange_converges`. Not coinductive ∞-often delivery — header says so. |
| `Uwueave/Traces.lean` | **One dependent pair** (JOB 5): 3-letter alphabet, independence `a∥b`, `a∥c`, not `b∥c`; `TraceEq`; `exec_traceEq`; negative `dependent_pair_reordering_changes_exec`; real bridge `exec_perm_of_fullIndep` (fullIndep → TraceEq → exec, not a dead hypothesis). Not full Zielonka. |
| `Uwueave/Nary.lean` | **n-ary tails** (JOB 6): `net_enum`, PN nonneg refutation over any two distinct keys, escrow sum bound over enum, `BudgetInvN` / `budget_segmented_enum`; Catalog/Segmented Bool results recover as instances; zero new `MergeState` proofs. |
| `Uwueave/KernelCFCS.lean` | **Move kernel as `Necessity.Impl`** (JOB 7): honest that under `GroundedBase` the derived-acyclicity invariant is true of every log (embedding package, not new confluence); real content is materialization ↔ membership and view determination via `absReplay_ext_mem`; `move_kernel_cfcs` + `move_kernel_view_sec`. |
| `Uwueave/Ceiling.lean` | The four uniqueness refutations proved to be **one theorem**: `uniqueness_ceiling` — an invariant entailing "at most one element per selector key" over a grow-only set is never I-confluent — with the generic witness constructor `merge_breaks_uniqueOn` (two distinct same-key elements, one per replica, produce the clash). `ceiling_atMostOne` / `ceiling_uniqueAnchor` / `ceiling_uniqueGrant` / `ceiling_determinism` re-derive the Catalog, Sequence, Authority and Automata refutations verbatim as one-line instances, at the originals' own witnesses; the originals stay in their home files with their narratives and pins. The mutex-shaped ceilings (`or_breaks_iconfluence`, sole-admin) are the same trap but a different selector shape — they cap occupied *keys*, not elements per key — and keep their own refutations. |
| `Uwueave/Budget.lean` | A budget trichotomy whose constructors carry the right kind of evidence: a witnessed plan may accept, a forced floor may reject (`rejected_sound`), and a named synthesis gap remains unresolved. `lower_bound_does_not_license_acceptance` refutes acceptance from one affordable lower bound, while `reblocking_escapes_the_floor` proves that changing the workload's blocking would invalidate rejection. The unit is per-stream seam crossings, not meetings. |
| `Uwueave/CoordEffect.lean` | Coordination grades are strategy-indexed cost profiles, composed pointwise and minimized only when the session closes. `opt_compose_ge_sum_opt` names the compositional inequality, `optimum_compose_achieved` returns one coherent strategy that pays the result, and `pin_session_costs_exactly_one` proves the scalar alternative reports 0 for a session that costs 1. The strategy list is finite, nonempty, and chosen — not an enumeration of every seam. |
| `Uwueave/EraKernel.lean` | The executable ERA codec and `@[export uwueave_era_resolve]`: Rust marshals bytes, while this module calls `Era.resolve` and emits roles plus per-event status. `eraReplay_same_sets` proves byte-level delivery independence for the whole response; `duel_trace_marks_the_skip` and `duel_response_words` expose the paper's duel through the shipped format. Event-id uniqueness is enforced by the Rust boundary for attribution, not required here for deterministic resolution. |
| `Uwueave/Evidence.lean` | The epistemic carrier separates candidates, outstanding obligations, and certificates, yielding exact/provisional and closed/open fork states instead of conflating value plurality with future openness. `closed_iconfluent` says closure merges while determinacy does not; `divergent_futures_force_nonexact` forbids exactness across admissible divergent futures. `render_retracts_when_a_new_source_appears` pins the boundary: `render` is sound for the sealed future, not arbitrary membership extension. |
| `Uwueave/Exits.lean` | The eight-exit display vocabulary and its worked ceiling, balance, and duel menus. Its typed applicability witnesses and refutations remain useful, but `Exit.price` and the hand-authored rows are explicitly superseded as semantic authority by `RepairMenu`: the price is independent free data, and the ceiling seam row demonstrably prints 0 where 1 is forced. Escrow tracks divisibility, not the resurrection/accumulation dichotomy. |
| `Uwueave/Fugue.lean` | A Fugue-style left/right origin tree, its op-set insertion model, and the RGA contrast on the same editing intent. `run_contiguous` / `fugue_runs_never_interleave` prove generated concurrent runs remain contiguous under the stated groundedness and concurrency hypotheses; `rga_head_runs_interleave` versus `fugue_head_runs_stay_contiguous` exhibits the concrete anomaly and repair. This is the model and theorem, not the shipping sequence kernel. |
| `Uwueave/Gated.lean` | Authorization as a derived view over grants, revocations, and move ops. `gated_sec` inherits SEC, `gated_antitone` proves late revocation can only remove effects, and `kernel_gate_agrees_gatedOps` connects the model to the shipping kernel under `WF` plus unique grants. Signatures remain a deployment premise; the gate bounds what a cited grant may do, not who may cite it. |
| `Uwueave/Histories.lean` | Repeated and criss-cross merge over a rank-grounded version DAG. `repeated_merge_breaks_the_invariant` shows the one-fork ancestral theorem does not close under merging its own results; `base_accident_decides_the_invariant` gives two equally maximal bases with legal versus illegal outcomes; `swap_never_converges` proves coherent base choice alone is not convergence. The failure is merge closure, not the one-step merge theorem. |
| `Uwueave/HonestRender.lean` | Rendering honesty over an abstract five-way carrier: `consumers_factor` proves every consumer is a five-handler dispatch, `no_honest_projection` rules out a silent total projection at a forked site, and `singularSelection_implies_namedPolicy` makes singular resolution name its policy. `salience_is_not_enforceable` is a proved limit: an abstract interface cannot force visually distinct pixels. The five-way inability to separate absent from pending is repaired, not erased, by `RenderSix`. |
| `Uwueave/JoinHom.lean` | The exact boundary between shipping evidence and shipping a derived summary. `summaryFold_iff_joinHom` is the architecture iff; `no_count_merge_without_provenance` refutes every binary combiner on counts; `count_summary_must_distinguish` makes provenance necessary. `monotone_pullback_can_fail` retracts the stronger monotonicity claim: upward-closed result invariants pull back, arbitrary ones do not. |
| `Uwueave/MergeModel.lean` | One parameterized confluence judgement over genuinely different merge signatures: join CRDT, ancestral/MRDT, and op-replay. Laws are separate predicates rather than class fields; the ancestral witness is refutably non-idempotent, and op-replay is a function of the op set but not of the two materialized views. `iconfluentIn_join_iff` and `iconfluentIn_ancestral_iff` recover the existing judgements without reproving them. |
| `Uwueave/MinimalSummary.lean` | Contextual equivalence constructs the coarsest future-sufficient *partition* for a query. `ctxQuot_coarsest_sufficient` proves the universal property and `ctxQuot_fold_answers` makes the quotient shippable; membership collapses to one bit, exact count collapses nothing, and the three-element threshold quotient has five classes. This is not a minimum-bit representation or a reachable-context quotient. |
| `Uwueave/Recoverable.lean` | The positive ancestral converse, with the merge constructed: `faithful_stepConfluent_iff_legalSerialization` characterizes when recoverable deltas admit a faithful invariant-preserving three-way merge. `comm_forces_symmetric_chooser` derives chooser symmetry from commutativity, while `budget_boundary` isolates illegal serialization as the counter obstruction. Step confluence alone still does not lift through longer branches. |
| `Uwueave/Repair.lean` | Typed transformations `Repair P Q`, multidimensional `Price`, and five-axis `PromiseRelation` replace a flat exit plus scalar. `introduced_premise_forces_a_charge` and `no_free_arbitration` make trust costs unprintable as free; `crossings_cannot_see_the_difference` proves a crossing count cannot distinguish arbitration, fork exposure, and retained evidence. Repairs compose, but their summed declared prices are not claimed minimal and nothing here searches for a repair. |
| `Uwueave/ResultStatus.lean` | Six runtime statuses separate static mergeability from reach-relative capability. `declaration_is_relative_to_the_reach` proves one declaration can hold on a reach and fail after one admissible extension; `sixth_cell_is_distinguishable` separates definitive absence from pending despite identical empty candidate sets. `forget_statusOf` recovers the five-way render, and value-dependent finality refutes any status determined only by closure structure. |
| `Uwueave/SeamColoring.lean` | The safety clause of segmentation is exactly graph colouring (`safetyClause_iff_properColoring`); full segmentation additionally needs fiber stability, and `coloring_alone_does_not_segment` proves that residual is real. `synthesizeSeam?` returns a certified seam or an honest `none`; on the pin ceiling, traversal order recovers each hand-written seam. No completeness is claimed without a covering finite pool. |
| `Uwueave/Tactics/Core.lean` | The cycle-free machinery below the `classify` demonstrations and verdict-value layer: complete `FinEnum`s, heuristic `Probes`, the `Clash` evidence type, the search `findClash`, and the positive tactic routes. `Clash.not_iconfluent` makes every returned hit a refutation, while `findClash_none` says only that the supplied pool contains no clash. Verdict-valued `classifyIn?` / `classifyFinite` deliberately live one module up because `Spec.Verdict` would reintroduce the import cycle. |
| `Uwueave/WeaveState.lean` | The library's composed loom document: node/content/activation/bookmark/pin/authority/quota fields inherit their merges, and `core_iconfluent` assembles the free field invariants. The pin ceiling stays deliberately live in `weaveDocVerdict`; `weaveDoc_segmented` lifts the combined pin/allocation seam to the whole document. It is a classified miniature, not a claim that text, moves, signatures, or networking are modeled here. |
| `Uwueave/Wellformed.lean` | Structural well-formedness is separated from application legality. `merge_preserves_wellformed` is unconditional, while `merged_doc_violates_onePin_but_is_wellFormed` proves a merge can violate the pin promise and remain a renderable document; `no_crash` quantifies over every reader total on well-formed documents. Unique anchors are deliberately excluded because including them would make the headline false. |
| `Uwueave/WorldFuture.lean` | Futures indexed by epistemic worlds rather than materialized states. `delivery_future_is_not_state_indexed` exhibits equal observed states with different issued-but-undelivered pools; `quiescence_is_a_sound_certificate` makes the world-keyed check sound, while `no_sound_state_cert_accepts_openW` proves that reusing the same fact at the state key is impossible. Frontier plus epoch still does not separate the witness; the pool does. |
| `Uwueave/Bounds.lean` | The modal and quantitative lower bounds meet in `coordination_necessary_and_costly`, but not at zero: `zero_floor_does_not_imply_cfcs` gives live pin forks that every per-stream clash decomposition misses. `fork_clash_charges_the_pair` recovers the missing joint charge. `ew_rejected_at_zero_over_unreachable_pair` then exposes the old cost model's reachability hole by rejecting on the element-wide OR-Set pair that no protocol cut reaches. |
| `Uwueave/CertificateScope.lean` | Future-sufficient keys as the quotient by equal residual futures, with `resQuot_coarsest_sufficient` proving the factorization property. This resembles `MinimalSummary` only at the kernel shape: `residual_is_not_a_join_congruence` refutes a merge on these classes. `deliveryKey_sufficient` shows the pool belongs in the key and the epoch may be dropped; `closed_is_not_a_sound_delivery_certificate` separates value closure from view finality. |
| `Uwueave/CliqueLive.lean` | Clique certificates jointly constrain live seam width and fork-scenario cost. `live_clique_forces_live_width` and `live_clique_forces_scenario_floor` are general lower bounds; `the_live_clique_number_determines_both` pins the slot witness at live 2 versus global 3. Width is not claimed equal to clique number in general: colouring may need more colours, and seam stability adds non-graph obligations; `the_two_floors_are_incomparable` says block and clique floors must both be reported. |
| `Uwueave/DerivedDocument.lean` | Evidence is encoded as a document without loss (`encodeEvidence_iso`), and `deriveDoc_hom` makes "a computation over a loom yields a little loom" a one-line join-hom composition. `tallyDoc_requires_evidence` transfers the count impossibility to documents while `seenDoc_joinHom` exhibits the provenance-retaining escape. Rank-grounded pipelines terminate and merge freely; acyclicity alone is explicitly weaker. `docStatus_encodeEvidence` lets the six-status renderer serve both primary evidence and derived documents. |
| `Uwueave/EraCertificate.lean` | ERA finalization as a delivery certificate: under the readable `Settled` premise, `era_finalisation_is_a_sound_certificate`; `era_stops_before_quiescence` shows the final prefix can stabilize while the full view still moves. Honest cut extension preserves that prefix, but `backdated_cut_rewrites_the_finalised_view` refutes the claim without the hypothesis. `an_event_born_finalised_rewrites_the_view` names the Byzantine boundary: announced event ids must be unforgeable. |
| `Uwueave/ForkGrade.lean` | A fork-aware coordination profile whose worlds are path endpoints by construction. `liveScenario_optimum_eq_zero_iff_no_live_clash` reflects zero (the reverse needs the constant seam in the strategy space); `cfcs_iff_locallySafe_and_all_finite_scenarios_zero` bridges the modal and quantitative readings. `the_disagreement_resolved` puts the pin workload's per-stream floor 0 beside its live fork optimum 1 on the same carrier. |
| `Uwueave/HistoryBase.lean` | Merge-base validity moved from state pairs onto a version DAG: `ValidInHistory` means lowest common base, two distinct maximal bases, or a proof that no common ancestor exists. `coherent_never_unavailable` makes unavailable a cross-history answer; the state and history obligations are independent in both directions. Base-scoped state certificates are sound where unscoped and root-scoped reuse fail, and `the_model_certifies_what_the_history_breaks` shows a safe state-level decision model can refuse the very merge a real history records. |
| `Uwueave/HistoryPolicy.lean` | Four policy judgements — base robustness, selector safety, explicit ambiguity, and history convergence — with their separations inhabited. The crown is `recordDetermined_converges`: equal records under one record-determined policy derive equal views over any rank-grounded version DAG. `the_swap_is_order_dependence` identifies the two-cycle as asymmetric self-base selection, and `the_self_base_policy_is_not_history_licensed` shows history validity refuses exactly that policy. |
| `Uwueave/LiveBudget.lean` | A reachability-aware budget verdict: only `liveRejected` carries a proof that the realized path cost agrees with the abstract workload; `carrierGlobalBound` has no model field and therefore cannot claim liveness. `ew_no_live_realization` proves the element-wide workload admits no live realization at all, while `claim_sound` assigns each constructor exactly the proposition it may print. `pathSegmented_iff_liveSegmented` connects the path-local strategy space to `LiveSegmented`. |
| `Uwueave/LiveCost.lean` | Proof-carrying paths replace reachability side conditions. `ClashChain.accused_are_connected` follows from construction, `cost_floor_becomes_live` names the required total simulation `Grounds`, and `totalModel_grounds_everything` says why a permissive model gives the repair no teeth. The tag-scoped OR-Set clash is live and charged; the element-wide pair refuses a live accusation and `ewTeleport_not_grounded` locates the failed transport. |
| `Uwueave/LiveSegmented.lean` | Segmentation relativized to co-reachable states, closing the strategy-space reachability hole. `live_optimum_strictly_below_global_optimum` proves least live width 2 versus least carrier-global width 3; `the_third_domain_is_charged_for_an_unreachable_pair` identifies the exact extra edge. The safety clause still equals live proper colouring, while fiber stability remains independent; the file records which `SeamAlgebra` laws survive or need weaker live hypotheses. |
| `Uwueave/MenuTotality.lean` | Makes seam-menu applicability decidable over a covering pool, provides real synthesis, and replaces a free hand-authored floor with a clique-backed `CertifiedSeam`. `uniqueOn_singletons_clash_iff` corrects the false "ceiling graph is complete" conjecture; `atMostOne_seam_row_refuted_at_every_finite_segment` shows the `Nat` ceiling admits no finite seam. `clique_forces_joint_crossings` supplies the concurrent `k-1` floor that `the_clique_floor_is_invisible_to_the_block_calculus` proves the sequential block calculus cannot see. |
| `Uwueave/Preo/Classification.lean` | Fragment 2's facet algebra: rules accumulate global verdicts, seams, mergeability results, or honest obligations. `verdict_agree`, `seam_forces_clash`, and `fourth_unique` prevent contradictory evidence; `run_answer_of_perm` proves route-order invariance. `mergeability_comp` transports a derived computation along one field projection, requiring surjectivity only for the negative `needsEvidence` direction. |
| `Uwueave/Preo/Demo.lean` | Executable acceptance tests for `preo`: `LoomDoc2` retains seam/cross/derive facets; `TwinQuota` derives a product document seam; `NestedSurface` finds two seams through eight fields and absorbs six checked FREE rows; `KeyedDoc` makes `per` change the carrier and re-derives `WeaveState.bookmarksVerdict` by `rfl`. The general algebra also reconstructs `weaveDocSeamVerdict` as the same value. Unsupported shapes still become obligations. |
| `Uwueave/Preo/Elab.lean` | The command elaborator that turns a `preo` declaration into ordinary state/projection definitions plus kernel-checked `Verdict`, `SegVerdict`, `Fourth.Correct`, or `Obligation` values. It supports keyed `per` carriers, conservative clash self-seams, two seam rows anywhere in a right-nested document, and checked FREE-row absorption. Routes accumulate by facet family and the report reduces its answer from emitted terms; unsupported predicates never inherit a carrier-shaped guess. |
| `Uwueave/Preo/Syntax.lean` | The fragment-2 surface and its small semantic support: six field kinds, optional `field name per Key : Kind` families, one- or two-field invariants, one-field derives, report rows, and an evidence-free `Obligation`. `proj_iconfluent` is the uniform join-homomorphic projection lift. There is deliberately no deep expression AST; ordinary Lean terms stay opaque except for which declared fields they mention. |
| `Uwueave/RenderProgress.lean` | Splits pending truth, fair-delivery progress, and authorized actionability into separate contracts. `statusOf_pending_escapable_by_sealing` proves the old escapability clause can be discharged by abandoning every source; `pending_progress_under_fair_delivery` gives the actual liveness result; `a_revoked_actor_gets_no_button` makes authorization load-bearing. The semantic widget forbids `loading` at `absent`, though pixel salience remains outside the model. |
| `Uwueave/RenderSix.lean` | The six-way carrier and soundness contract that distinguish definitive absence from pending. `five_handlers_cannot_separate` proves the old limit and `six_carrier_separates` retires it; `statusOf_sound6` adds absent-final and pending-escapable obligations while folding back to the five-way contract. `spinner_is_an_honest_five_status_renderer` proves the old interface admits a forever-spinner; `absence_is_the_more_defensible_badge` is specifically a two-sided merge fact, not a unilateral one. |
| `Uwueave/RepairMenu.lean` | Menus generated from typed repairs: every row is available, conditional with a priced obligation, or universally impossible. `menu_price_is_projection` and `menu_delta_is_projection` prevent independent display drift; `ceiling_seam_row_disagrees` demonstrates the old hand row's 0 versus the generated forced 1. The seam acceptance test inhabits all three row constructors, while `no_free_pin_arbitration` and the escrow refutations keep absent rows distinct from impossible ones. |
| `Uwueave/TextSummary.lean` | Applies the summary theorems to sequence views. `no_text_merge_without_provenance` refutes every combiner on rendered text with well-formed replica states; `linearize_not_joinHom` separately exposes a causally pending-anchor boundary. `tombstones_are_load_bearing` and `no_gc_summary_sufficient` prove that deleting the tombstone resurrects a character in a future context, while `tombstoned_content_never_read` isolates what may be discarded. `verdict_order_policy_invariant` shows RGA and Fugue can disagree on order and agree on the evidence verdict. |

## Keystone ledger

The two axes from the paragraph above, per marquee keystone. Names are as cited
in the rows above (namespace prefix omitted where the module is the row's).
Reachability is only for negative results — clashes and anomaly exhibits — and
each `Live` / `LatticeOnly` tag cites nothing beyond the named module's own
docstrings (upgraded by `CausalReach` theorems where those supersede them);
`—` marks rows the axis does not apply to. Every row is covered by
`#audit_floor`'s total gate — there is no per-row trust column to read. The
table currently holds 285 rows:

| Theorem | Module | Generality | Reachability |
|---|---|---|---|
| `escalation_witness` | Confluence | ∀-general | — |
| `product_iconfluent` | Confluence | ∀-general | — |
| `pi_iconfluent` | Confluence | ∀-general | — |
| `gset_mem_iconfluent` | Catalog | ∀-general | — |
| `gset_monotone_iconfluent` | Catalog | ∀-general | — |
| `gset_atMostOne_not_iconfluent` | Catalog | finite-story | Live |
| `or_breaks_iconfluence` | Catalog | finite-story | Live |
| `pncounter_nonneg_not_iconfluent` | Catalog | finite-story | Live |
| `lww_every_invariant_iconfluent` | Catalog | ∀-general | — |
| `lww_cross_field_not_iconfluent` | Catalog | finite-story | Live |
| `escrow_local_bound_iconfluent` | Catalog | parametric | — |
| `acyclicity_not_iconfluent` | Acyclicity | finite-story | Live |
| `grounded_iconfluent` | Acyclicity | parametric | — |
| `grounded_acyclic` | Acyclicity | parametric | — |
| `causal_dag_free` | Acyclicity | parametric | — |
| `derived_view_sec` | Move | ∀-general | — |
| `view_not_stable` | Move | finite-story | Live |
| `miniInterp_acyclic` | Move | finite-story | — |
| `orset_present_survives` | ORSet | ∀-general | — |
| `orset_present_not_iconfluent` | ORSet | finite-story | Live |
| `clset_present_iconfluent` | ORSet | ∀-general | — |
| `vclock_leq_iff` | Causality | ∀-general | — |
| `fork_evidence_iconfluent` | Causality | parametric | — |
| `conflict_surfaces` | MVRegister | finite-story | — |
| `resolution_is_a_write` | MVRegister | finite-story | — |
| `undo_restores` | Undo | finite-story | — |
| `undo_preserves_history` | Undo | finite-story | — |
| `undo_conflicts_visibly` | Undo | finite-story | — |
| `joinAll_perm` | Delta | ∀-general | — |
| `joinAll_append_merge` | Delta | ∀-general | — |
| `same_deltas_same_state` | Delta | ∀-general | — |
| `wf_iconfluent` | Sequence | parametric | — |
| `linearize_mem` | Sequence | parametric | — |
| `linearize_anchor_precedes` | Sequence | parametric | — |
| `linearize_count_one` | Sequence | parametric | — |
| `wf_unique_anchor_not_iconfluent` | Sequence | finite-story | Unknown |
| `interleaving_anomaly` | Sequence | finite-story | Live |
| `iconfluent_iff_trivially_segmented` | Segmented | ∀-general | — |
| `budget_not_iconfluent` | Segmented | finite-story | Live |
| `budget_segmented` | Segmented | parametric | — |
| `epoch_sole_not_iconfluent` | Seams | finite-story | Live |
| `epoch_segmented` | Seams | parametric | — |
| `schema_widening_iconfluent` | Seams | parametric | — |
| `schema_tightening_not_iconfluent` | Seams | finite-story | Live |
| `schema_segmented` | Seams | parametric | — |
| `Verdict.keyedClash` (def) | Spec | ∀-general | — |
| `active_path_not_iconfluent` | Weave | finite-story | Live |
| `absReplay_acyclic` | ExecRefine | ∀-general | — |
| `kernel_derived_view_sec` | ExecRefine | ∀-general | — |
| `evalSet_hom` | Holes | ∀-general | — |
| `determinate_result_not_iconfluent` | Holes | finite-story | Live |
| `stable_inputs_seal_the_result` | Holes | ∀-general | — |
| `monadic_has_phantoms` | Holes | finite-story | — |
| `guardGluing_iff_iconfluent` | Gluing | ∀-general | — |
| `glues_is_not_iconfluent_renamed` | Gluing | finite-story | — |
| `guardGluingSeam_iff_segmented` | Gluing | ∀-general | — |
| `glue_eq_merged_fill` | Gluing | ∀-general | — |
| `coordination_forced` | Cost | ∀-general | — |
| `budget_cost_is_three` | Cost | finite-story | Live |
| `no_seam_frees_both` | Cost | finite-story | — |
| `projection_sound` | Choreo | ∀-general | — |
| `coordination_free_iff_iconfluent` | Choreo | ∀-general | — |
| `seam_coordination_free` | Choreo | ∀-general | — |
| `atMostOne_sync_cannot_be_dropped` | Choreo | finite-story | Live |
| `compatibility_axes_are_load_bearing` | Scheduling | finite-story | — |
| `SessionProfile.crossingProfile_comp` | Scheduling | ∀-general | — |
| `least_le_upper` | Scheduling | ∀-general | — |
| `composed_plan_uses_one_strategy` | Scheduling | ∀-general | — |
| `crossings_can_exceed_meetings` | Scheduling | finite-story | Live |
| `meetings_can_exceed_crossings` | Scheduling | finite-story | Live |
| `no_crossing_count_determines_least_meetings` | Scheduling | finite-story | Live |
| `no_least_meeting_count_determines_crossings` | Scheduling | finite-story | Live |
| `one_crossing_can_need_two_rounds` | Scheduling | finite-story | Live |
| `meetings_cannot_erase_currency` | Scheduling | finite-story | Live |
| `ra_linearizable_but_unsafe` | RALin | finite-story | Live |
| `ra_lin_preserves_inductive_invariants` | RALin | ∀-general | — |
| `maxctr_every_invariant_iconfluent` | RALin | ∀-general | — |
| `clash_dichotomy` | Ancestral | ∀-general | — |
| `lock_ancestral_confluent` | Ancestral | parametric | Live |
| `budget_defeats_every_faithful_merge` | Ancestral | ∀-general | — |
| `linked_segmented` | SeamAlgebra | ∀-general | — |
| `left_only_seam_iff` | SeamAlgebra | ∀-general | — |
| `antitone_forbids_enabling` | GatedEra | ∀-general | — |
| `ge_duel_resolved` | GatedEra | finite-story | Live |
| `fugue_runs_never_interleave` | Fugue | ∀-general | Live |
| `kernel_gate_agrees_gatedOps` | Gated | ∀-general | — |
| `applied_set_not_antitone` | ExecRefine | finite-story | Live |
| `resolve_same_sets` | Era | ∀-general | — |
| `final_view_immune` | Era | ∀-general | — |
| `encode_merge` | Era | ∀-general | — |
| `duelling_admins_resolved` | Era | finite-story | Live |
| `linearizeK_mem` | SeqKernel | parametric | — |
| `linearizeK_nodup` | SeqKernel | parametric | — |
| `linearizeK_ancestor_precedes` | SeqKernel | parametric | — |
| `linearizeK_sublist_emitAll` | SeqKernel | ∀-general | — |
| `necessity` | Necessity | ∀-general | — |
| `reachable_clash_refutes_cfcs` | Necessity | ∀-general | — |
| `iconfluent_implies_cfcs` | Necessity | ∀-general | — |
| `atMostOneBit_necessity` | Necessity | finite-story | Live |
| `orset_clash_joint` | CausalReach | finite-story | Live |
| `orset_clash_present` | CausalReach | finite-story | Live |
| `ew_clashL_unreachable` | CausalReach | finite-story | LatticeOnly |
| `orset_reachability_depends_on_remove_shape` | CausalReach | finite-story | — |
| `rem_without_add_not_a_cut` | CausalReach | finite-story | — |
| `atMostOne_joint` | CausalReach | finite-story | Live |
| `coordination_repairs_what_cf_breaks` | Necessity | finite-story | — |
| `fair_converges` | Liveness | ∀-general | — |
| `unfair_starvation` | Liveness | finite-story | — |
| `exec_traceEq` | Traces | ∀-general | — |
| `dependent_pair_reordering_changes_exec` | Traces | finite-story | — |
| `pncounter_nonneg_not_iconfluent_enum` | Nary | ∀-general | Live |
| `budget_segmented_enum` | Nary | parametric | — |
| `move_kernel_cfcs` | KernelCFCS | parametric | — |
| `absReplay_eq_of_exactMaterializes` | KernelCFCS | ∀-general | — |
| `acyclicity_cfcs_does_not_imply_view_stability` | KernelCFCS | finite-story | Live |
| `absReplay_ext_mem` | ExecRefine | ∀-general | — |
| `replay_encodeRequest` | ExecRefine | ∀-general | — |
| `miniReplay_eq_miniInterp` | Move | finite-story | — |
| `absReplay_matches_miniInterp` | Move | finite-story | — |
| `chainHits_decides` | ExecRefine | ∀-general | — |
| `decode_encode_id` | ExecRefine | ∀-general | — |
| `ormap_get_survives` | ORMap | ∀-general | — |
| `ormap_present_not_iconfluent` | ORMap | finite-story | Live |
| `ormap_doomed_update` | ORMap | finite-story | Live |
| `ormap_policy_divergence` | ORMap | finite-story | Live |
| `exec_perm` | Automata | ∀-general | — |
| `run_same_inputs` | Automata | ∀-general | — |
| `determinism_not_iconfluent` | Automata | finite-story | Live |
| `token_firings_segmented` | Automata | parametric | — |
| `wf_iconfluent` | Authority | parametric | — |
| `scope_le_root` | Authority | parametric | — |
| `authority_view_antitone` | Authority | parametric | — |
| `wf_unique_not_iconfluent` | Authority | finite-story | Unknown |
| `sole_admin_not_iconfluent` | Authority | finite-story | Live |
| `duelling_revocations_not_iconfluent` | Authority | finite-story | Live |
| `uniqueness_ceiling` | Ceiling | ∀-general | — |
| `rejected_sound` | Budget | ∀-general | — |
| `lower_bound_does_not_license_acceptance` | Budget | finite-story | — |
| `reblocking_escapes_the_floor` | Budget | finite-story | — |
| `opt_compose_ge_sum_opt` | CoordEffect | ∀-general | — |
| `optimum_compose_achieved` | CoordEffect | ∀-general | — |
| `pin_session_costs_exactly_one` | CoordEffect | finite-story | — |
| `eraReplay_same_sets` | EraKernel | ∀-general | — |
| `duel_response_words` | EraKernel | finite-story | Live |
| `closed_iconfluent` | Evidence | ∀-general | — |
| `divergent_futures_force_nonexact` | Evidence | ∀-general | — |
| `render_retracts_when_a_new_source_appears` | Evidence | finite-story | Unknown |
| `monotonicity_and_finality_are_independent` | Evidence | finite-story | — |
| `pin_escrow_starves` | Exits | finite-story | — |
| `repeated_merge_breaks_the_invariant` | Histories | finite-story | LatticeOnly |
| `base_accident_decides_the_invariant` | Histories | finite-story | LatticeOnly |
| `swap_never_converges` | Histories | parametric | LatticeOnly |
| `consumers_factor` | HonestRender | ∀-general | — |
| `no_honest_projection` | HonestRender | ∀-general | Unknown |
| `salience_is_not_enforceable` | HonestRender | ∀-general | — |
| `summaryFold_iff_joinHom` | JoinHom | ∀-general | — |
| `no_count_merge_without_provenance` | JoinHom | ∀-general | — |
| `count_summary_must_distinguish` | JoinHom | ∀-general | — |
| `monotone_pullback_can_fail` | JoinHom | finite-story | — |
| `iconfluentIn_join_iff` | MergeModel | ∀-general | — |
| `iconfluentIn_ancestral_iff` | MergeModel | ∀-general | — |
| `ancestral_not_idempotent` | MergeModel | finite-story | Live |
| `replay_not_observational` | MergeModel | finite-story | Live |
| `ctxQuot_coarsest_sufficient` | MinimalSummary | ∀-general | — |
| `ctxQuot_fold_answers` | MinimalSummary | ∀-general | — |
| `mem_ctxEquiv_iff` | MinimalSummary | ∀-general | — |
| `card_ctxEquiv_iff` | MinimalSummary | parametric | — |
| `threshold_quotient_not_cappedCount` | MinimalSummary | finite-story | — |
| `faithful_stepConfluent_iff_legalSerialization` | Recoverable | ∀-general | — |
| `comm_forces_symmetric_chooser` | Recoverable | ∀-general | — |
| `budget_boundary` | Recoverable | parametric | — |
| `crossings_cannot_see_the_difference` | Repair | finite-story | — |
| `no_free_arbitration` | Repair | parametric | — |
| `weakened_chain_is_not_the_original` | Repair | finite-story | — |
| `declaration_is_relative_to_the_reach` | ResultStatus | finite-story | Live |
| `sixth_cell_is_distinguishable` | ResultStatus | finite-story | — |
| `absence_outlives_exactness` | ResultStatus | finite-story | — |
| `segmented_iff_properColoring` | SeamColoring | ∀-general | — |
| `pin_synthesizeSeam_isSome` | SeamColoring | finite-story | — |
| `coloring_alone_does_not_segment` | SeamColoring | finite-story | Unknown |
| `Clash.not_iconfluent` | Tactics/Core | ∀-general | — |
| `findClash_none` | Tactics/Core | ∀-general | — |
| `core_iconfluent` | WeaveState | parametric | — |
| `weaveDocVerdict` (def) | WeaveState | finite-story | Live |
| `weaveDoc_segmented` | WeaveState | parametric | — |
| `merge_preserves_wellformed` | Wellformed | parametric | — |
| `merged_doc_violates_onePin_but_is_wellFormed` | Wellformed | finite-story | Live |
| `no_crash` | Wellformed | ∀-general | — |
| `delivery_future_is_not_state_indexed` | WorldFuture | finite-story | Live |
| `quiescence_is_a_sound_certificate` | WorldFuture | ∀-general | — |
| `no_sound_state_cert_accepts_openW` | WorldFuture | ∀-general | — |
| `coordination_necessary_and_costly` | Bounds | ∀-general | — |
| `zero_floor_does_not_imply_cfcs` | Bounds | parametric | Live |
| `fork_clash_charges_the_pair` | Bounds | ∀-general | Live |
| `ew_rejected_at_zero_over_unreachable_pair` | Bounds | finite-story | LatticeOnly |
| `resQuot_coarsest_sufficient` | CertificateScope | ∀-general | — |
| `deliveryKey_sufficient` | CertificateScope | ∀-general | — |
| `residual_is_not_a_join_congruence` | CertificateScope | finite-story | — |
| `closed_is_not_a_sound_delivery_certificate` | CertificateScope | finite-story | Live |
| `live_clique_forces_live_width` | CliqueLive | ∀-general | — |
| `live_clique_forces_scenario_floor` | CliqueLive | ∀-general | — |
| `triple_clash_forces_triangle` | CliqueLive | ∀-general | — |
| `the_two_floors_are_incomparable` | CliqueLive | parametric | — |
| `the_live_clique_number_determines_both` | CliqueLive | finite-story | — |
| `encodeEvidence_iso` | DerivedDocument | ∀-general | — |
| `deriveDoc_hom` | DerivedDocument | ∀-general | — |
| `tallyDoc_requires_evidence` | DerivedDocument | finite-story | — |
| `pipelines_merge_coordination_free` | DerivedDocument | ∀-general | — |
| `acyclic_pipelines_are_not_all_grounded` | DerivedDocument | parametric | — |
| `docStatus_encodeEvidence` | DerivedDocument | parametric | — |
| `era_finalisation_is_a_sound_certificate` | EraCertificate | parametric | — |
| `era_stops_before_quiescence` | EraCertificate | finite-story | — |
| `honest_announcement_resumes_the_finalised_view` | EraCertificate | ∀-general | — |
| `backdated_cut_rewrites_the_finalised_view` | EraCertificate | finite-story | Live |
| `an_event_born_finalised_rewrites_the_view` | EraCertificate | finite-story | Live |
| `liveScenario_optimum_eq_zero_iff_no_live_clash` | ForkGrade | ∀-general | — |
| `cfcs_iff_locallySafe_and_no_reachableClash` | ForkGrade | ∀-general | — |
| `cfcs_iff_locallySafe_and_all_finite_scenarios_zero` | ForkGrade | ∀-general | — |
| `the_disagreement_resolved` | ForkGrade | parametric | Live |
| `coherent_never_unavailable` | HistoryBase | ∀-general | — |
| `the_base_scope_repairs_the_state_keyed_certificate` | HistoryBase | finite-story | Live |
| `the_model_certifies_what_the_history_breaks` | HistoryBase | finite-story | LatticeOnly |
| `safety_is_selector_relative` | HistoryPolicy | finite-story | LatticeOnly |
| `recordDetermined_converges` | HistoryPolicy | ∀-general | — |
| `ccHistory_not_policyGenerated` | HistoryPolicy | ∀-general | LatticeOnly |
| `the_swap_is_order_dependence` | HistoryPolicy | finite-story | LatticeOnly |
| `the_self_base_policy_is_not_history_licensed` | HistoryPolicy | finite-story | LatticeOnly |
| `claim_sound` | LiveBudget | ∀-general | — |
| `ew_no_live_realization` | LiveBudget | finite-story | LatticeOnly |
| `carrier_global_rejection_is_not_live` | LiveBudget | ∀-general | LatticeOnly |
| `pathSegmented_iff_liveSegmented` | LiveBudget | ∀-general | — |
| `ClashChain.accused_are_connected` | LiveCost | ∀-general | Live |
| `cost_floor_becomes_live` | LiveCost | ∀-general | Live |
| `orset_tag_scoped_clash_is_live` | LiveCost | finite-story | Live |
| `ew_pair_refuses_a_live_accusation` | LiveCost | parametric | LatticeOnly |
| `clashBlocks_head_coReachable` | LiveSegmented | ∀-general | Live |
| `live_optimum_strictly_below_global_optimum` | LiveSegmented | finite-story | LatticeOnly |
| `the_third_domain_is_charged_for_an_unreachable_pair` | LiveSegmented | finite-story | LatticeOnly |
| `liveSegmented_iff_liveProperColoring` | LiveSegmented | ∀-general | — |
| `seam_row_dichotomy` | MenuTotality | ∀-general | — |
| `uniqueOn_singletons_clash_iff` | MenuTotality | ∀-general | — |
| `atMostOne_seam_row_refuted_at_every_finite_segment` | MenuTotality | ∀-general | — |
| `clique_forces_joint_crossings` | MenuTotality | ∀-general | Live |
| `the_clique_floor_is_invisible_to_the_block_calculus` | MenuTotality | parametric | — |
| `verdict_agree` | Preo/Classification | ∀-general | — |
| `seam_forces_clash` | Preo/Classification | ∀-general | — |
| `run_answer_of_perm` | Preo/Classification | ∀-general | — |
| `mergeability_comp` | Preo/Classification | ∀-general | — |
| `one_pin_escalates` | Preo/Demo | finite-story | Live |
| `loomDocFree` | Preo/Demo | parametric | — |
| `loomDoc2Free` | Preo/Demo | parametric | — |
| `elabPreoDecl` (def) | Preo/Elab | ∀-general | — |
| `proj_iconfluent` | Preo/Syntax | ∀-general | — |
| `statusOf_pending_escapable_by_sealing` | RenderProgress | ∀-general | — |
| `pending_progress_under_fair_delivery` | RenderProgress | ∀-general | Live |
| `a_truthful_spinner_may_wait_forever` | RenderProgress | finite-story | Live |
| `a_revoked_actor_gets_no_button` | RenderProgress | finite-story | — |
| `absence_is_not_unilaterally_merge_closed` | RenderProgress | finite-story | Unknown |
| `constant_widget_is_not_honest` | RenderProgress | ∀-general | — |
| `statusOf_sound6` | RenderSix | ∀-general | — |
| `five_handlers_cannot_separate` | RenderSix | ∀-general | — |
| `spinner_is_an_honest_five_status_renderer` | RenderSix | finite-story | — |
| `absence_is_the_more_defensible_badge` | RenderSix | parametric | Unknown |
| `menu_price_is_projection` | RepairMenu | ∀-general | — |
| `menu_delta_is_projection` | RepairMenu | ∀-general | — |
| `ceiling_seam_row_disagrees` | RepairMenu | finite-story | — |
| `duel_two_tags_one_repair` | RepairMenu | finite-story | — |
| `no_free_pin_arbitration` | RepairMenu | parametric | — |
| `seam_row_takes_all_three_constructors` | RepairMenu | finite-story | — |
| `no_text_merge_without_provenance` | TextSummary | ∀-general | Live |
| `linearize_not_joinHom` | TextSummary | ∀-general | LatticeOnly |
| `tombstones_are_load_bearing` | TextSummary | finite-story | Live |
| `no_gc_summary_sufficient` | TextSummary | ∀-general | Live |
| `text_architecture_is_forced` | TextSummary | parametric | — |
| `verdict_order_policy_invariant` | TextSummary | finite-story | Live |
| `keyed_cross_iconfluent` | Confluence | ∀-general | — |
| `SegVerdict.prependFree` | SeamAlgebra | ∀-general | — |
| `SegVerdict.selfSeam` | SeamAlgebra | ∀-general | — |
| `LoomDoc.one_wide.seam` | Preo/Demo | finite-story | Live |
| `KeyedDoc.fk.verdict` | Preo/Demo | finite-story | — |
| `TwinQuota.documentSeam` | Preo/Demo | finite-story | Live |
| `NestedSurface.documentSeam` | Preo/Demo | finite-story | Live |
| `NestedSurface.documentSeamFree6` | Preo/Demo | finite-story | Live |
| `weaveCoordViaAlgebra` | Preo/Demo | finite-story | Live |
| `weaveDocViaAlgebra` | Preo/Demo | finite-story | Live |

Ledger rows grow with the tree; reachability is derived from module docstrings
**and** from `CausalReach` theorems where those supersede older caution notes.
**Live** (selection): `pncounter`, `lww_cross_field`, `acyclicity`,
`view_not_stable`, `interleaving_anomaly`, `active_path`, the OR-Set/OR-Map
tag-scoped remove shapes, fork scenarios, proof-carrying paths, and the text
histories whose modules construct the operations from a common start. The
Seams `Live` tags follow that module's own partition narratives (an epoch-1
replica's claims gossiped across the boundary; a v0 record carried into a v1
store). **Unknown / CA-blocked** remains the conservative label where a module
gives a lattice witness or abstract renderer obstruction without settling an
operational history; Sequence and Authority's full id-uniqueness refutations
still depend on a collision-extraction premise even though their free-id
fragments are Live. **LatticeOnly** now has several proved inhabitants rather
than one: the element-wide OR-Set pair (`CausalReach`, `Bounds`, `LiveCost`,
`LiveBudget`), the carrier-global seam domain that `LiveSegmented` charges only
for that unreachable pair, history/base-policy examples explicitly shown not
run-realized or not history-licensed, and `TextSummary`'s pending-anchor state
that the shipping merge rejects. Tag-scoped OR-Set/OR-Map presence clashes do
not belong in this column.
Trust is not a column: every row is inside `#audit_floor`'s total gate, and
per-theorem axiom profiles are `#print axioms <name>` away.
