# The map — every module, what it settles

The theorem-by-file guide. Each row names its keystone theorems so the claims
are checkable rather than vibes. Trust is enforced wholesale, not per-name:
`Uwueave/Audit.lean`'s `#audit_floor` walks every constant in the namespace
and fails the build on any axiom outside Lean's floor — a stray `sorry` or
`native_decide` anywhere in the tree goes red, zero-lag, no list to maintain.
(Coverage is total by construction; the [ledger](#keystone-ledger) below is a
reading aid, not a trust mechanism.)

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
| `Uwueave/Confluence.lean` | The judgement itself: `MergeState`, `IConfluent`, and `escalation_witness` — a failed invariant *always* yields a runnable two-replica repro. Plus the lifts that let a document's verdict be computed field-by-field. |
| `Uwueave/Catalog.lean` | The classic structures — G-Set, counters, LWW, escrow — with merge laws proved and keystone invariants classified. The pattern worth internalizing: ceilings, uniqueness, and mutual exclusion escalate; grow-only facts and per-replica quotas run free; a lone LWW register can never merge-break anything (`lww_every_invariant_iconfluent`) while two LWW registers can break any invariant *relating* them (`lww_cross_field_not_iconfluent`). |
| `Uwueave/Acyclicity.lean` | The DAG dichotomy of part 2 above: `acyclicity_not_iconfluent`, `grounded_iconfluent`, `grounded_acyclic` — packaged as `causal_dag_free`. |
| `Uwueave/Move.lean` | The op-log pattern's guarantee, once and generically (`derived_view_sec`), and its price on a concrete miniature (`view_not_stable`). |
| `Uwueave/ORSet.lean` | Removable sets, both honest ways: add-wins correctly scoped (`orset_present_survives`), unscoped presence refuted (`orset_present_not_iconfluent`), and the causal-length set free per-element (`clset_present_iconfluent`). |
| `Uwueave/Causality.lean` | Vector clocks: the clock order *is* the merge's order (`vclock_leq_iff`) — and fork evidence is forever (`fork_evidence_iconfluent`): a peer caught equivocating cannot gossip its way back to innocence. |
| `Uwueave/MVRegister.lean` | The multi-value register: keep the fork, show the fork. Concurrent writes both surface (`conflict_surfaces`); resolving is just another write (`resolution_is_a_write`). For a loom this isn't conflict *handling* — forks are the product. |
| `Uwueave/Undo.lean` | Multi-user undo/redo as ordinary writes at fresh clocks — the view restores (`undo_restores`), history is never rewritten (`undo_preserves_history`), and a concurrent undo conflicts *visibly* instead of losing silently. |
| `Uwueave/Delta.lean` | Why shipping deltas instead of states is sound: `joinAll` is exactly the least upper bound, and `same_deltas_same_state` — same delta-set, any order, any duplication, any batching, same replica. Twelve of its sixteen theorems use no axioms at all. |
| `Uwueave/Sequence.lean` | The text layer, with its boundary drawn precisely: membership and anchor-order hold from well-formedness alone; exactly-once needs an id-uniqueness premise *and we prove that premise isn't free* — nor is it hash injectivity (no finite hash has that): `uniqueAnchor_violation_extracts_collision` reads any violation as a constructive hash-collision exhibit, the computational-CR handoff; and the centerpiece is a concrete interleaving-anomaly witness — two runs merging to `[4,3,2,1]`, strictly alternated. No-interleaving is explicitly *not* claimed; that's what real sequence CRDTs (loro, Fugue) are for. |
| `Uwueave/Segmented.lean` | The gentlest verdict: some invariants that fail globally are free *within a seam* (`budget_segmented` vs `budget_not_iconfluent` — same invariant, both verdicts). Spend freely inside your quota; coordinate only to re-divide it. |
| `Uwueave/Spec.lean` | A composition DSL where verdicts carry their evidence: a schema's answer is either a proof or a counterexample transported up from the exact field that caused it. |
| `Uwueave/Seams.lean` | Seams two and three, so `SegmentedIConfluent` is a design recipe rather than one museum piece: the **epoch seam** (`epoch_sole_not_iconfluent` / `epoch_segmented` — duelling admins clash across the boundary, merge freely within it; plus the proved dead end `sole_unpinned_not_segmented`: the epoch *alone* fixes nothing) and the **schema-version seam** (`schema_tightening_not_iconfluent` / `schema_segmented` — a tightening migration is a flag day; `schema_widening_iconfluent` — widening needs no seam at all, the proof-shaped expand/contract asymmetry). Both packaged as `SegVerdict`s beside the budget. ⚠ Read §1 with `Era.lean`'s four corrections: the docstrings' original protocol reading (named-winner arbiter, per-replica epoch, coordinated boundary crossing) was guessed from the paper's abstract and corrected by the implementation — the carrier's theorems stand; the mechanism story is Era's. |
| `Uwueave/Weave.lean` | A real weave library's feature list classified feature-by-feature — including the loom-specific theorem that a *shared* replicated active path is not a CRDT (`active_path_not_iconfluent`); make it per-user, which is better UX anyway. |
| `Uwueave/Exec.lean` | The executable kernel: the move-replay decision procedure, authored in Lean, exported to C, and linked into the Rust crate — now factored so `replay` is *by definition* decode → `absReplay` → encode, leaving no bytes-vs-decision gap to prove. Format v2 returns a per-op applied/skipped trace (`view_not_stable`, made visible to UIs). Sole remaining open, stated in its header: C-backend trust — the terminal TCB, named, not undone work. |
| `Uwueave/ExecRefine.lean` | The kernel's theorems: **`absReplay_acyclic`** — for a grounded base and *arbitrary* op arrays (any order, duplicates, junk indices), the replayed view has no cycle; fuel adequacy (`chainHits_decides`, from-scratch pigeonhole); the output codec round-trip capped by `decode_encode_id`. `miniInterp_acyclic`, generalized from the two-op toy to the real kernel. Wave 5 closed the rest: **`kernel_derived_view_sec`** (SEC's three clauses for `absReplay` itself) via **`absReplay_ext_mem`** (the kernel is a function of the op *set*), the miniInterp bridge (`miniReplay_eq_miniInterp` + `absReplay_matches_miniInterp` — same rule, two presentations, machine-checked), and the input codec (`replay_encodeRequest`). |
| `Uwueave/Audit.lean` | The trust gate, total: `#audit_floor` audits **every** constant in the `Uwueave` namespace against the axiom floor `{propext, Classical.choice, Quot.sound}` — `sorry` (`sorryAx`) and `native_decide` (`ofReduceBool`) are build failures everywhere, with a vacuity tripwire so the gate itself cannot pass on an empty walk. Replaced 113 per-theorem pins on 2026-08-10; the file's header carries the honest accounting. |
| `Uwueave/ORMap.lean` | The observed-remove map — documents are maps. Add-wins scoped (`ormap_get_survives`), the **doomed-update anomaly** as a theorem (a nested write concurrent with its key's removal survives the merge but is masked by the view), and the centerpiece: remove-wins and update-wins views provably *disagree on the same merged state* (`ormap_policy_divergence`) — the merge is policy-neutral; the choice is yours and visible. |
| `Uwueave/Automata.lean` | Replicated automata sorted by the same verdicts: semilattice-action runs converge as instances of the delta laws (`run_same_inputs`); commuting inputs may be replayed in any order (`exec_perm`, axiom-free — the seed of the Mazurkiewicz/Zielonka connection, cited not claimed); DFA determinism is the uniqueness ceiling (concrete clash), with LWW-arbitration vs accept-the-NFA priced as exits; token firing under escrow reads the segmented theorems as Petri nets. |
| `Uwueave/Authority.lean` | Local-first permissions: delegation chains as a grounded CRDT — issuing narrowed grants is coordination-free (`wf_iconfluent`), authority provably only narrows (`scope_le_root`), sole-admin escalates (the duelling-admins clash), revocation's late arrivals only ever *shrink* authority (`authority_view_antitone`) — the derived view's instability points fail-closed, the security dual of `view_not_stable` — and the per-id uniqueness premise is priced like Sequence's: `uniqueGrant_violation_extracts_collision` turns any violation into a hash-collision exhibit (collision resistance, not injectivity, is what a deployment supplies). |
| `Uwueave/SeqKernel.lean` | The sequence CRDT, **implemented** the house way: RGA-with-tombstones order decision authored in Lean, exported as `uwueave_seq_kernel` beside the move kernel. Proved: every visible element appears (`linearizeK_mem`), exactly once (`linearizeK_nodup` — groundedness alone), ancestors precede (`linearizeK_ancestor_precedes`), and deletes filter without reordering (`linearizeK_sublist_emitAll`). The brief's index-ordered hypothesis was refuted by the lane as vacuous-for-real-inputs and replaced by rank-groundedness. Non-claims: `interleaving_anomaly` still governs (reproduced through the shipping kernel in a Rust test); Fugue cited, not implemented. |
| `Uwueave/Holes.lean` | **The hole calculus** — replicated computation with multi-candidate results. Worlds carry correlations (the set monad's phantom candidates proved both directions on one witness), and the headline `evalSet_hom` needs *no hypothesis on the program*: compute-then-merge = merge-then-compute, unconditionally — images are free; the whole price sits in wanting one answer (`determinate_result_not_iconfluent`, the ceiling pulled back through evaluation). `stable_inputs_seal_the_result` transports input stability to result stability along the hom in one rewrite; provenance rides by type into `MVReg`. ⚠ Read the header's three retractions: the hom holds because *images* distribute over unions, not because machinery "transfers unchanged" (monotone ≠ join-preserving — see `JoinHom.lean`); a monotone expression's holes fill by gossip **only** under a finite closed scope with fair complete delivery (Power–Koutris–Hellerstein 2025); and a freeze, a causal cut and an arbiter cut play one role with three different evidentiary meanings. Prior art: Hazel-style holes over replicated collaborative editing is Grove (POPL 2025); a generic partial-value calculus is λ∨ (Rioux–Zdancewic 2025). |
| `Uwueave/Gluing.lean` | **`guardGluing_iff_iconfluent`** — named four times in a sibling repo's design study and never built there (its kernel forbade partial cones). Guarded holes with delta-shaped fills; divergent fills glue iff the guard is I-confluent, under `Spanning` — and `stampedHole` proves the iff is *not a renaming* (`Glues` and `IConfluent` come apart exactly when `Spanning` fails). Consequences: the sheaf-shaped `glue_eq_merged_fill`, a hole verdict `Spec.Verdict` cannot express, partially-glueable holes via seams, and one-shot *sharpened*: gluing licenses local double-fill. |
| `Uwueave/Cost.lean` | **Coordination frequency is real and has a floor**: `crossings` counts σ-changes along a workload, and `coordination_forced` shows clash blocks in the *spec* force the count for every seam in every universe. Tight instance: three budget re-divisions cost exactly 3. Self-correction included: linking seams did **not** lower the document's floor — it made the obvious seam optimal. The undercounting verdict is proved and stated as the measure's domain of validity. |
| `Uwueave/Choreo.lean` | **The verdict moves onto the program**: choreographies over replica-owned CRDT state, endpoint projection with `projection_sound` as pointwise state equality (no bisimulation — the channel *is* the lattice), and `coordination_free_iff_iconfluent`, iff-shaped with neither direction `Iff.rfl`. The seam refinement the in-house prior art never had: `seam_coordination_free` — barriers exactly at σ-changes, free within fibers, no global `IConfluent` hypothesis anywhere. ⚠ Retracted with the file: the choreography × CRDT junction is **not** empty — Kuhn–Melgratti–Tuosto (ECOOP 2023) project swarm protocols to local-first peer machines with progress under unavailability. The defensible claim is narrower: an I-confluence-derived coordination verdict **plus** a seam refinement over it is what we could not find elsewhere. |
| `Uwueave/RALin.lean` | **Correctness ≠ safety**, against Sal (arXiv:2603.27202): `ra_linearizable_but_unsafe` — Sal's own Table-2 PN-counter, RA-linearizable for any fork and branches, every branch legal at every prefix, and the merge overdraws. Converse: the max-counter loses updates, making *every* invariant I-confluent while failing RA-lin — safety bought by data loss. `quadrants` inhabits all four cells; `ra_lin_preserves_inductive_invariants` (axiom-free) is what RA-lin *does* buy; `guarding_moves_the_bug` shows the verdicts entangled through op preconditions. |
| `Uwueave/Ancestral.lean` | **The LCA question, answered: incomparable.** Two-way I-confluence can be bought by a join that drops a committed op (effect-faithfulness is the honesty condition); mutual exclusion under hand-off is free with an ancestor (`lock_ancestral_confluent`) and provably beyond every two-way join; the bounded counter is beyond every honest merge (`budget_defeats_every_faithful_merge`) — escrow stands. `clash_dichotomy` names the rule: **resurrection** clashes an LCA repairs; **accumulation** clashes nothing repairs. |
| `Uwueave/SeamAlgebra.lean` | The calculus segmented confluence lacked: product/pi/and lifts hold; refinement REFUTED (a conjunctive observation over grow-only fields is not a seam); free-riding refuted with stability pinned necessary and sufficient; the dividing line as an iff (`left_only_seam_iff`); and the prize, `linked_segmented` — two seams collapse into one exactly where well-formedness makes one seam a function of the other. |
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

## Keystone ledger

The two axes from the paragraph above, per marquee keystone. Names are as cited
in the rows above (namespace prefix omitted where the module is the row's).
Reachability is only for negative results — clashes and anomaly exhibits — and
each `Live` / `LatticeOnly` tag cites nothing beyond the named module's own
docstrings (upgraded by `CausalReach` theorems where those supersede them);
`—` marks rows the axis does not apply to. Every row is covered by
`#audit_floor`'s total gate — there is no per-row trust column to read. The
table currently holds 126 rows:

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
| `kernel_gate_agrees_gatedOps` | Exec | ∀-general | — |
| `applied_set_not_antitone` | Exec | finite-story | Live |
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

Ledger rows grow with the tree; reachability is derived from module docstrings
**and** from `CausalReach` theorems where those supersede older caution notes.
**Live** (selection): `pncounter`, `lww_cross_field`, `acyclicity`,
`view_not_stable`, `interleaving_anomaly`, `active_path`, `ormap_doomed_update`,
`ormap_policy_divergence`, `determinism`, `sole_admin`, `duelling_revocations`,
**and** (post–JOB 2) `orset_present_not_iconfluent` / `ormap_present_not_iconfluent`
under tag-scoped rem-after-add (`CausalReach.orset_clash_joint`), plus
at-most-one / mutex / budget concurrent-op shapes (`atMostOne_joint`,
`budget_joint`). **Unknown / CA-blocked** — Sequence and Authority dup-pair
refutations: free-id fragments are Live (`sequence_dup_frag_joint`); full
uniqueness under content addressing is a collision-extraction premise, not a
cut theorem. **LatticeOnly** — the `CausalReach` element-wide row
(`ew_clashL_unreachable`) is the axis's one deliberate inhabitant: it *proves*
the lattice pair unreachable under that protocol reading; none remain for the
OR-Set/OR-Map presence clashes under the tag-scoped reading. The Seams `Live`
tags follow that module's own partition narratives (an epoch-1 replica's
claims gossiped across the boundary; a v0 record carried into a v1 store).
Trust is not a column: every row is inside `#audit_floor`'s total gate, and
per-theorem axiom profiles are `#print axioms <name>` away.
