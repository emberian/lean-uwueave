# The map — every module, what it settles

The theorem-by-file guide. Each row names its keystone theorems so the claims
are checkable rather than vibes. Trust is enforced wholesale, not per-name:
`Uwueave/Audit.lean`'s `#audit_floor` walks every constant in the namespace
and fails the build on any axiom outside Lean's floor — a stray `sorry` or
`native_decide` anywhere in the tree goes red, zero-lag, no list to maintain.
(The ledger's audit column below is a reading aid; coverage is total by
construction.)

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
docstring does not settle it and this table refuses to guess. *Audit-pinned*
records whether `Uwueave/Audit.lean` pins the theorem's axiom footprint
(verified by grep, not memory); an unpinned row is named work, not hidden work.

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
| `Uwueave/Weave.lean` | A real weave library's feature list classified feature-by-feature — including the loom-specific theorem that a *shared* replicated active path is not a CRDT (`active_path_not_iconfluent`); make it per-user, which is better UX anyway. |
| `Uwueave/Exec.lean` | The executable kernel: the move-replay decision procedure, authored in Lean, exported to C, and linked into the Rust crate — now factored so `replay` is *by definition* decode → `absReplay` → encode, leaving no bytes-vs-decision gap to prove. Format v2 returns a per-op applied/skipped trace (`view_not_stable`, made visible to UIs). Sole remaining open, stated in its header: C-backend trust — the terminal TCB, named, not undone work. |
| `Uwueave/ExecRefine.lean` | The kernel's theorems: **`absReplay_acyclic`** — for a grounded base and *arbitrary* op arrays (any order, duplicates, junk indices), the replayed view has no cycle; fuel adequacy (`chainHits_decides`, from-scratch pigeonhole); the output codec round-trip capped by `decode_encode_id`. `miniInterp_acyclic`, generalized from the two-op toy to the real kernel. Wave 5 closed the rest: **`kernel_derived_view_sec`** (SEC's three clauses for `absReplay` itself) via **`absReplay_ext_mem`** (the kernel is a function of the op *set*), the miniInterp bridge (`miniReplay_eq_miniInterp` + `absReplay_matches_miniInterp` — same rule, two presentations, machine-checked), and the input codec (`replay_encodeRequest`). |
| `Uwueave/Audit.lean` | The trust gate, total: `#audit_floor` audits **every** constant in the `Uwueave` namespace against the axiom floor `{propext, Classical.choice, Quot.sound}` — `sorry` (`sorryAx`) and `native_decide` (`ofReduceBool`) are build failures everywhere, with a vacuity tripwire so the gate itself cannot pass on an empty walk. Replaced 113 per-theorem pins on 2026-08-10; the file's header carries the honest accounting. |
| `Uwueave/ORMap.lean` | The observed-remove map — documents are maps. Add-wins scoped (`ormap_get_survives`), the **doomed-update anomaly** as a theorem (a nested write concurrent with its key's removal survives the merge but is masked by the view), and the centerpiece: remove-wins and update-wins views provably *disagree on the same merged state* (`ormap_policy_divergence`) — the merge is policy-neutral; the choice is yours and visible. |
| `Uwueave/Automata.lean` | Replicated automata sorted by the same verdicts: semilattice-action runs converge as instances of the delta laws (`run_same_inputs`); commuting inputs may be replayed in any order (`exec_perm`, axiom-free — the seed of the Mazurkiewicz/Zielonka connection, cited not claimed); DFA determinism is the uniqueness ceiling (concrete clash), with LWW-arbitration vs accept-the-NFA priced as exits; token firing under escrow reads the segmented theorems as Petri nets. |
| `Uwueave/Authority.lean` | Local-first permissions: delegation chains as a grounded CRDT — issuing narrowed grants is coordination-free (`wf_iconfluent`), authority provably only narrows (`scope_le_root`), sole-admin escalates (the duelling-admins clash), revocation's late arrivals only ever *shrink* authority (`authority_view_antitone`) — the derived view's instability points fail-closed, the security dual of `view_not_stable` — and the per-id uniqueness premise is priced like Sequence's: `uniqueGrant_violation_extracts_collision` turns any violation into a hash-collision exhibit (collision resistance, not injectivity, is what a deployment supplies). |
| `Uwueave/SeqKernel.lean` | The sequence CRDT, **implemented** the house way: RGA-with-tombstones order decision authored in Lean, exported as `uwueave_seq_kernel` beside the move kernel. Proved: every visible element appears (`linearizeK_mem`), exactly once (`linearizeK_nodup` — groundedness alone), ancestors precede (`linearizeK_ancestor_precedes`), and deletes filter without reordering (`linearizeK_sublist_emitAll`). The brief's index-ordered hypothesis was refuted by the lane as vacuous-for-real-inputs and replaced by rank-groundedness. Non-claims: `interleaving_anomaly` still governs (reproduced through the shipping kernel in a Rust test); Fugue cited, not implemented. |
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
docstrings; `—` marks rows the axis does not apply to. Audit-pinned was
verified by grepping `Uwueave/Audit.lean`.

| Theorem | Module | Generality | Reachability | Audit-pinned |
|---|---|---|---|---|
| `escalation_witness` | Confluence | ∀-general | — | yes |
| `product_iconfluent` | Confluence | ∀-general | — | yes |
| `pi_iconfluent` | Confluence | ∀-general | — | yes |
| `gset_mem_iconfluent` | Catalog | ∀-general | — | no |
| `gset_monotone_iconfluent` | Catalog | ∀-general | — | no |
| `gset_atMostOne_not_iconfluent` | Catalog | finite-story | Live | total gate |
| `or_breaks_iconfluence` | Catalog | finite-story | Live | total gate |
| `pncounter_nonneg_not_iconfluent` | Catalog | finite-story | Live | yes |
| `lww_every_invariant_iconfluent` | Catalog | ∀-general | — | yes |
| `lww_cross_field_not_iconfluent` | Catalog | finite-story | Live | yes |
| `escrow_local_bound_iconfluent` | Catalog | parametric | — | yes |
| `acyclicity_not_iconfluent` | Acyclicity | finite-story | Live | yes |
| `grounded_iconfluent` | Acyclicity | parametric | — | yes |
| `grounded_acyclic` | Acyclicity | parametric | — | yes |
| `causal_dag_free` | Acyclicity | parametric | — | no |
| `derived_view_sec` | Move | ∀-general | — | yes |
| `view_not_stable` | Move | finite-story | Live | yes |
| `miniInterp_acyclic` | Move | finite-story | — | yes |
| `orset_present_survives` | ORSet | ∀-general | — | yes |
| `orset_present_not_iconfluent` | ORSet | finite-story | Live | total gate |
| `clset_present_iconfluent` | ORSet | ∀-general | — | yes |
| `vclock_leq_iff` | Causality | ∀-general | — | yes |
| `fork_evidence_iconfluent` | Causality | parametric | — | yes |
| `conflict_surfaces` | MVRegister | finite-story | — | yes |
| `resolution_is_a_write` | MVRegister | finite-story | — | yes |
| `undo_restores` | Undo | finite-story | — | yes |
| `undo_preserves_history` | Undo | finite-story | — | yes |
| `undo_conflicts_visibly` | Undo | finite-story | — | yes |
| `joinAll_perm` | Delta | ∀-general | — | yes |
| `joinAll_append_merge` | Delta | ∀-general | — | yes |
| `same_deltas_same_state` | Delta | ∀-general | — | yes |
| `wf_iconfluent` | Sequence | parametric | — | yes |
| `linearize_mem` | Sequence | parametric | — | yes |
| `linearize_anchor_precedes` | Sequence | parametric | — | yes |
| `linearize_count_one` | Sequence | parametric | — | yes |
| `wf_unique_anchor_not_iconfluent` | Sequence | finite-story | Unknown | yes |
| `interleaving_anomaly` | Sequence | finite-story | Live | yes |
| `iconfluent_iff_trivially_segmented` | Segmented | ∀-general | — | yes |
| `budget_not_iconfluent` | Segmented | finite-story | Live | total gate |
| `budget_segmented` | Segmented | parametric | — | yes |
| `Verdict.keyedClash` (def) | Spec | ∀-general | — | yes |
| `active_path_not_iconfluent` | Weave | finite-story | Live | yes |
| `absReplay_acyclic` | ExecRefine | ∀-general | — | yes |
| `kernel_derived_view_sec` | ExecRefine | ∀-general | — | total gate |
| `resolve_same_sets` | Era | ∀-general | — | total gate |
| `final_view_immune` | Era | ∀-general | — | total gate |
| `encode_merge` | Era | ∀-general | — | total gate |
| `duelling_admins_resolved` | Era | finite-story | Live | total gate |
| `linearizeK_mem` | SeqKernel | parametric | — | total gate |
| `linearizeK_nodup` | SeqKernel | parametric | — | total gate |
| `linearizeK_ancestor_precedes` | SeqKernel | parametric | — | total gate |
| `linearizeK_sublist_emitAll` | SeqKernel | ∀-general | — | total gate |
| `necessity` | Necessity | ∀-general | — | total gate |
| `reachable_clash_refutes_cfcs` | Necessity | ∀-general | — | total gate |
| `iconfluent_implies_cfcs` | Necessity | ∀-general | — | total gate |
| `atMostOneBit_necessity` | Necessity | finite-story | Live | total gate |
| `orset_clash_joint` | CausalReach | finite-story | Live | total gate |
| `orset_clash_present` | CausalReach | finite-story | Live | total gate |
| `ew_clashL_unreachable` | CausalReach | finite-story | LatticeOnly | total gate |
| `orset_reachability_depends_on_remove_shape` | CausalReach | finite-story | — | total gate |
| `rem_without_add_not_a_cut` | CausalReach | finite-story | — | total gate |
| `atMostOne_joint` | CausalReach | finite-story | Live | total gate |
| `coordination_repairs_what_cf_breaks` | Necessity | finite-story | — | total gate |
| `fair_converges` | Liveness | ∀-general | — | total gate |
| `unfair_starvation` | Liveness | finite-story | — | total gate |
| `exec_traceEq` | Traces | ∀-general | — | total gate |
| `dependent_pair_reordering_changes_exec` | Traces | finite-story | — | total gate |
| `pncounter_nonneg_not_iconfluent_enum` | Nary | ∀-general | Live | total gate |
| `budget_segmented_enum` | Nary | parametric | — | total gate |
| `move_kernel_cfcs` | KernelCFCS | parametric | — | total gate |
| `absReplay_eq_of_exactMaterializes` | KernelCFCS | ∀-general | — | total gate |
| `acyclicity_cfcs_does_not_imply_view_stability` | KernelCFCS | finite-story | Live | total gate |
| `absReplay_ext_mem` | ExecRefine | ∀-general | — | total gate |
| `replay_encodeRequest` | ExecRefine | ∀-general | — | total gate |
| `miniReplay_eq_miniInterp` | Move | finite-story | — | total gate |
| `absReplay_matches_miniInterp` | Move | finite-story | — | total gate |
| `chainHits_decides` | ExecRefine | ∀-general | — | yes |
| `decode_encode_id` | ExecRefine | ∀-general | — | yes |
| `ormap_get_survives` | ORMap | ∀-general | — | yes |
| `ormap_present_not_iconfluent` | ORMap | finite-story | Live | total gate |
| `ormap_doomed_update` | ORMap | finite-story | Live | yes |
| `ormap_policy_divergence` | ORMap | finite-story | Live | yes |
| `exec_perm` | Automata | ∀-general | — | yes |
| `run_same_inputs` | Automata | ∀-general | — | yes |
| `determinism_not_iconfluent` | Automata | finite-story | Live | yes |
| `token_firings_segmented` | Automata | parametric | — | yes |
| `wf_iconfluent` | Authority | parametric | — | yes |
| `scope_le_root` | Authority | parametric | — | yes |
| `authority_view_antitone` | Authority | parametric | — | yes |
| `wf_unique_not_iconfluent` | Authority | finite-story | Unknown | yes |
| `sole_admin_not_iconfluent` | Authority | finite-story | Live | yes |
| `duelling_revocations_not_iconfluent` | Authority | finite-story | Live | yes |
| `uniqueness_ceiling` | Ceiling | ∀-general | — | no |

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
cut theorem. **LatticeOnly** — none remaining for the OR-Set/OR-Map presence
clashes under the tag-scoped reading; element-wide remove-all-observed is still
unmodeled. Audit column "total gate" means covered by `#audit_floor`, not a
per-name pin. Not pinned as a separate ritual (named
work): `gset_mem_iconfluent`, `gset_monotone_iconfluent`, `causal_dag_free`,
and the new `Ceiling` names.
