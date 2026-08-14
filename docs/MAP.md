# The map — the classified modules, and what each settles

The theorem-by-file guide. Each row names its keystone theorems so the claims
are checkable rather than vibes. Trust is enforced wholesale, not per-name:
`Uwueave/TrustFloor.lean` defines the one reusable axiom policy and the
`#audit_floor` / `#audit_floor_prefix` commands; `Uwueave/Audit.lean` applies
that policy to every constant in this namespace. A stray `sorry` or
`native_decide` anywhere in the tree goes red, zero-lag, no list to maintain.
(That total coverage is a fact about the **gate**, not about this table; the
[ledger](#keystone-ledger) below is a reading aid, not a trust mechanism.)

✅ **Coverage, 2026-08-13.** The file table below has one row for each of the
185 Lean module files under `Uwueave/`, including the nested `Preo` and
`Tactics` modules. This is a documentation invariant rather than a trust
mechanism: the root aggregator and `#gate_covers_root` remain the authorities
for transitive gate coverage. Re-derive the table's coverage instead of
trusting this prose after adding or moving a module:

The Wave 30 gate built 186 jobs, found 162 direct root modules below the gated
closure, and audited 25,747 `Uwueave` constants. Those are mechanical
snapshot counts, not a semantic-adequacy claim.

```sh
python3 - <<'PY'
from pathlib import Path
import re
source = re.split(
    r"^## " + r"Keystone ledger$", Path("docs/MAP.md").read_text(),
    maxsplit=1, flags=re.MULTILINE)[0]
mapped = set(re.findall(r"^\| `([^`]+\.lean)` \|", source, re.MULTILINE))
present = {str(path) for path in Path("Uwueave").rglob("*.lean")}
assert mapped == present, (sorted(present - mapped), sorted(mapped - present))
assert len(mapped) == 185
PY
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
| `Uwueave/Confluence.lean` | The judgement itself: `MergeState`, `IConfluent`, and `escalation_witness` — a failed invariant *always* yields a runnable two-replica repro. Plus the product, Pi, and keyed-cross transports that let document verdicts be computed structurally without pretending separate field proofs establish a relation. Wave 24's small normalization kit (`leq_iff_merge_eq`, absorption, and the three shared-input join equations) centralizes the semilattice algebra used by `ClashGraph` and `CliqueLive`; it deliberately does not make associativity/commutativity global simp rules. |
| `Uwueave/Catalog.lean` | The classic structures — G-Set, counters, LWW, escrow — with merge laws proved and keystone invariants classified. The pattern worth internalizing: ceilings, uniqueness, and mutual exclusion escalate; grow-only facts and per-replica quotas run free; a lone LWW register can never merge-break anything (`lww_every_invariant_iconfluent`) while two LWW registers can break any invariant *relating* them (`lww_cross_field_not_iconfluent`). |
| `Uwueave/Acyclicity.lean` | The DAG dichotomy of part 2 above: `acyclicity_not_iconfluent`, `grounded_iconfluent`, `grounded_acyclic` — packaged as `causal_dag_free`. |
| `Uwueave/Move.lean` | The op-log pattern's guarantee, once and generically (`derived_view_sec`), and its price on a concrete miniature (`view_not_stable`). |
| `Uwueave/ORSet.lean` | Removable sets, both honest ways: add-wins correctly scoped (`orset_present_survives`), unscoped presence refuted (`orset_present_not_iconfluent`), and the causal-length set free per-element (`clset_present_iconfluent`). §3 is the module's other half and the reason the refutation is not the whole story: the **remove-shape dichotomy**. The clash needs a replica to tombstone one tag while keeping another, which the element-wide "remove all observed tags" op (`removeAll`) cannot do — so on *that* protocol class the same invariant is I-confluent (`orset_ew_present_iconfluent`), and `CausalReach.lean` §6 settles it causally (`ew_clashL_unreachable`, `orset_reachability_depends_on_remove_shape`). Verdict follows the remove, not the set. |
| `Uwueave/Causality.lean` | Vector clocks: the clock order *is* the merge's order (`vclock_leq_iff`) — and fork evidence is forever (`fork_evidence_iconfluent`): a peer caught equivocating cannot gossip its way back to innocence. |
| `Uwueave/MVRegister.lean` | The multi-value register: keep the fork, show the fork. Concurrent writes both surface (`conflict_surfaces`); resolving is just another write (`resolution_is_a_write`). For a loom this isn't conflict *handling* — forks are the product. |
| `Uwueave/Undo.lean` | Multi-user undo/redo as ordinary writes at fresh clocks — the view restores (`undo_restores`), history is never rewritten (`undo_preserves_history`), and a concurrent undo conflicts *visibly* instead of losing silently. |
| `Uwueave/Delta.lean` | Why shipping deltas instead of states is sound: `joinAll` is exactly the least upper bound, and `same_deltas_same_state` — same delta-set, any order, any duplication, any batching, same replica. Twelve of its sixteen theorems use no axioms at all. |
| `Uwueave/Sequence.lean` | The text layer, with its boundary drawn precisely: membership and anchor-order hold from well-formedness alone; exactly-once needs an id-uniqueness premise *and we prove that premise isn't free* — nor is it hash injectivity (no finite hash has that): `uniqueAnchor_violation_extracts_collision` reads any violation as a constructive hash-collision exhibit, the computational-CR handoff; and the centerpiece is a concrete interleaving-anomaly witness — two runs merging to `[4,3,2,1]`, strictly alternated. No-interleaving is explicitly *not* claimed; that's what real sequence CRDTs (loro, Fugue) are for. |
| `Uwueave/ListProofs.lean` | Proof-only structural lemmas shared by `Sequence`, `SeqKernel`, and `Fugue`: `flatMap_nodup_of_nodup_of_pairwise_disjoint`, its count-at-most-one corollary, and `sublist_flatMap_of_mem`. They factor the generic list induction away from tree, anchor, rank, and fuel arguments; fixtures pin the abstraction, and no executable traversal or semantic judgement changes. |
| `Uwueave/Segmented.lean` | The gentlest verdict: some invariants that fail globally are free *within a seam* (`budget_segmented` vs `budget_not_iconfluent` — same invariant, both verdicts). Spend freely inside your quota; coordinate only to re-divide it. |
| `Uwueave/Spec.lean` | A composition DSL where verdicts carry their evidence: a schema's answer is either a proof or a counterexample transported up from the exact field that caused it. |
| `Uwueave/Seams.lean` | Seams two and three, so `SegmentedIConfluent` is a design recipe rather than one museum piece: the **epoch seam** (`epoch_sole_not_iconfluent` / `epoch_segmented` — duelling admins clash across the boundary, merge freely within it; plus the proved dead end `sole_unpinned_not_segmented`: the epoch *alone* fixes nothing) and the **schema-version seam** (`schema_tightening_not_iconfluent` / `schema_segmented` — a tightening migration is a flag day; `schema_widening_iconfluent` — widening needs no seam at all, the proof-shaped expand/contract asymmetry). Both packaged as `SegVerdict`s beside the budget. ⚠ Read §1 with `Era.lean`'s four corrections: the docstrings' original protocol reading (named-winner arbiter, per-replica epoch, coordinated boundary crossing) was guessed from the paper's abstract and corrected by the implementation — the carrier's theorems stand; the mechanism story is Era's. |
| `Uwueave/Weave.lean` | A real weave library's feature list classified feature-by-feature — including the loom-specific theorem that a *shared* replicated active path is not a CRDT (`active_path_not_iconfluent`); make it per-user, which is better UX anyway. |
| `Uwueave/Exec.lean` | The executable kernel: the move-replay decision procedure, authored in Lean, exported to C, and linked into the Rust crate — factored so `replay` is *by definition* decode → `gatedReplayFull` → encode, leaving no bytes-vs-decision gap to prove. **Format v3**, and v2 requests no longer parse: a magic word makes the flag day loud, and bytes without it get an *empty* response rather than a guess. v3 gives the request an authority substrate, so the op gate `Uwueave/Gated.lean` models runs *inside the shipping kernel*, and the per-op trace carries four codes — applied, skipped (cycle rule), skipped (invalid index), and `3` = skipped (unauthorised) — which is what makes `view_not_stable`'s priced anomaly visible to UIs. The former Rust byte marshaller is gone: typed lanes cross the FFI and `encodeRequestKernel_eq` proves the Lean export calls the canonical encoder. [`docs/TRUST.md`](TRUST.md) Ledger 2 and its [machine manifest](trust/ledger2-v1.json) preserve ten named execution boundaries plus the separately paid Lean-owned request encoding and fail-closed build-freshness controls. CakeML is the existence proof for the codegen half; CompCert covers exactly one row, the C compiler, and does **not** reach Lean's IR→C step. |
| `Uwueave/ExecRefine.lean` | The kernel's theorems: **`absReplay_acyclic`** — for a grounded base and *arbitrary* op arrays (any order, duplicates, junk indices), the replayed view has no cycle; fuel adequacy (`chainHits_decides`, from-scratch pigeonhole); the output codec round-trip capped by `decode_encode_id`. `miniInterp_acyclic`, generalized from the two-op toy to the real kernel. Wave 5 closed the rest: **`kernel_derived_view_sec`** (SEC's three clauses for `absReplay` itself) via **`absReplay_ext_mem`** (the kernel is a function of the op *set*), the miniInterp bridge (`miniReplay_eq_miniInterp` + `absReplay_matches_miniInterp` — same rule, two presentations, machine-checked), and the input codec (`replay_encodeRequest`). Wave 23 factors the repeated byte proofs into carrier-polymorphic `WordCodec.foldlPushWord_size` / `_get_lt` / `_get` and width-polymorphic `FixedWidth.flatMap_length` / `_getElem?_eq`; view, request, and ERA codecs retain their domain-specific theorem names as wrappers. |
| `Uwueave/TrustFloor.lean` | The reusable trust-floor implementation: one `allowedAxioms`, `offFloor`, `constantsUnder`, bounded `firstViolations`, Lean-parser-backed `directImports`, and nonvacuous `#audit_floor_prefix` for downstream namespaces. It also owns the compatibility `#audit_floor` command; this module defines policy and mechanics, while `Audit.lean` chooses the repository-wide roots and executes the gates. |
| `Uwueave/Audit.lean` | The repository-wide trust-gate invocation, total: `#audit_floor` audits **every** constant in the `Uwueave` namespace against the policy in `TrustFloor`, and `#gate_covers_root` checks that every direct root import is below the audited closure. `sorry` (`sorryAx`) and `native_decide` (`ofReduceBool`) are build failures everywhere, with vacuity tripwires for both namespace and root coverage. Replaced 113 per-theorem pins on 2026-08-10; the file's header carries the honest accounting. |
| `Uwueave/ORMap.lean` | The observed-remove map — documents are maps. Add-wins scoped (`ormap_get_survives`), the **doomed-update anomaly** as a theorem (a nested write concurrent with its key's removal survives the merge but is masked by the view), and the centerpiece: remove-wins and update-wins views provably *disagree on the same merged state* (`ormap_policy_divergence`) — the merge is policy-neutral; the choice is yours and visible. |
| `Uwueave/Automata.lean` | Replicated automata sorted by the same verdicts: semilattice-action runs converge as instances of the delta laws (`run_same_inputs`); commuting inputs may be replayed in any order (`exec_perm`, axiom-free — the seed of the Mazurkiewicz/Zielonka connection, cited not claimed); DFA determinism is the uniqueness ceiling (concrete clash), with LWW-arbitration vs accept-the-NFA priced as exits; token firing under escrow reads the segmented theorems as Petri nets. |
| `Uwueave/Authority.lean` | Local-first permissions: delegation chains as a grounded CRDT — issuing narrowed grants is coordination-free (`wf_iconfluent`), authority provably only narrows (`scope_le_root`), sole-admin escalates (the duelling-admins clash), revocation's late arrivals only ever *shrink* authority (`authority_view_antitone`) — the derived view's instability points fail-closed, the security dual of `view_not_stable` — and the per-id uniqueness premise is priced like Sequence's: `uniqueGrant_violation_extracts_collision` turns any violation into a hash-collision exhibit (collision resistance, not injectivity, is what a deployment supplies). |
| `Uwueave/SeqKernel.lean` | The sequence CRDT, **implemented** the house way: RGA-with-tombstones order decision authored in Lean, exported as `uwueave_seq_kernel` beside the move kernel. Proved: every visible element appears (`linearizeK_mem`), exactly once (`linearizeK_nodup` — groundedness alone), ancestors precede (`linearizeK_ancestor_precedes`), and deletes filter without reordering (`linearizeK_sublist_emitAll`). The brief's index-ordered hypothesis was refuted by the lane as vacuous-for-real-inputs and replaced by rank-groundedness. Non-claims: `interleaving_anomaly` still governs (reproduced through the shipping kernel in a Rust test); Fugue cited, not implemented. |
| `Uwueave/Holes.lean` | **The hole calculus** — replicated computation with multi-candidate results. Worlds carry correlations (the set monad's phantom candidates proved both directions on one witness), and the headline `evalSet_hom` needs *no hypothesis on the program*: compute-then-merge = merge-then-compute, unconditionally — images are free; the whole price sits in wanting one answer (`determinate_result_not_iconfluent`, the ceiling pulled back through evaluation). Wave 26 adds `Positioned` and `evalPositions`: exact value/source/static-position membership, a union homomorphism, and an empty-position refusal. These are typed attributions supplied by an adapter, not causal provenance or authentication. `stable_inputs_seal_the_result` transports input stability to result stability along the hom in one rewrite. ⚠ Read the header's three retractions: the hom holds because *images* distribute over unions, not because machinery "transfers unchanged" (monotone ≠ join-preserving — see `JoinHom.lean`); a monotone expression's holes fill by gossip **only** under a finite closed scope with fair complete delivery (Power–Koutris–Hellerstein 2025); and a freeze, a causal cut and an arbiter cut play one role with three different evidentiary meanings. Prior art: Hazel-style holes over replicated collaborative editing is Grove (POPL 2025); a generic partial-value calculus is λ∨ (Rioux–Zdancewic 2025). |
| `Uwueave/Gluing.lean` | **`guardGluing_iff_iconfluent`** — named four times in a sibling repo's design study and never built there (its kernel forbade partial cones). Guarded holes with delta-shaped fills; divergent fills glue iff the guard is I-confluent, under `Spanning` — and `stampedHole` proves the iff is *not a renaming* — `Spanning` is **not removable** (`stampedHole_glues` + `excl_not_iconfluent`: a non-spanning hole that glues while its guard clashes), so `Glues` and `IConfluent` are genuinely different predicates. ⚠ Read the direction: `Spanning` is *sufficient*, not proved necessary — the ⟸ half of `guardGluing_iff_iconfluent` never touches it. `oneShotHole_partially_glues` gives the exact one-shot verdict: globally it fails, within the owner seam it glues, and every valid such seam must separate distinct singleton owners; conversely `anchorHole_admits_double_fill` proves gluing alone does not impose one-shot admission. |
| `Uwueave/Cost.lean` | **Coordination frequency is real and has a floor**: `crossings` counts σ-changes along a workload, and `coordination_forced` shows clash blocks in the *spec* force the count for every seam in every universe. Tight instance: three budget re-divisions cost exactly 3. Self-correction included: linking seams did **not** lower the document's floor — it made the obvious seam optimal. The undercounting verdict is proved and stated as the measure's domain of validity. |
| `Uwueave/Choreo.lean` | **The verdict moves onto the program**: choreographies over replica-owned CRDT state, endpoint projection with `projection_sound` as pointwise state equality (no bisimulation — the channel *is* the lattice), and `coordination_free_iff_iconfluent`, iff-shaped with neither direction `Iff.rfl`. The seam refinement the in-house prior art never had: `seam_coordination_free` — barriers exactly at σ-changes, free within fibers, no global `IConfluent` hypothesis anywhere. ⚠ Retracted with the file: the choreography × CRDT junction is **not** empty — Kuhn–Melgratti–Tuosto (ECOOP 2023) project swarm protocols to local-first peer machines with progress under unavailability. The defensible claim is narrower: an I-confluence-derived coordination verdict **plus** a seam refinement over it is what we could not find elsewhere. |
| `Uwueave/Scheduling.lean` | **Crossings are effects; meetings discharge coeffects.** `Session.comp` adds crossing counts while reindexing proof-carrying obligation origins, and `SessionProfile.comp` retains one shared strategy until a `ProfilePlan` chooses it. `ProfileUpperBound` accepts five pointwise limits only through one real plan; `ProfileUpperBound.comp` soundly appends plans, while `meeting_floor_does_not_entail_profile_acceptance` proves a peer floor cannot construct that evidence. The exact 2-crossings→1-meeting, 0→1, and 1→2 examples still refute every scalar conversion. No `Budget.ForcedFloor`→meeting-floor or unannotated `Choreo` extraction is claimed. |
| `Uwueave/ScheduleSynthesis.lean` | Proof-carrying finite schedule search over a supplied catalog of real `Plan`s. `SearchResult.bound_exists_of_isFound` recovers a member and full five-currency `ProfileUpperBound`; `exhaustive_of_not_isFound` returns a named-currency violation for every candidate. `selectLeast` is least only under an explicit `OrderPolicy` and catalog order. `Preo.Planning` now supplies the first bounded generator: every canonical sublist of one duplicate-free, pre-capped authored action universe, filtered by actual schedule coverage. Arbitrary schedules outside that finite universe remain intentionally unenumerated. |
| `Uwueave/RALin.lean` | **Correctness ≠ safety**, against Sal (arXiv:2603.27202): `ra_linearizable_but_unsafe` — Sal's own Table-2 PN-counter, RA-linearizable for any fork and branches, every branch legal at every prefix, and the merge overdraws. Converse: the max-counter loses updates, making *every* invariant I-confluent while failing RA-lin — safety bought by data loss. `quadrants` inhabits all four cells; `ra_lin_preserves_inductive_invariants` (axiom-free) is what RA-lin *does* buy; `guarding_moves_the_bug` shows the verdicts entangled through op preconditions. |
| `Uwueave/Ancestral.lean` | **The LCA question, answered: incomparable.** Two-way I-confluence can be bought by a join that drops a committed op (effect-faithfulness is the honesty condition); mutual exclusion under hand-off is free with an ancestor (`lock_ancestral_confluent`) and provably beyond every two-way join; the bounded counter is beyond every honest merge (`budget_defeats_every_faithful_merge`) — escrow stands. `clash_dichotomy` names the rule: **resurrection** clashes an LCA repairs; **accumulation** clashes nothing repairs. |
| `Uwueave/SeamAlgebra.lean` | The calculus segmented confluence lacked: product/pi/and lifts hold; refinement REFUTED (a conjunctive observation over grow-only fields is not a seam); free-riding refuted with stability pinned necessary and sufficient; the dividing line as an iff (`left_only_seam_iff`); and the prize, `linked_segmented` — two seams collapse into one exactly where well-formedness makes one seam a function of the other. `selfSeam` turns an already-certified clash into the conservative identity seam, while `prependFree` supplies the conjunction-order mirror needed to reconstruct the hand weave seam. |
| `Uwueave/GatedEra.lean` | Arbitrated authority composed with the op gate: `ge_deterministic`, `ge_duel_resolved` (the survivor's op stands where fail-closed denied both), `ge_finalised_stable`. The finding: `antitone_forbids_enabling` — any permission rule antitone in event growth makes promotion impossible. Fail-closed guarantees shrinkage; arbitration guarantees agreement; the trade is a theorem. |
| `Uwueave/Tactics.lean` | Heavy demonstrations, adversarial fixtures, and the proof-idiom measurements for the production `verdict` tactic exported by `Tactics/Verdict`. The examples verify five kernel-checked routes, loud clash-bearing failures, and that "no clash found" remains explicitly **NO VERDICT**; the idiom kit retains the measured ~161→25-line shrink list beside a measured not-replaceable list. Runtime and downstream users may import the split verdict layer without elaborating this fixture corpus. |
| `Uwueave/Era.lean` | The ERA protocol core, **implemented** from the paper (cuts, epochs, the four-op grammar, authorised execution, sorted-insert canonicalisation): delivery-independence by the set-function route (`resolve_same_sets`), rollback-immunity of the finalised prefix (`final_view_immune`), and the payoff — `duelling_admins_resolved`: one deterministic survivor at every replica, where `Authority.duelling_admins_annihilate` killed both. Corrects four guesses in `Seams.lean` (headline: the arbiter never names a winner, only orders events — and nobody coordinates; the epoch boundary is a trusted announcement priced in rollback). |
| `Uwueave/Necessity.lean` | **Bailis necessity, modeled** (delivered by grok via `GROKJOB.md`): an execution model where coordination-freedom is definitional (`Impl.tryApply` sees local state only), and the theorem the library previously only cited — a *reachable* clash refutes coordination-free-convergent-safety (`necessity`, axiom-free core), with sufficiency back (`iconfluent_implies_cfcs`). Satisfiable (`gset_true_is_cfcs`) and refutable (`atMostOneBit_necessity`) per the job's falsifiability bar; the MAP's Live/LatticeOnly axis is now a formal hypothesis (`ReachableClash`). |
| `Uwueave/CausalReach.lean` | **Op-based causal cuts** (JOB 2 + residuals): `FinHistory` / `Cut` / `Joint`; clash states are definitionally cut interpretations. Tag-scoped rem-after-add ⇒ OR-Set presence clash **Live** (`orset_clash_joint`); **element-wide rem after both adds** ⇒ same lattice pair **unreachable** (`ew_clashL_unreachable` / `orset_reachability_depends_on_remove_shape` — protocol dichotomy). Concurrent miniatures Live; free-id dup fragments Live; illegal cuts rejected. Content-addressing out of band. |
| `Uwueave/Liveness.lean` | **SEC liveness half** (JOB 4): finite-covering fairness `FairOn` + `fair_converges` lands every listed replica at `joinAll base issued` (rides `Delta.same_deltas_same_state`); G-Set `unfair_starvation` witness; two-replica `pair_exchange_converges`. Not coinductive ∞-often delivery — header says so. |
| `Uwueave/Traces.lean` | **One dependent pair** (JOB 5): 3-letter alphabet, independence `a∥b`, `a∥c`, not `b∥c`; `TraceEq`; `exec_traceEq`; negative `dependent_pair_reordering_changes_exec`; real bridge `exec_perm_of_fullIndep` (fullIndep → TraceEq → exec, not a dead hypothesis). Not full Zielonka. |
| `Uwueave/Nary.lean` | **n-ary tails** (JOB 6): `net_enum`, PN nonneg refutation over any two distinct keys, escrow sum bound over enum, `BudgetInvN` / `budget_segmented_enum`; Catalog/Segmented Bool results recover as instances; zero new `MergeState` proofs. |
| `Uwueave/KernelCFCS.lean` | **Move kernel as `Necessity.Impl`** (JOB 7): honest that under `GroundedBase` the derived-acyclicity invariant is true of every log (embedding package, not new confluence); real content is materialization ↔ membership and view determination via `absReplay_ext_mem`; `move_kernel_cfcs` + `move_kernel_view_sec`. |
| `Uwueave/Ceiling.lean` | The four uniqueness refutations proved to be **one theorem**: `uniqueness_ceiling` — an invariant entailing "at most one element per selector key" over a grow-only set is never I-confluent — with the generic witness constructor `merge_breaks_uniqueOn` (two distinct same-key elements, one per replica, produce the clash). `ceiling_atMostOne` / `ceiling_uniqueAnchor` / `ceiling_uniqueGrant` / `ceiling_determinism` re-derive the Catalog, Sequence, Authority and Automata refutations verbatim as one-line instances, at the originals' own witnesses; the originals stay in their home files with their narratives and pins. The mutex-shaped ceilings (`or_breaks_iconfluence`, sole-admin) are the same trap but a different selector shape — they cap occupied *keys*, not elements per key — and keep their own refutations. |
| `Uwueave/Budget.lean` | A budget trichotomy whose constructors carry the right kind of evidence: a witnessed plan may accept and a forced floor may reject (`rejected_sound`), while a lower bound alone never manufactures a plan (`lower_bound_does_not_license_acceptance`). The former unlinked synthesis gap is closed: `unlinkedFinitePlanSpace_agrees_with_exact_optimum` connects exhaustive finite selection of the predictive plan to the universe-polymorphic floor at exactly two. `reblocking_escapes_the_floor` proves that changing the workload's blocking would invalidate rejection. The unit is per-stream seam crossings, not meetings. |
| `Uwueave/CoordEffect.lean` | Coordination grades are strategy-indexed cost profiles, composed pointwise and minimized only when the session closes. `opt_compose_ge_sum_opt` names the compositional inequality, `optimum_compose_achieved` returns one coherent strategy that pays the result, and `pin_session_costs_exactly_one` proves the scalar alternative reports 0 for a session that costs 1. `minAlong_eq_listMin` now exposes the standard `List.min?` specification behind the finite optimum rather than maintaining a private recursive proof library. The strategy list is finite, nonempty, and chosen — not an enumeration of every seam. |
| `Uwueave/EraKernel.lean` | The executable ERA codec and `@[export uwueave_era_resolve]`: Rust marshals bytes, while this module calls `Era.resolve` and emits roles plus per-event status. `eraReplay_same_sets` proves byte-level delivery independence for the whole response; `duel_trace_marks_the_skip` and `duel_response_words` expose the paper's duel through the shipped format. Event-id uniqueness is enforced by the Rust boundary for attribution, not required here for deterministic resolution. |
| `Uwueave/Evidence.lean` | The epistemic carrier separates candidates, outstanding obligations, and certificates, yielding exact/provisional and closed/open fork states instead of conflating value plurality with future openness. `closed_iconfluent` says closure merges while determinacy does not; `divergent_futures_force_nonexact` forbids exactness across admissible divergent futures. `PositionCandidate` and `positionCandidates` adapt the hole calculus's exact value/source/position image without changing the stable three-axis `ResultEvidence`; `mem_positionCandidates` and `positionCandidates_hom` pin its membership and merge law. `render_retracts_when_a_new_source_appears` pins the boundary: `render` is sound for the sealed future, not arbitrary membership extension. |
| `Uwueave/Exits.lean` | The eight-exit display vocabulary and its worked ceiling, balance, and duel menus. Its typed applicability witnesses and refutations remain useful, but `Exit.price` and the hand-authored rows are explicitly superseded as semantic authority by `RepairMenu`: the price is independent free data, and the ceiling seam row demonstrably prints 0 where 1 is forced. Escrow tracks divisibility, not the resurrection/accumulation dichotomy. |
| `Uwueave/Fugue.lean` | A Fugue-style left/right origin tree, its op-set insertion model, and the RGA contrast on the same editing intent. `run_contiguous` / `fugue_runs_never_interleave` prove generated concurrent runs remain contiguous under the stated groundedness and concurrency hypotheses; `rga_head_runs_interleave` versus `fugue_head_runs_stay_contiguous` exhibits the concrete anomaly and repair. This is the model and theorem, not the shipping sequence kernel. |
| `Uwueave/Gated.lean` | Authorization as a derived view over grants, revocations, and move ops. `gated_sec` inherits SEC, `gated_antitone` proves late revocation can only remove effects, and `kernel_gate_agrees_gatedOps` connects the model to the shipping kernel under `WF` plus unique grants. Signatures remain a deployment premise; the gate bounds what a cited grant may do, not who may cite it. |
| `Uwueave/Histories.lean` | Repeated and criss-cross merge over a rank-grounded version DAG. `repeated_merge_breaks_the_invariant` shows the one-fork ancestral theorem does not close under merging its own results; `base_accident_decides_the_invariant` gives two equally maximal bases with legal versus illegal outcomes; `swap_never_converges` proves coherent base choice alone is not convergence. `historySafeFrom_iff` gives the exact condition over every extension admitted by coherent histories. Wave 23 exposes the proof-engineering surface used across the history stack: stable negative reachability (`not_reaches_of_ne_of_rank_ge`), `VersionDag.rank_induction`, semantic-origin `History.Coherent.induction`, budget-polymorphic `spend_run` / `spend_reachable` / `spend_reach_add` / `spend_reach` / `spend_locally_safe`, and shared counter-bound lemmas. The older root-reachability closure package implies exact safety but is not necessary (`counter_historySafe_true_and_not_mergeClosed`); the ceiling counter refutes it and the lock satisfies it. |
| `Uwueave/HonestRender.lean` | Rendering honesty over an abstract five-way carrier: `consumers_factor` proves every consumer is a five-handler dispatch, `no_honest_projection` rules out a silent total projection at a forked site, and `singularSelection_implies_namedPolicy` makes singular resolution name its policy. `salience_is_not_enforceable` is a proved limit: an abstract interface cannot force visually distinct pixels. The five-way inability to separate absent from pending is repaired, not erased, by `RenderSix`. |
| `Uwueave/JoinHom.lean` | The exact boundary between shipping evidence and shipping a derived summary. `summaryFold_iff_joinHom` is the architecture iff; `no_count_merge_without_provenance` refutes every binary combiner on counts; `count_summary_must_distinguish` makes provenance necessary. `monotone_pullback_can_fail` retracts the stronger monotonicity claim: upward-closed result invariants pull back, arbitrary ones do not. |
| `Uwueave/MergeModel.lean` | One parameterized confluence judgement over genuinely different merge signatures: join CRDT, ancestral/MRDT, and op-replay. Keys, states, merge contexts, results, and observations now occupy independent universes; laws remain separate predicates rather than class fields. The ancestral witness is refutably non-idempotent, and op-replay is a function of the op set but not of the two materialized views. `iconfluentIn_join_iff` and `iconfluentIn_ancestral_iff` recover the existing judgements without reproving them. |
| `Uwueave/MinimalSummary.lean` | Contextual equivalence constructs the coarsest future-sufficient *partition* for a query. `ctxQuot_coarsest_sufficient` proves the universal property and `ctxQuot_fold_answers` makes the quotient shippable; membership collapses to one bit, exact count collapses nothing, and the three-element threshold quotient has five classes. This is not a minimum-bit representation or a reachable-context quotient. |
| `Uwueave/Recoverable.lean` | The positive ancestral converse, with the merge constructed: `faithful_stepConfluent_iff_legalSerialization` characterizes when recoverable deltas admit a faithful invariant-preserving three-way merge. `comm_forces_symmetric_chooser` derives chooser symmetry from commutativity, while `budget_boundary` isolates illegal serialization as the counter obstruction. Recovery work is now explicit: `cheapLockConstructedMerge_work_le_one` gives a tight useful bound, whereas `paddedLockConstructedMerge_both_moved_work` proves correctness alone permits arbitrary padding. Step confluence alone still does not lift through longer branches. |
| `Uwueave/Repair.lean` | Typed transformations `Repair P Q`, multidimensional `Price`, and a proof-carrying `PromiseRelation` replace a flat exit plus scalar. `introduced_premise_forces_a_charge` and `no_free_arbitration` make trust costs unprintable as free; `crossings_cannot_see_the_difference` proves a crossing count cannot distinguish arbitration, fork exposure, retained evidence, or reachability restriction. `Repair.RestrictsReachability` states the exact admission loss; `RepairMenu.balanceEscrow_price_and_delta` exhibits it while seam crossings remain zero. Repairs compose, but their summed declared prices are not claimed minimal and nothing here searches for a repair. |
| `Uwueave/ResultStatus.lean` | Six runtime statuses separate static mergeability from reach-relative capability. `Status.Semantics` states the exact meaning of every cell; `exists_two_of_nonunique` packages fork witnesses; and `statusOf_semantics`, `statusOf_eq_iff`, and `statusOf_ne_iff` provide the canonical public constructor/inversion API consumed by renderers and effects. `declaration_is_relative_to_the_reach` proves one declaration can hold on a reach and fail after one admissible extension; `sixth_cell_is_distinguishable` separates definitive absence from pending despite identical empty candidate sets. `forget_statusOf` recovers the five-way render, and value-dependent finality refutes any status determined only by closure structure. |
| `Uwueave/SeamColoring.lean` | The safety clause of segmentation is exactly graph colouring (`safetyClause_iff_properColoring`); full segmentation additionally needs fiber stability, and `coloring_alone_does_not_segment` proves that residual is real. Over a covering finite pool and finite palette, `minimumSeam_search_total` exhaustively returns either a least certified seam or a proof that none exists; `pin_minimum_is_exact` computes the uniqueness clash's optimum as two colours. The certified search now delegates argument minimization to standard `List.minOn?`; `argMin_mem`, `argMin_le_of_mem`, and `argMin_first_tie_fixture` preserve membership, least cost, and first-tie behavior. No global completeness is claimed without those finite coverage hypotheses. |
| `Uwueave/Tactics/Core.lean` | The cycle-free machinery below the `classify` demonstrations and verdict layer: complete `FinEnum`s, heuristic `Probes`, the `Clash` evidence type, and `findClash`. `Clash.not_iconfluent` makes every returned hit a refutation, while `findClash_none` says only that the supplied pool contains no clash. Positive routes now return typed `RouteOutcome`s so resource refusal (`automaticFiniteStateCap = 64`, `automaticFinitePairWorkCap = 4096`) cannot be mistaken for a negative semantic result; compatibility Boolean wrappers remain. Verdict-valued classification deliberately lives in `Tactics/Verdict.lean`, where importing `Spec.Verdict` cannot recreate Core's import cycle. |
| `Uwueave/Tactics/Verdict.lean` | The minimal production verdict layer over `Tactics/Core`: `iconfluent_of_isFree` / `not_iconfluent_of_isFree_false`, `Clash.toVerdict` / `toVerdict_isFree`, and `classifyIn?` / `classify?` / `classifyFinite`. `classifyIn?_never_free`, `classifyIn?_sound`, `classifyFinite_isFree_iff`, and `classifyFinite_not_iconfluent` pin both negative and positive answers. The `verdict` tactic elaborator also lives here; heavy demonstrations and adversarial fixtures remain in `Tactics.lean`, so production consumers need not elaborate them. |
| `Uwueave/WeaveState.lean` | The library's composed loom document: node/content/activation/bookmark/pin/authority/quota fields inherit their merges, and `core_iconfluent` assembles the free field invariants. The pin ceiling stays deliberately live in `weaveDocVerdict`; `weaveDoc_segmented` lifts the combined pin/allocation seam to the whole document. It is a classified miniature, not a claim that text, moves, signatures, or networking are modeled here. |
| `Uwueave/Wellformed.lean` | Structural well-formedness is separated from application legality. `merge_preserves_wellformed` is unconditional, while `merged_doc_violates_onePin_but_is_wellFormed` proves a merge can violate the pin promise and remain a renderable document; `no_crash` quantifies over every reader total on well-formed documents. Unique anchors are deliberately excluded because including them would make the headline false. |
| `Uwueave/WorldFuture.lean` | Futures indexed by epistemic worlds rather than materialized states. `delivery_future_is_not_state_indexed` exhibits equal observed states with different issued-but-undelivered pools; `quiescence_is_a_sound_certificate` makes the world-keyed check sound, while `no_sound_state_cert_accepts_openW` proves that reusing the same fact at the state key is impossible. Frontier plus epoch still does not separate the witness; the pool does. |
| `Uwueave/Bounds.lean` | The modal and quantitative lower bounds meet in `coordination_necessary_and_costly`, but not at zero: `zero_floor_does_not_imply_cfcs` gives live pin forks that every per-stream clash decomposition misses. `fork_clash_charges_the_pair` recovers the missing joint charge. `ew_rejected_at_zero_over_unreachable_pair` then exposes the old cost model's reachability hole by rejecting on the element-wide OR-Set pair that no protocol cut reaches. |
| `Uwueave/CertificateScope.lean` | Future-sufficient keys as the quotient by equal residual futures, with independently universe-polymorphic worlds, results, observations, and key domains; `resQuot_coarsest_sufficient` proves the factorization property. The `MinimalSummary` bridge is equally polymorphic, while evidence-specific worlds/results remain at `Type 0` because their upstream carriers do. `residual_is_not_a_join_congruence` refutes a merge on these classes; `deliveryKey_sufficient` shows the pool belongs in the key and the epoch may be dropped. |
| `Uwueave/CliqueLive.lean` | Clique certificates jointly constrain live seam width and fork-scenario cost. `live_clique_forces_live_width` and `live_clique_forces_scenario_floor` are general lower bounds; `the_live_clique_number_determines_both` pins the slot witness at live 2 versus global 3. Width is not claimed equal to clique number in general: colouring may need more colours, and seam stability adds non-graph obligations; `the_two_floors_are_incomparable` says block and clique floors must both be reported. |
| `Uwueave/DerivedDocument.lean` | Evidence is encoded as a document without loss (`encodeEvidence_iso`), and `deriveDoc_hom` makes "a computation over a loom yields a little loom" a one-line join-hom composition. `AttributedDoc` augments it with exact value/source/position nodes: `forgetPositions_deriveAttributedDoc` recovers the old document on the nose, the two membership iff theorems retain candidate and position witnesses, and `deriveAttributedDoc_hom` preserves mergeability. The source and positions remain adapter inputs, not authenticated provenance. `tallyDoc_requires_evidence` transfers the count impossibility to documents while `seenDoc_joinHom` exhibits the provenance-retaining escape. Rank-grounded pipelines terminate and merge freely; acyclicity alone is explicitly weaker. `docStatus_encodeEvidence` lets the six-status renderer serve both primary evidence and derived documents. |
| `Uwueave/EraCertificate.lean` | ERA finalization as a delivery certificate: under the readable `Settled` premise, `era_finalisation_is_a_sound_certificate`; `era_stops_before_quiescence` shows the final prefix can stabilize while the full view still moves. Honest cut extension preserves that prefix, but `backdated_cut_rewrites_the_finalised_view` refutes the claim without the hypothesis. `an_event_born_finalised_rewrites_the_view` names the Byzantine boundary: announced event ids must be unforgeable. |
| `Uwueave/ForkGrade.lean` | A fork-aware coordination profile whose worlds are path endpoints by construction. `liveScenario_optimum_eq_zero_iff_no_live_clash` reflects zero (the reverse needs the constant seam in the strategy space); `cfcs_iff_locallySafe_and_all_finite_scenarios_zero` bridges the modal and quantitative readings. `the_disagreement_resolved` puts the pin workload's per-stream floor 0 beside its live fork optimum 1 on the same carrier. `Scenario.edgesOfPaths_eq_flatMap` exposes the branch-edge collector as the standard list combinator, letting membership and cost proofs reuse `mem_flatMap` and `countP_flatMap`. |
| `Uwueave/HistoryBase.lean` | Merge-base validity moved from state pairs onto a version DAG: `ValidInHistory` means lowest common base, two distinct maximal bases, or a proof that no common ancestor exists. State-level decisions and `VersionCert` are universe-polymorphic; the history-facing declarations honestly remain at `Type 0` because `Histories.VersionDag`/`History` still do. `coherent_never_unavailable` makes unavailable a cross-history answer; base-scoped certificates are sound where unscoped and root-scoped reuse fail. Its `spend_*` names are retained compatibility wrappers; the generic proofs now live in `Histories`. |
| `Uwueave/HistoryPolicy.lean` | Four policy judgements — base robustness, selector safety, explicit ambiguity, and history convergence — with their separations inhabited. The crown is `recordDetermined_converges`: equal records under one record-determined policy derive equal views over any rank-grounded version DAG. `SameShape.classify` packages the nine-way origin-constructor elimination used by record comparisons without equating merge bases. `the_swap_is_order_dependence` identifies the two-cycle as asymmetric self-base selection, and `the_self_base_policy_is_not_history_licensed` shows history validity refuses exactly that policy. |
| `Uwueave/FiniteHistory.lean` | Certified search over an explicitly supplied duplicate-free covering enumeration of a `VersionDag`. `reaches_iff_bounded` makes rank-bounded backward search exact; `mem_commonCandidates_iff` proves the filtered ancestor list exhaustive; and `policyAccepted_iff` certifies a proposed raw base selector on every ordered pair. `cc_root_pair_decision`, `cc_merge_pair_decision`, and `two_pair_decision` compute exact selected, ambiguous, and unavailable answers. `searchCertified` may still return `none` rather than misreporting unavailable, and the module neither enumerates an arbitrary/infinite DAG nor constructs a semantic `HistoryMerge`. |
| `Uwueave/LiveBudget.lean` | A reachability-aware budget verdict: only `liveRejected` carries a proof that the realized path cost agrees with the abstract workload; `carrierGlobalBound` has no model field and therefore cannot claim liveness. `ew_no_live_realization` proves the element-wide workload admits no live realization at all, while `claim_sound` assigns each constructor exactly the proposition it may print. `pathSegmented_iff_liveSegmented` connects the path-local strategy space to `LiveSegmented`. |
| `Uwueave/LiveCost.lean` | Proof-carrying paths replace reachability side conditions. `ClashChain.accused_are_connected` follows from construction, `cost_floor_becomes_live` names the required total simulation `Grounds`, and `totalModel_grounds_everything` says why a permissive model gives the repair no teeth. The tag-scoped OR-Set clash is live and charged; the element-wide pair refuses a live accusation and `ewTeleport_not_grounded` locates the failed transport. |
| `Uwueave/LiveSegmented.lean` | Segmentation relativized to co-reachable states, closing the strategy-space reachability hole. `live_optimum_strictly_below_global_optimum` proves least live width 2 versus least carrier-global width 3; `the_third_domain_is_charged_for_an_unreachable_pair` identifies the exact extra edge. The safety clause still equals live proper colouring, while fiber stability remains independent; the file records which `SeamAlgebra` laws survive or need weaker live hypotheses. |
| `Uwueave/MenuTotality.lean` | Makes seam-menu applicability decidable over a covering pool, provides real synthesis, and replaces a free hand-authored floor with a clique-backed `CertifiedSeam`. `uniqueOn_singletons_clash_iff` corrects the false "ceiling graph is complete" conjecture; `atMostOne_seam_row_refuted_at_every_finite_segment` shows the `Nat` ceiling admits no finite seam. `minimumMenuSynthesis_total` carries the exhaustive least-seam/refusal certificate into the menu without rerunning search, and `pin_minimum_menu_is_exact` shows the two-colour optimum reaches a real row. `clique_forces_joint_crossings` supplies the concurrent floor the sequential block calculus cannot see. |
| `Uwueave/Preo/Classification.lean` | Fragment 2's facet algebra: rules accumulate global verdicts, seams, mergeability results, or honest obligations. `verdict_agree`, `seam_forces_clash`, and `fourth_unique` prevent contradictory evidence; `run_answer_of_perm` proves route-order invariance. An equality `answer = some a` licenses `checkedVerdict`, with `checkedVerdict_isFree` pinning its semantic answer; `no_checkedVerdict_licence_of_answer_none` blocks unresolved rows. `mergeability_comp` transports a derived computation along one field projection, requiring surjectivity only for the negative `needsEvidence` direction. |
| `Uwueave/Preo/Demo.lean` | Executable acceptance tests for `preo`: the earlier seam/cross/custom-carrier/budget/export fixtures remain, and `SemanticSurface.Next` now proves the `typed derive` path end to end. Its raw program equals the hand `Expr.Program`; holes and reads are exact; an off-dependency delta reuses and chains the cache at zero counted root evaluations; the declared finite reach yields a least six-status effect; and the checked report pins site, status, future, resolution, surface, visibility, and disclosure. Malformed and raw-custom typed programs are rejected by guarded surface commands. |
| `Uwueave/Preo/Elab.lean` | The thin public command facade and sole registration point for `preo`, `preo_certificate`, `preo_budget`, `preo_export`, `#preo_report`, and native `preo_protocol`. It delegates to non-registered phase cores below, preserving the historical public elaborator names while preventing a leaf import from installing a second handler. |
| `Uwueave/Preo/Elab/Internal.lean` | Shared command infrastructure: type/head probes, syntax dependency analysis, field projection/plant construction, trust-floor checks, optional `probeCommand`, mandatory `emitRequired`, and whole-command `withEnvTransaction`. Required failures retain diagnostics but restore the environment—including persistent report rows—so a late phase cannot leave a partial declaration. |
| `Uwueave/Preo/Elab/State.lean` | `State.emit` performs field parsing, carrier/default normalization, right-nested `State`, projections, merge-homomorphism and planting declarations, returning one aligned `State.Context`. Field source order is the indexing ABI consumed by every later phase. |
| `Uwueave/Preo/Elab/Invariant.lean` | `Invariant.emit` builds the ordered invariant registry (`Fired`, `FiredSeam`, `Result`): checked global verdict facets, field seam facets, obligations, document-scale transports, and report metadata. Positive routes are emitted and floor-checked; a probe failure remains a non-answer rather than evidence. |
| `Uwueave/Preo/Elab/DocumentSeam.lean` | `DocumentSeam.emit` is the declaration-scale seam fold. Exactly two distinct field seams are lifted through their right-nested projections, conjoined, and enriched in source order only by FREE rows whose witness-side legality kernel-checks. |
| `Uwueave/Preo/Elab/Future.lean` | `Future.emit` is the named-future phase: it emits the explicit world-model alias and checked relation, floor-checks the result, and returns its `Future.Context` report row. It does not infer a future from materialized state. |
| `Uwueave/Preo/Elab/TypedDerive.lean` | `TypedDerive.emit` carries one `Raw.infer` witness through exact holes/reads, conservative certificates, proof-tied cache updates, equality-future result declaration, finite-reach report, and policy identities. A failed inference transaction emits none of this API. |
| `Uwueave/Preo/Elab/Derive.lean` | `Derive.emit` consumes its extended `Derive.Context` for ordinary single-field Lean derives and their ordered mergeability registry. Each successful route is checked against the generated computation; unmatched shapes produce an obligation, never a guessed `fromResults` answer. |
| `Uwueave/Preo/Elab/Protocol.lean` | `Elab.Protocol.emitOpaqueProtocols` and `.emitSessions` own the declaration phases; `ProtocolSurface.elabNativeProtocolCore` owns recursive native `preo_protocol`. They retain one global strategy, exact seven-axis demands, bounded crossing origins, and transactional generated declarations without registering commands themselves. |
| `Uwueave/Preo/Elab/Declaration.lean` | `Declaration.elabPreoDeclCore` is the transactional orchestrator for `preo`. It fixes phase and report-row order—state, invariants/seam, futures, typed derives, ordinary derives, protocols, sessions—and writes `preoExt` only after every required declaration and floor check succeeds. |
| `Uwueave/Preo/Elab/Certificate.lean` | Non-registered `Certificate.elabPreoCertificateCore`. It positively checks that the written type reduces to `Future.CheckedCertificate`, emits the exact dependent term, floor-checks it, and rolls back atomically on failure. |
| `Uwueave/Preo/Elab/Budget.lean` | Non-registered `Budget.elabPreoBudgetCore`. It emits the five-currency limits/session aliases, one exact `ProfileUpperBound`, its carried plan, and the peer-barrier compatibility projection; no scalar conversion is inferred. |
| `Uwueave/Preo/Elab/Export.lean` | Non-registered checked export core. `Names.ofSurface` preserves every historical `E.*` name; the heterogeneous manifest fold retains item order and exact-plan equality, then emits bundle/artifact/encoding/durable bytes/V2 validation/validated/rendered declarations through mandatory commands inside one environment transaction. Composed profile plans and validation refusals leave no partial export. |
| `Uwueave/Preo/Elab/Readback.lean` | Reduction-only `Readback.readAnswer` and `.readMergeAnswer` helpers for `Classification.answer` and `.mergeAnswer`. Outer failure and genuine inner `none` remain distinct, so unreadable evidence cannot print as FREE. |
| `Uwueave/Preo/Elab/Report.lean` | Non-registered `Report.elabPreoReportCore`. It reads the persistent rows and reduces checked classification constants at print time; verdicts and mergeability answers are never duplicated into display metadata. |
| `Uwueave/Preo/Syntax.lean` | The surface grammar and its semantic support: built-in and explicit-seed carriers, keyed families, invariants, ordinary one-field derives, named futures/certificates, proof-carrying protocols/budgets, checked export manifests, and parser-hard `typed derive` rows over explicit schemas and finite reaches. Ordinary Lean derives remain the opaque one-field escape hatch; typed derives use the first-order `Expr.Raw` AST, rejecting malformed, out-of-schema, wrong-typed, and raw-custom programs. |
| `Uwueave/Preo/Expr.lean` | The intrinsically typed first-order expression language now consumed by `typed derive`. `Raw.infer`/`compile?` are the fail-closed existential typechecker, `Program` retains the raw spelling and inference equality, `Term.holes`/`reads` are exact dependencies, and `Term.eval_ext` proves them sufficient. Constructor-specific `[simp]` rules normalize `reads` for projections, options, Boolean operations, and the Nat primitives, removing repeated set algebra from generated proofs. `MergeSafe.sound` and `MonotoneSafe.sound` erase conservative certificates to semantic laws. Ill-typed raw syntax and raw custom nodes are refused; a custom typed node still requires explicit locality/algebraic evidence. |
| `Uwueave/RenderProgress.lean` | Splits pending truth, fair-delivery progress, and authorized actionability into separate contracts. `statusOf_pending_escapable_by_sealing` proves the old escapability clause can be discharged by abandoning every source; `pending_progress_under_fair_delivery` gives the actual liveness result; `a_revoked_actor_gets_no_button` makes authorization load-bearing. The semantic widget forbids `loading` at `absent`, though pixel salience remains outside the model. |
| `Uwueave/RenderSix.lean` | The six-way carrier and soundness contract that distinguish definitive absence from pending. `five_handlers_cannot_separate` proves the old limit and `six_carrier_separates` retires it; `statusOf_sound6` adds absent-final and pending-escapable obligations while folding back to the five-way contract. Its status case analysis now consumes `ResultStatus.statusOf_eq_iff`, the shared exact inversion API, instead of maintaining a second decision tree. `spinner_is_an_honest_five_status_renderer` proves the old interface admits a forever-spinner; `absence_is_the_more_defensible_badge` is specifically a two-sided merge fact, not a unilateral one. |
| `Uwueave/RepairMenu.lean` | Menus generated from typed repairs: every row is available, conditional with a priced obligation, or universally impossible. `menu_price_is_projection` and `menu_delta_is_projection` prevent independent display drift; `ceiling_seam_row_disagrees` demonstrates the old hand row's 0 versus the generated forced 1. `balanceEscrow_price_and_delta` corrects escrow's old free price: it charges the distinct reachability-restriction currency and supplies a source-legal state the target forbids, even though its seam-crossing projection is zero. |
| `Uwueave/TextSummary.lean` | Applies the summary theorems to sequence views. `no_text_merge_without_provenance` refutes every combiner on rendered text with well-formed replica states; `linearize_not_joinHom` separately exposes a causally pending-anchor boundary. `ctxEquiv_iff_agree_window` exactly characterizes the quotient: two arbitrary states are contextually equivalent iff they agree on every addressable element/anchor pair, with no `WF` or unique-parent premise. Tombstone identity remains load-bearing while tombstoned content may go; `verdict_order_policy_invariant` preserves the evidence verdict across RGA and Fugue order. |
| `Uwueave/Specification.lean` | Outcome-valued specifications over a declared refinement preorder. For total specifications, `coordinationFree_iff_historyMonotone_and_fiberDirected` exactly decomposes coordination freedom into history monotonicity and directed outcome fibers; `invariant_coordinationFree_iff` recovers `IConfluent` at the singleton-outcome boundary. The empty, branching-Boolean, and zero-absent witnesses separately expose vacuity, missing fiber directedness, and the fact that I-confluence does not imply monotonicity under arbitrary illegal extensions. |
| `Uwueave/Protocol.lean` | The deep protocol AST for operations, sequence, parallelism, nonempty finite choice, bounded repetition, and synchronization, retaining all seven scheduling axes and one global strategy. `elaborate` returns a checked `Session`, `Schedule`, `Plan`, and exact five-currency bound. `repeatDemands`, `repeatDemands_zero` / `_succ`, and `repeatSession_demands` expose bounded-repeat observations without globally unfolding the large proof-indexed session term; a 400-repeat fixture pins the normalization boundary. `Preo.ProtocolSurface` gives all six constructors a parser-safe native spelling while reusing this one semantics; crossing/meeting non-functions survive the surface unchanged. Runtime fairness, message loss, time, and deadlock remain outside the AST. |
| `Uwueave/Preo/ArtifactData.lean` | The minimal neutral first-order export leaf: stable typed IDs, artifact rows, `Artifact`, structural encodings/decoders, and `ArtifactEncoding.decode_canonicalEncoding`. It imports no checked judgement, scheduler, elaborator, diagnostics, or examples. Decoding produces data only and cannot reconstitute semantic proofs. |
| `Uwueave/Preo/ArtifactChecked.lean` | The one-way proof-indexed origin layer. Private checked constructors require real declaration, verdict, future, session, plan, and exact-plan `ProfileUpperBound` terms before `Checked*.toArtifact` erases them to stable IDs, witnesses, demands, origins, promised limits, and realized five-currency profiles. No decoded value is promoted back to proof authority. |
| `Uwueave/Preo/ArtifactDiagnostics.lean` | Optional `Repr` instances for the neutral artifact IDs, rows, and encodings. Keeping generated pretty-printer code outside `ArtifactData` preserves the existing umbrella API without putting diagnostics in the runtime validation closure. |
| `Uwueave/Preo/Artifact.lean` | The compatibility umbrella for `ArtifactData`, `ArtifactChecked`, and `ArtifactDiagnostics`, plus the closed nonempty examples. Existing import and declaration names remain stable; new kernel-facing code should depend on the narrow data or checked leaf it actually needs. This is a transport boundary, not a verifier or a minidregg-specific manifest. |
| `Uwueave/Preo/Future.lean` | Future declarations retain an epistemic world plus state, pool, frontier, epoch, and a typed scope. Stability and certificates restrict contravariantly along `FutureDecl.IncludedIn` (`certificate_sound_restrict`); the converse is concretely false. `same_state_different_worlds_block_certificate_reuse` proves a valid quiesced world certificate cannot be keyed only by materialized state, while `era_certificate_is_satisfiable_and_refutable` projects ERA finalization into a nonconstant delivery certificate. |
| `Uwueave/Preo/Export.lean` | The declaration-level one-way export seam: a private `DeclarationBundle` consumes checked fields, direct `Spec.Verdict`s or answered `Classification`s, world-indexed future certificates, ordinary protocol elaborations, and exact-plan five-currency budgets, then projects one neutral artifact and canonical encoding. `whole_artifact_is_hand_composition`, `budget_export_is_exact`, and the classification-agreement theorems pin the whole value to its semantic inputs; unresolved rows have no licence. Arbitrary decoded verdict and budget tags remain first-order data, with no wire-to-proof constructor. |
| `Uwueave/Preo/ArtifactDurableCore.lean` | The data-only canonical `List UInt8` codec and frame contract for neutral `ArtifactEncoding`. `stackSafeEncodeData`, generic `stackSafeEncodeFrame`, and generic `stackSafeEncodeValue` are tail-recursive executable paths proved byte-for-byte equal to the canonical logical encoders; `decodeValue_stackSafeEncodeValue_append` preserves exact suffix-aware reopen without introducing a second format. The explicit artifact format remains **v2** because its product includes witnessed five-currency budgets; v1 frames are refused rather than decoded under the new shape. `decodeProjection_projectionBytes_append` proves exact version/domain-framed roundtrip with trailing journal bytes; exact decoding rejects surplus and noncanonical payload bytes, and wrong version/domain tags refuse. This leaf is the codec imported by the journal runtime. |
| `Uwueave/Preo/ArtifactDurable.lean` | The compatibility umbrella over `ArtifactDurableCore` plus checked, nonempty examples and logical torn-journal fixtures. `Examples.two_frames_then_torn_third` recovers two complete artifact projections before a logically witnessed torn append. Decoding remains first-order and no filesystem/flush/crash refinement is claimed. |
| `Uwueave/Preo/ProjectionV1Core.lean` | Minimal data-only V1 validation leaf. It owns the schema, untrusted types, exact bounds/errors, private `ValidatedProjectionV1`, and `validate`, importing only `ArtifactData`; budget rows refuse before crossing the boundary. Rendering, `Repr`, checked examples, and giant strings are absent from this production closure. |
| `Uwueave/Preo/ProjectionV1Diagnostics.lean` | Opt-in `Repr` instances for V1 projection, policy, error, and validated types. It imports artifact diagnostics without burdening the core validator. |
| `Uwueave/Preo/ProjectionV1.lean` | The V1 renderer facade over `ProjectionV1Core`: deterministic Rust source, validation-first rendering, encoding-congruence/error-preservation theorems, and small public fixture hooks. Its exact project-module closure is `ArtifactData` → `ProjectionV1Core` → this renderer; naturals remain unbounded decimal strings, and the closure contains neither diagnostics, proof-indexed exports, checked example graphs, nor large exact strings. |
| `Uwueave/Preo/ProjectionV1Examples.lean` | Opt-in checked V1 acceptances and adversarial refusals, including budget rejection, ID/reference/crossing/profile/resource failures, and positive budget-empty artifacts. This is the only V1 layer that imports proof-indexed `Preo.Export`. |
| `Uwueave/Preo/ProjectionV1Fixtures.lean` | Opt-in exact generated-source strings and renderer-component equalities, isolating their elevated recursion limits from production validation and rendering. `empty_projection_lines_fixture` is the exact full-source fixture name. |
| `Uwueave/Frontier.lean` | Timely-style antichain progress for open membership. `flat_frontier_loses_position` proves source-level closure bits erase timestamp position; advance and delivered-set growth are kept separate, with `advance_without_delivery_is_unsound` refuting forward completeness from advance alone. Under explicit pool well-formedness, completeness, and settlement hypotheses, `world_complete_values_stable` transports frontier knowledge to delivery stability of candidate values—not to the full render. |
| `Uwueave/Authenticity.lean` | The constructive cryptographic handoff without a cryptographic hardness theorem. Domain-separated signing messages bind protocol version, issuer, key epoch, and every grant/event/move field; `move_domain_separated` and `signingMessage_move_injective` make the move lane explicit. `authenticity_violation_extracts_forgery` turns any accepted unissued record into an exact forgery witness. An intentionally insecure toy scheme makes the vocabulary both satisfiable and refutable; deployments still owe an actual EUF-style argument. |
| `Uwueave/AuthenticatedAdmission.lean` | The model-level conjunction of authentication, fork attribution, holder binding, and capability admission. `authenticIssuer_to_signatureAuthentic` derives Byzantine attribution premises from accepted signed events through an explicit codec. `AuthenticatedGatedOp` additionally requires genuine issuance, an explicit grant-holder policy, and `Gated.gatedOps`; Mallory's borrowed live grant and Bob's revoked genuine grant make those checks independently load-bearing. FORMAT v3/FFI signature admission remains outside the result. |
| `Uwueave/AuthenticatedFrontier.lean` | Authentication and frontier semantics meet without being conflated. `AuthenticatedProgress.ofAuthenticIssuer` retains one accepted signed ERA progress event, received-trace membership, genuine `WasIssued`, exact issuer/source, reserved kind, and finite-roster membership. A deployment-authored `ProgressCodec` projects timestamp, both frontiers, and the issued/before/after delivered sets from that same signed event; `AuthenticatedAdvance.toDeliveryAdvance` exposes the independently proved lawful transition. This authenticates an exact signer-authored claim, not an external running state, truthful codec, network observation, or cryptographic implementation. Consumers must bind every projection to their actual state. |
| `Uwueave/AuthenticatedWorldContext.lean` | The proof-carrying successor to `WorldContext`: accepted-and-issued signed typed-position claims retain exact world/value/static-position bindings, while signed-decoded origin/version are checked against the real causal cut and version base. `ConsumptionReceipt` grows one-use tombstones without deleting outstanding grants; `AuthenticatedConsumingDelivery` binds authenticated frontier issued/delivered sets exactly to both actual worlds, requires every new candidate to have a contextual signed witness, justifies every used grant, ties the progress signer to the actual roster, and enforces grant uniqueness. It projects only to `WorldFuture.DeliveryFuture`. The strict one-grant/one-candidate rule deliberately rejects batch-capability semantics; codecs, signature security, and host delivery remain deployment premises. |
| `Uwueave/AuthenticatedEraCertificate.lean` | A signed and genuinely issued progress event is joined to an independently proved lawful, delivery-complete ERA announcement without making either premise imply the other. `CompleteAnnouncement.settled` binds decoded cut/world/pool/log/frontier data from that same event and discharges `EraCertificate.Settled`; `Verification` exposes exact payload, issuance, source/roster, announcement, delivery scope, and surviving seal. `ReusableCertificate.sound` deliberately forgets the record and reuses only `settledCert` at exact `eraKey` equality under delivery. Accepted-but-unissued and authenticated-but-incomplete fixtures refuse the two missing halves. `EraCodec`, roster meaning, cryptographic security, live observation, event-ID authenticity, honest-extension detection, and the announcement future remain external. |
| `Uwueave/Byzantine.lean` | Separates equivocation, forgery, and withholding. Fork evidence is permanent under gossip and attributes blame only with authentic issuance; an unauthenticated submitter can otherwise pass the ordinary grant gate. `authentic_issuance_preserves_finality` states the ERA finality repair with grounded announcements and id authenticity, while `forged_announced_id_breaks_era_finality` realizes the exact failure without them. `authenticity_and_delivery_are_independent` keeps safety and liveness obligations distinct. |
| `Uwueave/Durable.lean` | A logical durability rung: canonical payload codecs, version/domain-separated self-delimiting frames, append-only journals, and prefix recovery. `recover_crashPrefix` proves that a canonical journal followed by an explicitly characterized torn frame recovers exactly the completed records; `recover_crashPrefix_monotone` preserves prefix order as more records complete. `DeploymentAssumptions` names, but does not inhabit, the missing filesystem/flush/crash refinement. |
| `Uwueave/EvidenceGraph.lean` | Structured evidence documents with typed candidate, source, obligation, and certificate vertices and rank-descending attribution/owing/discharge edges. Endpoint `WellFormed` is I-confluent and `encodeEvidenceGraph_joinHom` preserves merge. `flat_encodeEvidence_is_projection` recovers the old evidence document through a forgetful join homomorphism; `danglingAttribution_is_malformed` proves endpoint integrity remains a real invariant rather than a consequence of typed edge shapes alone. |
| `Uwueave/ChoreoRec.lean` | Guarded anonymous recursion over `Choreo`, interpreted only through finite fuel-bounded approximants. `approximate_embed` proves conservativity for every finite choreography and `projection_sound_approx` reuses the existing global/local semantics rather than inventing a recursive bisimulation. The operational layer proves a guarded barrier loop can step and a mismatched barrier is deadlocked; this is finite local progress only, with no fairness or eventual-delivery claim. |
| `Uwueave/WorldContext.lean` | Delivery futures extended with active authority capabilities, a downward-closed causal cut, and a version-history base/head. `delivery_projects` forgets these axes and `delivery_lifts` recovers a projected step only under explicit frozen-context and admission hypotheses. `same_world_axes_hide_context` and `projected_delivery_does_not_lift_without_context` prove equal materialized state, pool, frontier, and epoch do not determine the allowed future. `AuthenticatedWorldContext` now supplies the model-level signed/issued typed-position and one-use-consumption successor, while deployed cryptography and automatic IDs remain external. |
| `Uwueave/RepairSynthesis.lean` | Exact search over an explicit finite repair catalog. Rows retain stable IDs, decidable residual applicability, the actual typed `Repair`, and its complete eight-axis `Price`; a caller-supplied valuation ranks without replacing that record. `Catalog.minimum_none_exhaustive` and `Examples.refusal_is_exhaustive_for_catalog` scope refusal to supplied entries, while `finds_least_applicable` proves the executable search skips an inapplicable zero-score row. No repair universe, seam, or escrow partition is enumerated. |
| `Uwueave/FiniteRepairMenu.lean` | A bounded author-facing adapter over `RepairSynthesis`. Raw rows pass an exact length check and a strictly increasing numeric-ID check before `CheckedUniverse.toCatalog` exposes the unchanged underlying catalog. Search returns the first applicable authored ID together with its exact dependent `Repair`, generated available menu row, and complete eight-axis `Price`; refusal quantifies only over the checked list. Numeric IDs are an authored deterministic policy, not semantic cost or authentication: changing only them changes the selected priced repair. Empty, oversized, and reversed-ID fixtures keep vacuity, resource refusal, and noncanonical order visible. This does not discover a candidate universe, seam, escrow partition, global minimum, or exhaustive menu, and closes no marker. |
| `Uwueave/ChoreoChoice.lean` | Communicated Boolean choice over read-free `Choreo` blocks. `projection_sound` needs no `ReadsAgree`: the observer emits one label and remote endpoints branch on that delivered datum. The divergent-state fixtures exercise both branches while local observations disagree; missing labels and observer-label mismatches return `none`. This is finite safety, not channel authenticity, fairness, recursion, or eventual delivery. |
| `Uwueave/ClashGraph.lean` | Every caller-enumerated finite simple graph embeds exactly as the singleton clash graph of its independent-set invariant (`singleton_clashes_iff`). The induced `C₅` has no singleton triangle yet `c5_forces_three_domains`, proving the chromatic floor is real. A proof-carrying finite `LeaveOneOutObstruction` separately transports its listed size to a global segmented-width floor; no arbitrary carrier or infinite graph is enumerated. |
| `Uwueave/CompositeDelta.lean` | Explicit finite operation patches close the run-level ancestral-confluence boundary. `legalUnderComposition_iff_ancestralConfluent` is exact for arbitrary admitted patches; a proof-carrying residual `Algebra` supplies diamond, merge, and legality laws. The cheap lock inhabits it, while the existing two-step counter fails `LegalUnderComposition` and therefore cannot supply an algebra. No patch is reconstructed from state endpoints. |
| `Uwueave/ContextCompiler.lean` | An executable finite contextual quotient over caller-supplied states, contexts, and homogeneous queries. `signature_eq_iff` makes signature equality exactly the restricted multi-query contextual relation; `sufficient_refines_signature` is its common-refinement universal property, and representative decoding is choice-free. Completeness must be supplied before comparison with carrier-wide `CtxEquiv`; `restricted_contexts_can_coarsen` shows why. |
| `Uwueave/Preo/Incremental.lean` | Conservative differential evaluation plus the adapter used by `typed derive`. `updateProgramCache_correct` lets proof-tied caches chain through typed deltas; an off-dependency change reuses the exact value with zero counted root evaluations, while touched terms recompute once. `TypedResult.totalSound` gives every pure snapshot program an exact singleton six-status semantics under the equality future and constructs a `ResultProgram` over the authored finite reach. Opaque custom nodes still miss unless their author supplies a proof-carrying `IncrementalLaw`; the work counter covers root semantic evaluations only. |
| `Uwueave/StatusEffects.lean` | Six-status effects are downsets of an explicit refinement relation, with real lattice operations and exact embedding of the legacy three flags. `infer_is_least` computes the least effect over an explicit finite reach. Wave 27 centralizes executable reification: `allShapes` fixes canonical artifact order, `refinesBool_eq_true_iff` reflects semantic refinement, and `mem_inferredShapes_iff` proves the duplicate-free finite list is exactly `infer` membership; V3 no longer carries a second six-shape relation. `TotalSoundEvaluator6.semanticsAt` uniformly returns the exact `Status.Semantics` row. Resolution remains explicit. |
| `Uwueave/Temporal.lean` | Infinite action-labelled traces distinguish safety, weak fairness, and strong fairness. Generic theorems derive occurrence from continuous enabledness under weak fairness and show strong fairness implies weak fairness. Concrete `WorldFuture` and `RenderProgress` adapters prove a fair genuine delivery exits `pending`; the constant pending trace consists only of valid delivery steps yet is not weakly fair. Event indices are not wall-clock time. |
| `Uwueave/WovenEdit.lean` | A small checked local edit calculus complements merge preservation for `WovenDoc`: create, bookmark, update, and logical tombstone commands are checked against the current state, and `apply_preserves` / `runCommands_preserves` retain all six `WellFormed` conjuncts. Fixtures reject out-of-horizon clocks, dangling references, and disguised tombstones, while a legal four-command script succeeds. Physical deletion, GC, text edits, grants, pins, and cross-tree hole safety remain outside the calculus. |
| `Uwueave/Preo/ProjectionV2Core.lean` | Minimal data-only V2 validation leaf. It reuses `ProjectionV1Core` on a budget-cleared view, then checks action histograms, obligation coverage, budget IDs/references, plan/session/profile agreement, canonical five-currency rows, and every pointwise limit before constructing private `ValidatedProjectionV2`. |
| `Uwueave/Preo/ProjectionV2Diagnostics.lean` | Opt-in V2 `Repr` instances; its embedded V1 error makes `ProjectionV1Diagnostics` an explicit dependency rather than an accidental facade import. |
| `Uwueave/Preo/ProjectionV2.lean` | The V2 deterministic Rust renderer facade over `ProjectionV2Core`, with validation-first rendering, encoding-congruence/error-preservation theorems, and small fixture hooks. Its exact project-module closure is `ArtifactData` → `ProjectionV1Core` → `ProjectionV2Core` → this renderer; it remains first-order data only and imports neither diagnostics, `Preo.Export`, checked examples, nor fixtures. |
| `Uwueave/Preo/ProjectionV2Examples.lean` | Opt-in proof-originated full export and executable validation/refusal examples: action-profile lies, uncovered obligations, dangling/mismatched/duplicate budget references, malformed profiles, bounds, and exceeded limits. |
| `Uwueave/Preo/ProjectionV2Fixtures.lean` | Opt-in giant budget-renderer equality and unbounded-decimal fixture, keeping the `maxRecDepth 10000` proof outside production projection closure. |
| `Uwueave/HistoryEngine.lean` | An executable finite history boundary joining covered DAG search, scoped semantic policies, and explicit composite patches. `decidePair` has selected, ambiguous, unavailable, and proof-backed refused branches; the graph and semantic sweeps cover every ordered pair without making a partial policy total. `admitSelected` turns a certified base plus caller-supplied patch-labelled branches and a residual algebra into a legal policy-identical diamond. One residual delivery always converges; arbitrary positive duplicates additionally require `ReplayStable`. The length-two counter cannot supply that algebra. |
| `Uwueave/HistoryRuntime.lean` | Total finite history decisions and causal append. `refused_impossible` eliminates the finite engine's proof-backed refusal under coherent higher judgement, `decideTotal_valid` and `higherSweep_complete` cover the authored finite pair space without manufacturing an infinite enumeration, and `appendDag_reaches_inl` materializes a selected merge as a fresh proof-carrying child. The event layer admits only duplicate-free, non-self, causally closed parent lists: exact retries are idempotent, ID/content collisions and missing parents refuse, and `sameEventSet_converges` is independent of arrival order. Wave 26's bounded `DeliveryState` buffers causally premature events, drains deterministically when parents arrive, refuses retry/collision/self/duplicate-parent/capacity failures, and preserves `DeliveryValid` (capacity only) through successful `receive`/`receiveAll`; `SettledSameEventSet.view_eq` gives convergence after settlement. Stable IDs remain caller-supplied equality keys, not authenticated or globally unique. `orderAgreement_iff_selector_symmetric_at` states the exact conditioned symmetry requirement; `asymmetric_but_convergent` prevents it being over-read as a universal necessity. |
| `Uwueave/PersistentRuntime.lean` | A pure authoritative-log and recovery contract. Checked replay treats exact nonce retries idempotently and conflicting nonce content as refusal; a `CheckedBatch` plus the explicit `AtomicBatchObservation` premise reopens only before or after the complete batch. Validated checkpoints replay their suffix exactly like the whole log, and derived caches are irrelevant to reopen. `strict_prefix_not_atomic` and `snapshot_only_recovery_unsafe` make atomicity and record identity load-bearing. No filesystem, checksum, lock, flush, rename, or power-loss refinement is claimed. |
| `Uwueave/PersistentHistoryRuntime.lean` | The causal event admission function lifted into `PersistentRuntime`'s authoritative cursor/checkpoint contract. The delivery schema persists authoritative arrival records separately from materialized/pending state; `DeliveryCursorCoherent` is capacity plus exact arrival = materialized-or-pending membership. `DurableArrivalCallbacks` now names the typed receive/reopen equations, `schemaArrivalCallbacks` inhabits them, and `durableCallbacks_reverse_reopen_exact` pins reverse replay. Rust's separate `HistoryArrivalJournal` appends accepted arrivals before in-memory transition, replays bounded pending state, verifies canonical capacity-bound checkpoints, and refuses collisions/corruption; opaque payload bytes are deliberately not authentication. No theorem relates its bytes, checksums, sync policy, or filesystem to Lean. The older `BufferedHistoryJournal` still loses pending state, and Rust parent lists are strictly increasing where Lean asks only `Nodup`. |
| `Uwueave/FiniteHistoryDelivery.lean` | An authored finite `History` is paired with an exact version/event enumeration, injective caller IDs, origin-shaped parent lists, parent closure, coherence, ancestor selection, and policy generation. A `DeliveredGrowth` additionally assumes a permuted arrival list, successful logical replay, exact accepted records, cursor coherence, and settlement; only then do `materialized_iff`, `sameEventSet`, and `eventSetView_eq` forget arrival order and capacity. `FiniteGrowth.view_eq_state` and `semantic_view_eq_of_recordDetermined` keep semantic history derivation behind the existing policy premises rather than deriving it from event-set equality. The module constructs no fresh succession, authenticated ID, host bytes, Rust parent canonicalization, network liveness, or Lean↔Rust refinement, and closes no marker. |
| `Uwueave/Preo/ArtifactJournalKernel.lean` | The executable scanner for concatenated canonical ArtifactDurable-v2 frames, importing the narrow `ArtifactDurableCore` rather than checked examples or pretty printers. It returns exact record offsets and stops at the first clean EOF, syntactically torn final frame, or corrupt frame; `scan_stops_at_first_refusal` and `scan_torn_final` pin those boundaries. A narrow exported kernel returns one validation byte for exactly one canonical frame. `PhysicalRecord.Valid` names outer version/domain/length/digest obligations parametrically; it implements neither the digest nor stable storage, and opaque payload mutations detectable only by authentication remain outside framing. |
| `Uwueave/Preo/ArtifactJournalDiagnostics.lean` | Optional `Repr` instances for journal faults, refusals, inspections, records, stop reasons, scan results, and physical records. Operator/test diagnostics retain their public instances without pulling generated display code into the exported validator's native object closure. |
| `Uwueave/Preo/Planning.lean` | The bounded planning surface. `actionChoices` enumerates exactly the `2^n` canonical sublists of a duplicate-free, pre-capped action universe; `generatedPlans` retains exactly the covering schedules. A `Problem` runs the existing five-currency schedule and eight-axis repair engines under explicit ranking policies and a universal structural compatibility proof, returning a coupled selection or exact finite-scope refusal. The Boolean quota generator enumerates every exact partition and selects only nonstarving rows. No currency conversion or claim beyond the authored action/repair universes is made. |
| `Uwueave/Preo/ProtocolSurface.lean` | A parser-safe native spelling of all six deep `Protocol.Term` constructors. Every `preo_protocol` emits the exact term, one elaboration, session, plan, five-currency limits, and exact `ProfileUpperBound`; operation leaves retain all seven demand axes and crossing origins remain bounded `Fin`s. The full fixture exercises operation/sequence/parallel/choice/repeat/sync; out-of-range origins and unsupported nodes fail at the surface. The selected branch is a deterministic natural in this first fragment, not a liveness or channel theorem. |
| `Uwueave/Preo/ResultProgram.lean` | Checked six-status programs and reports. A `CheckedDeclaration` fixes its future and explicit resolution in the type, retains a finite reach, infers its least effect, and exposes the exact semantic row through `semanticsAt`. `ExactSnapshot.totalSound` centralizes complete six-status soundness for any pure evaluator stable under its authored future; `Incremental` and `StateProgram` delegate to it without changing their public semantics. `CheckedReport.says_semantics` connects any carrier claim to that row and refuses impossible status or resolution claims. `ReachReport` retains authored-reach membership and proves effect support; `ObservedReport` additionally carries a caller-supplied `ObservationBoundary.Authentic` witness to the rendered site. None of these wrappers discovers reachability or authenticates a world itself. |
| `Uwueave/StatusSemanticsAcceptance.lean` | Focused six-row acceptance/refusal suite. It reaches every `Status.Semantics` constructor, proves the old partial contract admits a pending-with-candidate liar rejected by total semantics, exercises reach-admitted typed snapshots, named-resolution refusal, and an explicit observation boundary that refuses the wrong state. |
| `Uwueave/Preo/ArtifactEmit.lean` | Opt-in, I/O-free registry from stable artifact names to exact canonical durable bytes. `semanticEncoding_eq_generated` pins the whole computable reification to the checked export; the tail-recursive implementation is proved equal to canonical framing, `bytesImpl_eq_bytes` connects native execution to the noncomputable named values, and `byteArray_data_toList` pins the host buffer byte-for-byte. |
| `Uwueave/Preo/ArtifactEmitMain.lean` | Executable-only CLI entry point for `--list`, `--stdout`, and `--output PATH`. Merely importing `ArtifactEmit` performs no I/O; this `main` writes only when explicitly invoked. Like `ArtifactInspectionMain`, it is mapped and separately built/run but is not imported by either aggregate: two root-level `main` declarations cannot coexist in one Lean environment. The pure `ArtifactEmit` library remains root-imported and trust-gated. This host boundary claims no atomic write, fsync, permissions, or path hardening. |
| `Uwueave/Preo/StateProgram.lean` | The explicit application-state binding for a typed query: an author supplies `State → Expr.Env Γ` and a finite `stateReach`; `envReach` is exactly its image, `mem_envReach_iff` characterizes membership, and `project_mem_envReach` deliberately has no converse without injectivity. Evaluation, cache construction, equality of projected environments, singleton exact results, six-status soundness, declaration, and reach-gated reporting all use that same projection. The list is authored analysis scope, not discovered or authenticated deployment reach. |
| `Uwueave/Preo/StateProgramSurface.lean` | Transactional parser-hard `preo_program`. `elabPreoProgramCore` emits predictable state/schema/raw/program/projection/reach/evaluation/cache/result/report names only after `Raw.infer`, required-command, and trust-floor checks succeed; malformed typing or any late failure restores the environment. Every projection, reach, future ID, resolution, and surface policy remains explicit—field names and runtime reach are never inferred. |
| `Uwueave/Preo/StateProgramSurfaceTests.lean` | Focused surface acceptance/refusal leaf. `journey_is_hand_program` pins the generated whole value to its hand-written `StateProgram`; fixtures exercise exact evaluation/cache/report membership, malformed and wrong-schema/projection refusals, out-of-reach report refusal, and transactional name reuse after failure. It is a test module imported by Audit, not a new production command facade. |
| `Uwueave/Preo/PlanningSurface.lean` | Transactional parser-hard `preo_plan` over one explicit bounded action universe and repair catalog. Selected mode retains the engine witness, exact plan/profile, all five schedule currencies, all eight repair-price axes, structural coupling, and a budget over that exact selected plan; refusal mode retains the schedule/repair evidence for the same finite problem. Duplicate/oversized universes, wrong selections/names, and late failures roll back. No scalar price conversion, liveness claim, or search outside the authored catalogs is introduced. |
| `Uwueave/Preo/DerivedProgram.lean` | The positive semantic bridge from intrinsically typed expressions to the repository's reusable judgements. A retained `MergeSafe` proof is exactly a `JoinHom`; `Program.specification` is total without claiming singleton outcomes coordinate freely; explicit `WorldDecoder` locality carries reads/holes into `DerivedDocument`; and the existing incremental cache supplies proof-tied updates and zero-work off-dependency reuse. `Program.attributedDocument` derives exact candidates and complete typed `Expr.Hole` positions, with forgetful and join-hom laws. `Program.verifiedAttributedDocument` adds a `SourceAuthenticity` premise, and `verified_position_iff` retains its external `Authentic world source` witness; the ungated spelling is attribution only. Source mismatch, false positions, opaque-only holes, and literal-no-position fixtures prevent broader provenance claims. Negative Boolean/aggregation/opaque fixtures refuse the missing merge/locality proof rather than widening the language silently. |
| `Uwueave/Preo/BoundResult.lean` | Binds one checked state declaration to an exact named world future only through an explicit world-to-state projection, authored world reach, reach-preservation proof, and fresh six-status world soundness. `CertifiedReport` retains a certificate for the declaration's exact answer function and exact `WorldIndex`; selected disclosure exists only through `ExactBranch`. Wrong answer, different world, and out-of-reach reports are refuted. Projected-state equality never relabels delivery/extension or reuses a certificate across worlds. |
| `Uwueave/Preo/ObservedBoundResult.lean` | Proof-only deployment-observation adapter over `BoundResult`. `attachAtWorld` requires the caller's `ObservationBoundary.Authentic` witness, independent membership in a supplied running reach and the authored world reach, and the exact world-indexed certificate. `ObservedCertifiedReport.exact_alignment` retains those premises at one world/projected state; forged state/world, stale index, and out-of-running-reach theorems refuse substitution. It reads no runtime, equates no reaches, and constructs no authenticity, identity, or delivery evidence. |
| `Uwueave/Preo/ArtifactV3Data.lean` | Neutral append-only V3 data: distinct stable IDs for schema/query/result/program/certificate/world/resolution/surface/reason, exact positional query reads and holes, positive analysis tags, value-erased six-status/effect rows, visibility, optional exact-branch disclosure, and certificate future/world identity over an unchanged V2 base. These rows are first-order coordination metadata, not reconstructed programs, certificates, worlds, or proofs. |
| `Uwueave/Preo/ArtifactV3Diagnostics.lean` | Opt-in `Repr` instances for every neutral V3 ID and row. Diagnostics remain outside the data, validator, durable-codec, and renderer production closures. |
| `Uwueave/Preo/ArtifactV3Durable.lean` | Canonical format-v3 durable framing for `ArtifactV3Encoding`. `decodeArtifactV3_encode` and `decodeProjection_projectionBytes_append` pin payload and framed roundtrips including trailing journal bytes; V2 and V3 decoders mutually refuse the other's version. Decoding yields first-order data only, with no data-to-proof promotion or host persistence theorem. |
| `Uwueave/Preo/ArtifactV3Checked.lean` | The one-way proof-indexed V3 builder boundary. Query reads, holes, and positive analyses come from the exact `StateProgram`; used stable field IDs must exist in the exact checked base. Results are indexed by the exact query/future/world/certified report and derive status, visibility, resolution, and disclosure. Their canonical effect now maps `StatusEffects.inferredShapes`; `mem_effectOfDeclaration_iff` is a thin exact bridge to the shared semantic effect rather than a duplicate refinement implementation. Checked append retains exact registries and strict stable-ID preservation; no caller-authored semantic lists or decode-to-proof route exist. |
| `Uwueave/Preo/ArtifactV3Surface.lean` | Transactional parser-hard `preo_export_v3`. It accepts only an exact `StateProgram`, real `ObservedCertifiedReport`, its retained certificate, exact checked plan/budget/query/future/world, authored stable-ID maps, explicit work cap, and validation config. The surface derives result semantics and certificate rows through proof-indexed builders, preflights finite work and final validation, emits canonical V3 durable bytes, and trust-floor checks the admitted prefix. `exactObserved` prevents duck-typed lookalikes; all generated declarations roll back on late failure and the prefix is reusable. It infers no authenticity, reach, identity, authorization, I/O, or host durability. |
| `Uwueave/Preo/ArtifactV3Examples.lean` | Opt-in nonempty canonical V3 durable example over the full proof-originated V2 base. `full_roundtrip` pins reopen and `v2_refuses_full_v3` pins the version boundary without putting examples in the codec closure. |
| `Uwueave/Preo/ArtifactV3Fixtures.lean` | Small exact durable V3 framing goldens: the format tag is `(3, 161)` and `full_bytes_are_v3_only` combines canonical V3 reopen with V2 refusal. It is an audited theorem fixture, not a second codec. |
| `Uwueave/Preo/ProjectionV3Core.lean` | Data-only bounded V3 validation over the unchanged V2 validator. Before embedded V2 admission it checks every V3 outer-list bound, duplicate/strict row order, every V3 stable ID against `maxStableIdValue`, and hole depth/segment shape against `maxHolePathDepth`; it then checks schema and bidirectional query/result references, field/read/hole consistency, coherent positive analyses, canonical/downward effects, status admission, exact-only disclosure, and certificate future/world registries. Private `ValidatedProjectionV3` carries `base_exact`, so the separately validated V2 base cannot drift from the accepted V3 encoding. These V3 ID bounds do not claim to bound every decimal rendered by the embedded V2 base, and validation reconstructs no semantic source. |
| `Uwueave/Preo/ProjectionV3.lean` | Deterministic Rust DTO renderer over only `ValidatedProjectionV3`, reusing the exact validated V2 renderer and adding typed query/result/certificate rows. `renderRustSource_eq_of_encoding_eq` depends on the stored `base_exact` invariant; validation refusal is preserved. Generated Rust exposes linear query/result/certificate lookup and `result_for_query_row` only as neutral DTO conveniences: fabricated rows acquire no permit or proof. The production closure contains neutral data/core validation/rendering, not diagnostics, proof-indexed builders, examples, or giant fixtures. |
| `Uwueave/Preo/ProjectionV3Diagnostics.lean` | Opt-in `Repr` instances for V3 projections, bounds, errors, and validated values, explicitly composed from V2 and ArtifactV3 diagnostics rather than leaking them into `ProjectionV3Core`. |
| `Uwueave/Preo/ProjectionV3Examples.lean` | Opt-in V3 acceptance/refusal suite. The full encoding validates and exposes `full_validated_base_exact`; fixtures reject wrong query schema, query/result mismatch, reads/holes disagreement, dangling result/certificate futures and worlds, missing or inapplicable disclosure, duplicate or unordered rows, oversized stable IDs, malformed/deep hole paths, incoherent analyses, noncanonical effects/status/disclosure, and resource-bound overflow. All decisions are kernel-evaluated. |
| `Uwueave/Preo/ProjectionV3Fixtures.lean` | Exact small Rust row goldens for query, result, and certificate DTOs plus kernel-only full-renderer acceptance. Large full-source equality remains in the host compile gate to avoid max-recursion/proof-term blowups; no `native_decide` enters the audit floor. |
| `Uwueave/Preo/ArtifactInspectionV1.lean` | Pure bounded inspection of canonical V2/V3 frames and concatenated journals. A stack-safe outer-envelope scan delegates payload decoding to the Lean-owned durable codecs and structural admission to `ProjectionV2`/`ProjectionV3`, then returns deterministic diagnostic-only JSON with offsets and typed V3 rows. Input/record/reference bounds, torn/corrupt suffixes, wrong formats, and structural invalidity refuse the whole request. It proves neither denial-of-service resistance nor host-file authenticity/durability. |
| `Uwueave/Preo/ArtifactInspectionMain.lean` | Explicit binary-input CLI for frame/journal inspection via file or stdin. It is mapped and separately built/run but excluded from root and Audit aggregates because its root-level `main` cannot coexist with `ArtifactEmitMain.main`; the pure inspection library is root-imported and trust-gated. File reads and printed diagnostics confer no proof, permit, atomicity, fsync, permissions, or path-hardening guarantee. |
| `Uwueave/Preo/Quickstart.lean` | One executable custom-state journey: `preo_program` binds state to a typed derived query; `BoundResult` attaches the exact named world future and certificate; native protocol/planning produce one exact five-currency plan and budget; proof-indexed V3 builders retain stable query/result/future/world/certificate identity; ProjectionV3 validates; canonical bytes reopen and inspect. `v3_bytes_executable_exact` proves the stack-safe emitted bytes equal the logical durable frame. The 71,011-byte canary writes/reopens a frame and two-record journal and rejects wrong projection/future/certificate/plan/world, but host I/O remains a test, not a filesystem refinement theorem. |
| `Uwueave/RuntimeAuthV4.lean` | A staged authenticated FORMAT-v4 record model, deliberately not wired into the shipping v3 execution entry point. Canonical signed bytes bind document/genesis, algorithm, issuer/epoch/nonce, stable ids, and every projected `Exec.Op` field; bounded decoding, shape checks, exact replay/collision classification, verification and resolver premises, layered outcomes, and nonempty versioned responses stay separate. The narrow exported `decodeCanonicalKernel` now performs only bounded canonical syntax classification and proved re-encoding, with exact one-byte tags for all five refusals. Substitution, collision, and real Rust-FFI codec fixtures are concrete. No shape admission, cryptographic hardness, authorization, membership, execution, append, or durability theorem is claimed. |
| `Uwueave/RuntimeAuthV4Kernel.lean` | The narrow context-bound admission-projection kernel. Request kind 3 signs every legacy move field plus a nonempty opaque context commitment and is byte-separated from legacy request kind 1, layered response kind 2, and projection response kind 4. Bounded canonical decoding, eight nonempty shape checks, and exact FORMAT-v3 host-width checks yield a self-decoding neutral projection that retains the canonical request, signing bytes, signature, context, stable IDs, and every execution lane; 16 distinct refusal tags roundtrip injectively. The exported endpoint performs none of context interpretation, signature verification, stable-ID resolution, nonce freshness, authority, membership, execution, or persistence. |
| `Uwueave/RuntimeAuthV4AdmissionTraceKernel.lean` | The exported, fail-closed checker for the host's bounded admission certificate. It parses the canonical v2 certificate, recomputes and compares the cited kind-4 projection and FORMAT-v3 replay observations, enforces dense execution-node/index binding, and returns one validation byte. This is a translation/refinement check over supplied provider and runtime observations, not cryptographic verification, authority, membership, freshness, persistence, or filesystem evidence. |
| `Uwueave/Preo/RuntimeAuthV4Data.lean` | Neutral first-order manifest-sidecar rows mirroring every signed-move field plus cited grant scope and authored context identities/roster/participants. Stable IDs and digests are opaque bytes, not hashes or authority. `schema` belongs to the untrusted host projection; the durable outer format is the sole byte-level sidecar version. |
| `Uwueave/Preo/RuntimeAuthV4Checked.lean` | One-way construction from the exact existing `RuntimeAuthV4.SignedRequest`, `ReadyForExecution`, a live cited-grant/scope receipt, and finite context receipt. UInt fields only widen through `toNat`; `sourceSigningBytes_exact` retains the old canonical signing message, which is explicitly not the sidecar frame. Ready's authority/membership predicates remain independent premises; the grant receipt proves no holder possession, and authored context digests/origin/version are not verified. Decoded rows never reconstruct proof. |
| `Uwueave/Preo/RuntimeAuthV4Durable.lean` | Canonical version/domain-framed bytes for the neutral manifest sidecar, with exact prefix/whole-frame roundtrips and bounded whole-frame refusal. Its `(4,162)` durable envelope is **not** the existing `UWV4` request wire and must never be submitted as request or signing bytes. Prefix decoding preserves journal suffixes; exact and bounded decoding reject trailing, malformed, oversized, or changed-format frames while returning data only. |
| `Uwueave/Preo/RuntimeAuthV4ProjectionCore.lean` | Data-only sidecar validation: schema, byte/list/Nat bounds, UInt8/UInt64 widths, nonempty identities, canonical strict roster/participant order, exact cite/grant reference and child scope, issuer membership, and participant subset. Private `ValidatedProjection` carries structural admission only—no signature, grant, membership, history, digest, or storage proof. |
| `Uwueave/Preo/RuntimeAuthV4Projection.lean` | Deterministic Rust DTO rendering from only the private validated sidecar. Decimal strings avoid host integer truncation and byte identities remain exact slices; lookup conveniences are neutral. `renderRustSource_eq_of_manifest_eq` and `validateAndRender_error` preserve exact accepted data and refusal. Generated Rust is not a verifier or permit. |
| `Uwueave/Preo/RuntimeAuthV4Examples.lean` | Opt-in proof-originated full sidecar and adversarial validation suite. It pins exact request-field/signing-byte preservation and rejects wrong schema/grant/scope, noncanonical or outsider membership, empty identities, width errors, and inconsistent node references. The fixture verifier/authority predicates are explicit toy premises. |
| `Uwueave/Preo/RuntimeAuthV4Fixtures.lean` | Golden sidecar metadata: exact 369-byte frame, prefix `[213,74,4,162]`, exact Lean reopen, and host SHA-256 regression label `a9f32051b0e1e328ab08b253a808ba54cc5c4a4e9cb2b5d2550c3811cf03b819`. The digest is a test label, not a cryptographic theorem; this opt-in leaf never enters the runtime object closure. |
| `Uwueave/RuntimeInit.lean` | The declaration- and data-free native initializer root. Its six imports (`Exec`, `SeqKernel`, `EraKernel`, `Preo/ArtifactJournalKernel`, `RuntimeAuthV4Kernel`, and `RuntimeAuthV4AdmissionTraceKernel`) are the single source of truth for the Rust-linked Lean object graph; Lake derives their transitive module/object closure, and the C shim calls only this root initializer. Diagnostics, checked artifact constructors, examples, and unrelated proof modules stay outside that closure unless a runtime kernel imports them. |

## Keystone ledger

The two axes from the paragraph above, per marquee keystone. Names are as cited
in the rows above (namespace prefix omitted where the module is the row's).
Reachability is only for negative results — clashes and anomaly exhibits — and
each `Live` / `LatticeOnly` tag cites nothing beyond the named module's own
docstrings (upgraded by `CausalReach` theorems where those supersede them);
`—` marks rows the axis does not apply to. Every row is covered by
`#audit_floor`'s total gate — there is no per-row trust column to read. The
table currently holds 731 rows:

| Theorem | Module | Generality | Reachability |
|---|---|---|---|
| `escalation_witness` | Confluence | ∀-general | — |
| `leq_iff_merge_eq` | Confluence | ∀-general | — |
| `join_xy_xz` | Confluence | ∀-general | — |
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
| `mem_evalPositions` | Holes | ∀-general | — |
| `evalPositions_hom` | Holes | ∀-general | — |
| `evalPositions_nil` | Holes | ∀-general | — |
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
| `flatMap_nodup_of_nodup_of_pairwise_disjoint` | ListProofs | ∀-general | — |
| `flatMap_count_le_one_of_nodup_of_pairwise_disjoint` | ListProofs | ∀-general | — |
| `sublist_flatMap_of_mem` | ListProofs | ∀-general | — |
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
| `WordCodec.foldlPushWord_get` | ExecRefine | ∀-general | — |
| `FixedWidth.flatMap_getElem?_eq` | ExecRefine | ∀-general | — |
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
| `minAlong_eq_listMin` | CoordEffect | ∀-general | — |
| `optimum_compose_achieved` | CoordEffect | ∀-general | — |
| `pin_session_costs_exactly_one` | CoordEffect | finite-story | — |
| `eraReplay_same_sets` | EraKernel | ∀-general | — |
| `duel_response_words` | EraKernel | finite-story | Live |
| `closed_iconfluent` | Evidence | ∀-general | — |
| `divergent_futures_force_nonexact` | Evidence | ∀-general | — |
| `render_retracts_when_a_new_source_appears` | Evidence | finite-story | Unknown |
| `monotonicity_and_finality_are_independent` | Evidence | finite-story | — |
| `mem_positionCandidates` | Evidence | ∀-general | — |
| `positionCandidates_hom` | Evidence | ∀-general | — |
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
| `statusOf_eq_iff` | ResultStatus | ∀-general | — |
| `segmented_iff_properColoring` | SeamColoring | ∀-general | — |
| `argMin_le_of_mem` | SeamColoring | ∀-general | — |
| `argMin_first_tie_fixture` | SeamColoring | finite-story | — |
| `pin_synthesizeSeam_isSome` | SeamColoring | finite-story | — |
| `coloring_alone_does_not_segment` | SeamColoring | finite-story | Unknown |
| `Clash.not_iconfluent` | Tactics/Core | ∀-general | — |
| `findClash_none` | Tactics/Core | ∀-general | — |
| `classifyIn?_sound` | Tactics/Verdict | ∀-general | — |
| `classifyFinite_isFree_iff` | Tactics/Verdict | ∀-general | — |
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
| `forgetPositions_deriveAttributedDoc` | DerivedDocument | ∀-general | — |
| `deriveAttributedDoc_candidate_iff` | DerivedDocument | ∀-general | — |
| `deriveAttributedDoc_position_iff` | DerivedDocument | ∀-general | — |
| `deriveAttributedDoc_hom` | DerivedDocument | ∀-general | — |
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
| `Scenario.edgesOfPaths_eq_flatMap` | ForkGrade | ∀-general | — |
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
| `Internal.withEnvTransaction` (def) | Preo/Elab/Internal | ∀-general | — |
| `Declaration.elabPreoDeclCore` (def) | Preo/Elab/Declaration | ∀-general | — |
| `Export.elabPreoExportCore` (def) | Preo/Elab/Export | ∀-general | — |
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
| `historySafeFrom_iff` | Histories | ∀-general | — |
| `History.Coherent.induction` | Histories | ∀-general | — |
| `spend_reachable` | Histories | parametric | — |
| `counter_not_historySafeFrom` | Histories | finite-story | LatticeOnly |
| `lock_historySafeFrom` | Histories | parametric | — |
| `counter_historySafe_true_and_not_mergeClosed` | Histories | finite-story | LatticeOnly |
| `unlinked_optimum_is_two` | Cost | finite-story | — |
| `unlinkedFinitePlanSpace_agrees_with_exact_optimum` | Budget | finite-story | — |
| `oneShotHole_partially_glues` | Gluing | parametric | — |
| `every_oneShot_gluing_seam_separates_singletons` | Gluing | ∀-general | — |
| `oneshot_orthogonal_to_gluing` | Gluing | parametric | — |
| `RestrictsReachability` (def) | Repair | ∀-general | — |
| `balanceEscrow_price_and_delta` | RepairMenu | finite-story | — |
| `ctxEquiv_iff_agree_window` | TextSummary | ∀-general | — |
| `saturatedExcept_observable` | TextSummary | ∀-general | — |
| `minimumSeam_search_total` | SeamColoring | ∀-general | — |
| `pin_minimum_is_exact` | SeamColoring | finite-story | — |
| `minimumMenuSynthesis_total` | MenuTotality | ∀-general | — |
| `pin_minimum_menu_is_exact` | MenuTotality | finite-story | — |
| `constructedMergeWork_le_of_recovery_bound` | Recoverable | ∀-general | — |
| `cheapLockConstructedMerge_work_le_one` | Recoverable | parametric | — |
| `paddedLockConstructedMerge_both_moved_work` | Recoverable | parametric | — |
| `coordinationFree_iff_historyMonotone_and_fiberDirected` | Specification | ∀-general | — |
| `invariant_coordinationFree_iff` | Specification | ∀-general | — |
| `zeroAbsent_not_historyMonotone` | Specification | finite-story | LatticeOnly |
| `Annotation.axes_retained` | Protocol | ∀-general | — |
| `elaborated_composition_uses_one_strategy` | Protocol | ∀-general | — |
| `no_ast_crossing_count_determines_least_meetings` | Protocol | finite-story | — |
| `CheckedInvariant.toArtifact` (def) | Preo/ArtifactChecked | ∀-general | — |
| `ArtifactEncoding.decode_canonicalEncoding` | Preo/ArtifactData | ∀-general | — |
| `certificate_sound_restrict` | Preo/Future | ∀-general | — |
| `same_state_different_worlds_block_certificate_reuse` | Preo/Future | finite-story | — |
| `era_certificate_is_satisfiable_and_refutable` | Preo/Future | finite-story | — |
| `DeclarationBundle.addCertifiedFuture` (def) | Preo/Export | ∀-general | — |
| `DeclarationBundle.addElaboration` (def) | Preo/Export | ∀-general | — |
| `DeclarationBundle.project` (def) | Preo/Export | ∀-general | — |
| `Examples.whole_export_roundtrips` | Preo/Export | finite-story | — |
| `flat_frontier_loses_position` | Frontier | finite-story | — |
| `advance_without_delivery_is_unsound` | Frontier | finite-story | — |
| `world_complete_values_stable` | Frontier | ∀-general | — |
| `grant_event_domain_separated` | Authenticity | ∀-general | — |
| `authenticity_violation_extracts_forgery` | Authenticity | ∀-general | — |
| `accepted_antitone_revocation` | Authenticity | ∀-general | — |
| `fork_evidence_permanent` | Byzantine | ∀-general | — |
| `fork_evidence_attributes_author` | Byzantine | ∀-general | — |
| `authentic_issuance_preserves_finality` | Byzantine | ∀-general | — |
| `forged_announced_id_breaks_era_finality` | Byzantine | finite-story | Unknown |
| `decodeValue_encodeValue_append` | Durable | ∀-general | — |
| `recover_crashPrefix` | Durable | ∀-general | — |
| `recover_crashPrefix_monotone` | Durable | ∀-general | — |
| `wellFormed_iconfluent` | EvidenceGraph | ∀-general | — |
| `encodeEvidenceGraph_joinHom` | EvidenceGraph | ∀-general | — |
| `flat_encodeEvidence_is_projection` | EvidenceGraph | ∀-general | — |
| `danglingAttribution_is_malformed` | EvidenceGraph | finite-story | — |
| `IConfluentIn` (def) | MergeModel | ∀-general | — |
| `BaseDecision.Valid` (def) | MergeModel | ∀-general | — |
| `VersionCert` (def) | HistoryBase | ∀-general | — |
| `SameShape.classify` | HistoryPolicy | ∀-general | — |
| `sufficientKey_iff_sufficientFor` | CertificateScope | ∀-general | — |
| `approximate_embed` | ChoreoRec | ∀-general | — |
| `projection_sound_approx` | ChoreoRec | ∀-general | — |
| `guardedBarrierLoop_progresses` | ChoreoRec | finite-story | — |
| `mismatched_barrier_is_deadlocked` | ChoreoRec | finite-story | Unknown |
| `delivery_projects` | WorldContext | ∀-general | — |
| `delivery_lifts` | WorldContext | ∀-general | — |
| `same_world_axes_hide_context` | WorldContext | finite-story | — |
| `projected_delivery_does_not_lift_without_context` | WorldContext | finite-story | — |
| `move_domain_separated` | Authenticity | ∀-general | — |
| `signingMessage_move_injective` | Authenticity | ∀-general | — |
| `authenticIssuer_to_signatureAuthentic` | AuthenticatedAdmission | ∀-general | — |
| `honest_equivocation_attributes_author` | AuthenticatedAdmission | finite-story | — |
| `mallory_fails_holder_even_when_gate_passes` | AuthenticatedAdmission | finite-story | — |
| `valid_signature_over_revoked_grant_fails_authorization` | AuthenticatedAdmission | finite-story | — |
| `ProfileUpperBound.toUpperBound` (def) | Scheduling | ∀-general | — |
| `ProfileUpperBound.comp` (def) | Scheduling | ∀-general | — |
| `meeting_floor_does_not_entail_profile_acceptance` | Scheduling | finite-story | — |
| `elaborate_exactProfileUpperBound_plan` | Protocol | ∀-general | — |
| `SearchResult.bound_exists_of_isFound` | ScheduleSynthesis | ∀-general | — |
| `SearchResult.exhaustive_of_not_isFound` | ScheduleSynthesis | ∀-general | — |
| `same_crossings_opposite_catalog_verdicts` | ScheduleSynthesis | finite-story | — |
| `selection_is_policy_dependent` | ScheduleSynthesis | finite-story | — |
| `checkedVerdict_isFree` | Preo/Classification | ∀-general | — |
| `no_checkedVerdict_licence_of_answer_none` | Preo/Classification | ∀-general | — |
| `addClassification_free_agrees_with_addVerdict` | Preo/Export | finite-story | — |
| `addClassification_seam_agrees_with_addVerdict` | Preo/Export | finite-story | — |
| `unresolved_classification_has_no_export_licence` | Preo/Export | finite-story | — |
| `Catalog.minimum_le_of_applicable` | RepairSynthesis | ∀-general | — |
| `Catalog.minimum_none_exhaustive` | RepairSynthesis | ∀-general | — |
| `Examples.finds_least_applicable` | RepairSynthesis | finite-story | — |
| `Examples.refusal_is_exhaustive_for_catalog` | RepairSynthesis | finite-story | — |
| `stackSafeEncodeData_eq` | Preo/ArtifactDurableCore | ∀-general | — |
| `stackSafeEncodeFrame_eq` | Preo/ArtifactDurableCore | ∀-general | — |
| `stackSafeEncodeValue_eq` | Preo/ArtifactDurableCore | ∀-general | — |
| `decodeValue_stackSafeEncodeValue_append` | Preo/ArtifactDurableCore | ∀-general | — |
| `decodeProjection_projectionBytes_append` | Preo/ArtifactDurableCore | ∀-general | — |
| `Examples.overlong_artifact_refused` | Preo/ArtifactDurable | finite-story | — |
| `Examples.wrong_projection_tags_are_refused` | Preo/ArtifactDurable | finite-story | — |
| `Examples.two_frames_then_torn_third` | Preo/ArtifactDurable | finite-story | — |
| `Examples.artifact_example_validates` | Preo/ProjectionV1Examples | finite-story | — |
| `Examples.duplicate_field_refused` | Preo/ProjectionV1Examples | finite-story | — |
| `Examples.noncanonical_profile_refused` | Preo/ProjectionV1Examples | finite-story | — |
| `Examples.wrong_schema_refused` | Preo/ProjectionV1Examples | finite-story | — |
| `groupedCarrierSurface_state_is_weaveDoc` | Preo/Demo | finite-story | — |
| `groupedCarrierSurface_core_seed_is_core₀` | Preo/Demo | finite-story | — |
| `renderRustSource_eq_of_encoding_eq` | Preo/ProjectionV1 | ∀-general | — |
| `validateAndRender_error` | Preo/ProjectionV1 | ∀-general | — |
| `Examples.unbounded_decimal_fixture` | Preo/ProjectionV1Fixtures | finite-story | — |
| `Examples.empty_projection_lines_fixture` | Preo/ProjectionV1Fixtures | finite-story | — |
| `coalescedProfileBudget_is_hand_witness` | Preo/Demo | finite-story | — |
| `coalescedProfileBudget_retains_five_currencies` | Preo/Demo | finite-story | — |
| `no_crossing_count_accepts_profile_budget` | Preo/Demo | parametric | — |
| `meeting_floor_does_not_accept_profile_budget` | Preo/Demo | finite-story | — |
| `reaches_iff_bounded` | FiniteHistory | ∀-general | — |
| `mem_commonCandidates_iff` | FiniteHistory | ∀-general | — |
| `toDecision_valid` | FiniteHistory | ∀-general | — |
| `policyAccepted_iff` | FiniteHistory | ∀-general | — |
| `sweepEntries_complete` | FiniteHistory | ∀-general | — |
| `Term.eval_ext` | Preo/Expr | ∀-general | — |
| `Term.dependency_iff_positional_hole` | Preo/Expr | ∀-general | — |
| `MergeSafe.sound` | Preo/Expr | ∀-general | — |
| `MonotoneSafe.sound` | Preo/Expr | ∀-general | — |
| `negatedMembership_not_monotone` | Preo/Expr | finite-story | — |
| `summedFields_not_preservesMerge` | Preo/Expr | finite-story | — |
| `malformed_not_classified` | Preo/Expr | finite-story | — |
| `opaque_not_auto_mergeSafe` | Preo/Expr | finite-story | — |
| `projection_sound` | ChoreoChoice | ∀-general | — |
| `fixture_observations_disagree` | ChoreoChoice | finite-story | — |
| `twoParty_remote_missing_label` | ChoreoChoice | finite-story | — |
| `singleton_clashes_iff` | ClashGraph | ∀-general | — |
| `c5_forces_three_domains` | ClashGraph | parametric | — |
| `LeaveOneOutObstruction.forces_domains` | ClashGraph | ∀-general | — |
| `legalUnderComposition_iff_ancestralConfluent` | CompositeDelta | ∀-general | — |
| `cheapLockAlgebra_ancestralConfluent` | CompositeDelta | parametric | — |
| `counter_not_legalUnderComposition` | CompositeDelta | finite-story | — |
| `signature_eq_iff` | ContextCompiler | ∀-general | — |
| `sufficient_refines_signature` | ContextCompiler | ∀-general | — |
| `restricted_contexts_can_coarsen` | ContextCompiler | finite-story | — |
| `incremental_correct` | Preo/Incremental | ∀-general | — |
| `off_dependency_zero` | Preo/Incremental | ∀-general | — |
| `custom_without_law_recomputes` | Preo/Incremental | ∀-general | — |
| `Examples.full_export_validates` | Preo/ProjectionV2Examples | finite-story | — |
| `Examples.action_profile_lie_refused` | Preo/ProjectionV2Examples | finite-story | — |
| `Examples.uncovered_obligation_refused` | Preo/ProjectionV2Examples | finite-story | — |
| `Examples.exceeded_budget_limit_refused` | Preo/ProjectionV2Examples | finite-story | — |
| `renderRustSource_eq_of_encoding_eq` | Preo/ProjectionV2 | ∀-general | — |
| `infer_is_least` | StatusEffects | ∀-general | — |
| `statusOf_totalSound6` | StatusEffects | ∀-general | — |
| `TotalSoundEvaluator6.semanticsAt` | StatusEffects | ∀-general | — |
| `closedForkAsOpen_not_total` | StatusEffects | finite-story | — |
| `continuously_enabled_eventually_occurs` | Temporal | ∀-general | — |
| `StrongFair.weakFair` | Temporal | ∀-general | — |
| `starvedPendingTrace_not_weakFair` | Temporal | finite-story | — |
| `fair_bob_delivery_exits_pending` | Temporal | parametric | — |
| `apply_preserves` | WovenEdit | ∀-general | — |
| `runCommands_preserves` | WovenEdit | ∀-general | — |
| `demoCommands_wellFormed` | WovenEdit | finite-story | — |
| `graphSweep_complete` | HistoryEngine | ∀-general | — |
| `SemanticDecision.result?_some_iff_scope` | HistoryEngine | ∀-general | — |
| `ResidualDiamond.repeated_delivery_converges` | HistoryEngine | ∀-general | — |
| `counter_length_two_refusal_fixture` | HistoryEngine | finite-story | — |
| `checked_atomic_reopen` | PersistentRuntime | ∀-general | — |
| `checkpoint_suffix_replay_equiv` | PersistentRuntime | ∀-general | — |
| `reopenImage_cache_irrelevant` | PersistentRuntime | ∀-general | — |
| `snapshot_only_recovery_unsafe` | PersistentRuntime | finite-story | — |
| `validateOne_projectionBytes` | Preo/ArtifactJournalKernel | ∀-general | — |
| `scan_stops_at_first_refusal` | Preo/ArtifactJournalKernel | ∀-general | — |
| `scan_torn_final` | Preo/ArtifactJournalKernel | ∀-general | — |
| `Fixtures.corrupt_middle_fixture` | Preo/ArtifactJournalKernel | finite-story | — |
| `mem_actionChoices_iff_sublist` | Preo/Planning | ∀-general | — |
| `actionChoices_length` | Preo/Planning | ∀-general | — |
| `Result.coupled_exists_of_isSelected` | Preo/Planning | ∀-general | — |
| `Result.refusal_scope` | Preo/Planning | ∀-general | — |
| `Examples.native_protocol_surface_is_plannable` | Preo/Planning | finite-story | — |
| `native_fixture_retains_exact_demands` | Preo/ProtocolSurface | finite-story | — |
| `crossings_can_still_exceed_meetings` | Preo/ProtocolSurface | finite-story | — |
| `meetings_can_still_exceed_crossings` | Preo/ProtocolSurface | finite-story | — |
| `CheckedDeclaration.effect_least` | Preo/ResultProgram | ∀-general | — |
| `CheckedDeclaration.renderer_honest` | Preo/ResultProgram | ∀-general | — |
| `ExactSnapshot.totalSound` | Preo/ResultProgram | ∀-general | — |
| `CheckedDeclaration.semanticsAt` | Preo/ResultProgram | ∀-general | — |
| `CheckedReport.says_semantics` | Preo/ResultProgram | ∀-general | — |
| `CheckedReport.refuses_wrong_resolution` | Preo/ResultProgram | ∀-general | — |
| `ReachReport.effect_supports` | Preo/ResultProgram | ∀-general | — |
| `ReachReport.refuses_out_of_reach` | Preo/ResultProgram | ∀-general | — |
| `ObservedReport.authentic_site` | Preo/ResultProgram | ∀-general | — |
| `ObservedReport.refuses_inauthentic` | Preo/ResultProgram | ∀-general | — |
| `CheckedReport.refuses_wrong_site` | Preo/ResultProgram | ∀-general | — |
| `open_report_refuses_lie_about_disclosure` | Preo/ResultProgram | finite-story | — |
| `not_total` | StatusSemanticsAcceptance | finite-story | — |
| `typed_snapshot_effect_supported` | StatusSemanticsAcceptance | finite-story | — |
| `observation_refuses_wrong_state` | StatusSemanticsAcceptance | finite-story | — |
| `semanticEncoding_eq_generated` | Preo/ArtifactEmit | finite-story | — |
| `bytesImpl_eq_bytes` | Preo/ArtifactEmit | parametric | — |
| `byteArray_data_toList` | Preo/ArtifactEmit | parametric | — |
| `signingBytesV4_injective` | RuntimeAuthV4 | ∀-general | — |
| `bounded_roundtrip` | RuntimeAuthV4 | ∀-general | — |
| `decodeCanonicalKernelBytes_accepted` | RuntimeAuthV4 | ∀-general | — |
| `decodeCanonicalKernelBytes_refused` | RuntimeAuthV4 | ∀-general | — |
| `compareNonce_collision_iff` | RuntimeAuthV4 | ∀-general | — |
| `toExecOp_exact_fields` | RuntimeAuthV4 | ∀-general | — |
| `fixture_document_substitution_refused` | RuntimeAuthV4 | finite-story | — |
| `contextRequest_roundtrip` | RuntimeAuthV4Kernel | ∀-general | — |
| `context_commitment_is_signed` | RuntimeAuthV4Kernel | ∀-general | — |
| `context_bounded_roundtrip` | RuntimeAuthV4Kernel | ∀-general | — |
| `AdmissionProjection.ofRequest_exact` | RuntimeAuthV4Kernel | ∀-general | — |
| `admissionResponse_roundtrip` | RuntimeAuthV4Kernel | ∀-general | — |
| `encodeAdmissionResponse_injective` | RuntimeAuthV4Kernel | ∀-general | — |
| `decode_projectAdmissionBytes` | RuntimeAuthV4Kernel | ∀-general | — |
| `distinct_refusals_have_distinct_responses` | RuntimeAuthV4Kernel | ∀-general | — |
| `Program.inferred` | Preo/Expr | ∀-general | — |
| `updateProgramCache_correct` | Preo/Incremental | ∀-general | — |
| `TypedResult.totalSound` | Preo/Incremental | ∀-general | — |
| `semanticSurface_next_report_policy_exact` | Preo/Demo | finite-story | — |
| `refused_impossible` | HistoryRuntime | ∀-general | — |
| `decideTotal_valid` | HistoryRuntime | ∀-general | — |
| `higherSweep_complete` | HistoryRuntime | ∀-general | — |
| `appendDag_reaches_inl` | HistoryRuntime | ∀-general | — |
| `lockForkAppended_coherent` | HistoryRuntime | finite-story | — |
| `sameEventSet_converges` | HistoryRuntime | ∀-general | — |
| `DeliveryState.empty_valid` | HistoryRuntime | ∀-general | — |
| `drain_pending_length_le` | HistoryRuntime | ∀-general | — |
| `receive_success_valid` | HistoryRuntime | ∀-general | — |
| `receiveAll_success_valid` | HistoryRuntime | ∀-general | — |
| `SettledSameEventSet.view_eq` | HistoryRuntime | ∀-general | — |
| `runtime_orders_converge` | HistoryRuntime | finite-story | — |
| `runtime_pending_collision_refused` | HistoryRuntime | finite-story | — |
| `orderAgreement_iff_selector_symmetric_at` | HistoryRuntime | ∀-general | — |
| `asymmetric_but_convergent` | HistoryRuntime | finite-story | — |
| `historySchema_step_eq_some_iff` | PersistentHistoryRuntime | ∀-general | — |
| `applyEvent_retry` | PersistentHistoryRuntime | ∀-general | — |
| `applyEvent_collision` | PersistentHistoryRuntime | ∀-general | — |
| `checkpoint_suffix_replay` | PersistentHistoryRuntime | ∀-general | — |
| `fork_arrival_orders_converge` | PersistentHistoryRuntime | finite-story | — |
| `emptyDeliveryCursor_coherent` | PersistentHistoryRuntime | ∀-general | — |
| `deliverySchema_step_eq_some_iff` | PersistentHistoryRuntime | ∀-general | — |
| `stableCausalCursor_coherent` | PersistentHistoryRuntime | finite-story | — |
| `stableReverseCursor_coherent` | PersistentHistoryRuntime | finite-story | — |
| `stable_replays_converge` | PersistentHistoryRuntime | finite-story | — |
| `stable_reverse_checkpoint_suffix_exact` | PersistentHistoryRuntime | finite-story | — |
| `mem_envReach_iff` | Preo/StateProgram | ∀-general | — |
| `project_mem_envReach` | Preo/StateProgram | ∀-general | — |
| `totalSound` | Preo/StateProgram | ∀-general | — |
| `declaration_evaluate` | Preo/StateProgram | ∀-general | — |
| `elabPreoProgramCore` (def) | Preo/StateProgramSurface | ∀-general | — |
| `journey_is_hand_program` | Preo/StateProgramSurfaceTests | finite-story | — |
| `selected_is_engine_witness` | Preo/PlanningSurface | finite-story | — |
| `selected_profile_is_exact` | Preo/PlanningSurface | finite-story | — |
| `selected_price_is_full` | Preo/PlanningSurface | finite-story | — |
| `selected_coupling_is_exact` | Preo/PlanningSurface | finite-story | — |
| `budget_is_selected_profile` | Preo/PlanningSurface | finite-story | — |
| `schedule_refusal_is_exact` | Preo/PlanningSurface | finite-story | — |
| `repair_refusal_is_exact` | Preo/PlanningSurface | finite-story | — |
| `preservesMerge_iff_joinHom` | Preo/DerivedProgram | ∀-general | — |
| `Program.joinHom` | Preo/DerivedProgram | ∀-general | — |
| `Program.specification_total` | Preo/DerivedProgram | ∀-general | — |
| `Program.evalWorld_eq_of_agreeOnReads` | Preo/DerivedProgram | ∀-general | — |
| `Program.document_joinHom` | Preo/DerivedProgram | ∀-general | — |
| `Program.forget_attributedDocument` | Preo/DerivedProgram | ∀-general | — |
| `Program.attributed_candidate_iff` | Preo/DerivedProgram | ∀-general | — |
| `Program.attributed_position_iff` | Preo/DerivedProgram | ∀-general | — |
| `Program.attributedDocument_joinHom` | Preo/DerivedProgram | ∀-general | — |
| `Program.verified_position_iff` | Preo/DerivedProgram | ∀-general | — |
| `constantSeven_source_mismatch` | Preo/DerivedProgram | finite-story | — |
| `Program.update_correct` | Preo/DerivedProgram | ∀-general | — |
| `Program.update_off_dependency_zero` | Preo/DerivedProgram | ∀-general | — |
| `liftResolution_identity` | Preo/BoundResult | ∀-general | — |
| `WorldBinding.declaration_evaluate` | Preo/BoundResult | ∀-general | — |
| `WorldBinding.CertifiedReport.certificate_answers_declaration` | Preo/BoundResult | ∀-general | — |
| `WorldBinding.CertifiedReport.refuses_different_world` | Preo/BoundResult | ∀-general | — |
| `WorldBinding.CertifiedReport.ExactBranch.says` | Preo/BoundResult | ∀-general | — |
| `WorldBinding.CertifiedReport.ExactBranch.disclosure_exact` | Preo/BoundResult | ∀-general | — |
| `WorldBinding.refuses_wrong_certificate_answer` | Preo/BoundResult | ∀-general | — |
| `WorldBinding.refuses_out_of_world_reach` | Preo/BoundResult | ∀-general | — |
| `ObservedCertifiedReport.observation` | Preo/ObservedBoundResult | ∀-general | — |
| `ObservedCertifiedReport.exact_alignment` | Preo/ObservedBoundResult | ∀-general | — |
| `ObservedCertifiedReport.refuses_forged_state` | Preo/ObservedBoundResult | ∀-general | — |
| `ObservedCertifiedReport.refuses_forged_world` | Preo/ObservedBoundResult | ∀-general | — |
| `ObservedCertifiedReport.refuses_stale_index` | Preo/ObservedBoundResult | ∀-general | — |
| `refuses_out_of_running_reach` | Preo/ObservedBoundResult | ∀-general | — |
| `decodeArtifactV3_encode` | Preo/ArtifactV3Durable | ∀-general | — |
| `decodeProjection_projectionBytes_append` | Preo/ArtifactV3Durable | ∀-general | — |
| `v2_decoder_refuses_v3` | Preo/ArtifactV3Durable | ∀-general | — |
| `v3_decoder_refuses_v2` | Preo/ArtifactV3Durable | ∀-general | — |
| `CheckedQuery.toRow_reads` | Preo/ArtifactV3Checked | ∀-general | — |
| `CheckedQuery.toRow_holes` | Preo/ArtifactV3Checked | ∀-general | — |
| `CheckedQuery.read_field_mem` | Preo/ArtifactV3Checked | ∀-general | — |
| `mem_effectOfDeclaration_iff` | Preo/ArtifactV3Checked | ∀-general | — |
| `CheckedResult.toExactRow_status` | Preo/ArtifactV3Checked | ∀-general | — |
| `append_preserves_strictIds` | Preo/ArtifactV3Checked | ∀-general | — |
| `workEstimate` (def) | Preo/ArtifactV3Surface | ∀-general | — |
| `exactObserved` (def) | Preo/ArtifactV3Surface | ∀-general | — |
| `certificateOfCheckedResult` (def) | Preo/ArtifactV3Surface | ∀-general | — |
| `addCertificateOfCheckedResult` (def) | Preo/ArtifactV3Surface | ∀-general | — |
| `elabPreoExportV3Core` (def) | Preo/ArtifactV3Surface | ∀-general | — |
| `full_roundtrip` | Preo/ArtifactV3Examples | finite-story | — |
| `v2_refuses_full_v3` | Preo/ArtifactV3Examples | finite-story | — |
| `format_golden` | Preo/ArtifactV3Fixtures | finite-story | — |
| `full_bytes_are_v3_only` | Preo/ArtifactV3Fixtures | finite-story | — |
| `ValidatedProjectionV3.base_exact` | Preo/ProjectionV3Core | ∀-general | — |
| `renderRustSource_eq_of_encoding_eq` | Preo/ProjectionV3 | ∀-general | — |
| `validateAndRender_error` | Preo/ProjectionV3 | ∀-general | — |
| `Examples.full_validates` | Preo/ProjectionV3Examples | finite-story | — |
| `Examples.full_validated_base_exact` | Preo/ProjectionV3Examples | finite-story | — |
| `Examples.wrong_query_schema_refused` | Preo/ProjectionV3Examples | finite-story | — |
| `Examples.mismatched_query_result_refused` | Preo/ProjectionV3Examples | finite-story | — |
| `Examples.query_reads_mismatch_refused` | Preo/ProjectionV3Examples | finite-story | — |
| `Examples.exact_without_disclosure_refused` | Preo/ProjectionV3Examples | finite-story | — |
| `Examples.pending_with_disclosure_refused` | Preo/ProjectionV3Examples | finite-story | — |
| `Examples.query_bound_refused` | Preo/ProjectionV3Examples | finite-story | — |
| `Examples.overdeep_hole_path_refused` | Preo/ProjectionV3Examples | finite-story | — |
| `Examples.invalid_hole_path_segment_refused` | Preo/ProjectionV3Examples | finite-story | — |
| `Examples.incoherent_analyses_refused` | Preo/ProjectionV3Examples | finite-story | — |
| `Examples.oversized_surface_id_refused` | Preo/ProjectionV3Examples | finite-story | — |
| `Examples.reordered_queries_refused` | Preo/ProjectionV3Examples | finite-story | — |
| `Examples.reordered_worlds_refused` | Preo/ProjectionV3Examples | finite-story | — |
| `Examples.reordered_results_refused` | Preo/ProjectionV3Examples | finite-story | — |
| `Examples.reordered_certificates_refused` | Preo/ProjectionV3Examples | finite-story | — |
| `Examples.noncanonical_analyses_refused` | Preo/ProjectionV3Examples | finite-story | — |
| `Examples.nondownward_effect_refused` | Preo/ProjectionV3Examples | finite-story | — |
| `Examples.status_outside_effect_refused` | Preo/ProjectionV3Examples | finite-story | — |
| `Examples.query_rust_golden` | Preo/ProjectionV3Fixtures | finite-story | — |
| `Examples.result_rust_golden` | Preo/ProjectionV3Fixtures | finite-story | — |
| `Examples.certificate_rust_golden` | Preo/ProjectionV3Fixtures | finite-story | — |
| `Examples.full_renderer_accepts` | Preo/ProjectionV3Fixtures | finite-story | — |
| `inspectJournal` (def) | Preo/ArtifactInspectionV1 | ∀-general | — |
| `inspectFrame` (def) | Preo/ArtifactInspectionV1 | ∀-general | — |
| `journey_exact` | Preo/Quickstart | finite-story | — |
| `journey_eval_exact` | Preo/Quickstart | finite-story | — |
| `certificate_is_for_exact_future_and_world` | Preo/Quickstart | finite-story | — |
| `protocol_is_exact` | Preo/Quickstart | finite-story | — |
| `plan_and_budget_are_exact` | Preo/Quickstart | finite-story | — |
| `checked_query_row_exact` | Preo/Quickstart | finite-story | — |
| `checked_result_and_certificate_rows_exact` | Preo/Quickstart | finite-story | — |
| `v3_artifact_validates` | Preo/Quickstart | finite-story | — |
| `v3_bytes_reopen_exact` | Preo/Quickstart | finite-story | — |
| `v3_bytes_executable_exact` | Preo/Quickstart | finite-story | — |
| `progressKind_not_ordinary` | AuthenticatedFrontier | ∀-general | — |
| `progressKind_ne_positionKind` | AuthenticatedFrontier | ∀-general | — |
| `AuthenticatedProgress.ofAuthenticIssuer` (def) | AuthenticatedFrontier | ∀-general | — |
| `AuthenticatedAdvance.toDeliveryAdvance` | AuthenticatedFrontier | ∀-general | — |
| `positionKind_ne_progressKind` | AuthenticatedWorldContext | ∀-general | — |
| `AuthenticatedPositionClaim.materialized` | AuthenticatedWorldContext | ∀-general | — |
| `ConsumptionReceipt.consumed_mono` | AuthenticatedWorldContext | ∀-general | — |
| `ConsumptionReceipt.used_after` | AuthenticatedWorldContext | ∀-general | — |
| `ConsumptionReceipt.unused_unchanged` | AuthenticatedWorldContext | ∀-general | — |
| `ConsumptionReceipt.preserves_wf` | AuthenticatedWorldContext | ∀-general | — |
| `AuthenticatedConsumingDelivery.projects_world_delivery` | AuthenticatedWorldContext | ∀-general | — |
| `AuthenticatedConsumingDelivery.progress_is_lawful` | AuthenticatedWorldContext | ∀-general | — |
| `authenticated_delivery_projects` | AuthenticatedWorldContext | finite-story | — |
| `accepted_forgery_not_promoted` | AuthenticatedWorldContext | finite-story | — |
| `stale_base_refuses_position` | AuthenticatedWorldContext | finite-story | — |
| `wrong_origin_refuses_position` | AuthenticatedWorldContext | finite-story | — |
| `consumed_token_not_reusable` | AuthenticatedWorldContext | finite-story | — |
| `refinesBool_eq_true_iff` | StatusEffects | ∀-general | — |
| `mem_allShapes` | StatusEffects | ∀-general | — |
| `mem_inferredShapes_iff` | StatusEffects | ∀-general | — |
| `schemaArrivalCallbacks` (def) | PersistentHistoryRuntime | ∀-general | — |
| `durableCallbacks_reverse_reopen_exact` | PersistentHistoryRuntime | ∀-general | — |
| `stableReversePrefixCursor_coherent` | PersistentHistoryRuntime | finite-story | — |
| `SignedMoveRow.ofRequest_signatureAlgorithm` | Preo/RuntimeAuthV4Checked | ∀-general | — |
| `SignedMoveRow.ofRequest_issuer` | Preo/RuntimeAuthV4Checked | ∀-general | — |
| `SignedMoveRow.ofRequest_keyEpoch` | Preo/RuntimeAuthV4Checked | ∀-general | — |
| `SignedMoveRow.ofRequest_lamport` | Preo/RuntimeAuthV4Checked | ∀-general | — |
| `GrantReceipt.toRow_id` | Preo/RuntimeAuthV4Checked | ∀-general | — |
| `CheckedManifest.toManifest_move` | Preo/RuntimeAuthV4Checked | ∀-general | — |
| `CheckedManifest.sourceSigningBytes_exact` | Preo/RuntimeAuthV4Checked | ∀-general | — |
| `decodeManifest_manifestBytes_append` | Preo/RuntimeAuthV4Durable | ∀-general | — |
| `decodeManifestExact_manifestBytes` | Preo/RuntimeAuthV4Durable | ∀-general | — |
| `decodeBounded_manifestBytes` | Preo/RuntimeAuthV4Durable | ∀-general | — |
| `decodeBounded_refuses_trailing` | Preo/RuntimeAuthV4Durable | ∀-general | — |
| `changed_format_refused` | Preo/RuntimeAuthV4Durable | ∀-general | — |
| `renderRustSource_eq_of_manifest_eq` | Preo/RuntimeAuthV4Projection | ∀-general | — |
| `validateAndRender_error` | Preo/RuntimeAuthV4Projection | ∀-general | — |
| `manifest_preserves_exact_request` | Preo/RuntimeAuthV4Examples | finite-story | — |
| `source_signing_bytes_are_exact` | Preo/RuntimeAuthV4Examples | finite-story | — |
| `validates` | Preo/RuntimeAuthV4Examples | finite-story | — |
| `wrong_schema_refused` | Preo/RuntimeAuthV4Examples | finite-story | — |
| `wrong_grant_refused` | Preo/RuntimeAuthV4Examples | finite-story | — |
| `noncanonical_roster_refused` | Preo/RuntimeAuthV4Examples | finite-story | — |
| `outsider_participant_refused` | Preo/RuntimeAuthV4Examples | finite-story | — |
| `wrong_algorithm_refused` | Preo/RuntimeAuthV4Examples | finite-story | — |
| `outside_scope_refused` | Preo/RuntimeAuthV4Examples | finite-story | — |
| `fixture_bytes_length` | Preo/RuntimeAuthV4Fixtures | finite-story | — |
| `fixture_bytes_format_prefix` | Preo/RuntimeAuthV4Fixtures | finite-story | — |
| `fixture_bytes_decode_exact` | Preo/RuntimeAuthV4Fixtures | finite-story | — |
| `CompleteAnnouncement.settled` | AuthenticatedEraCertificate | ∀-general | — |
| `Verification.payload_exact` | AuthenticatedEraCertificate | ∀-general | — |
| `Verification.wasIssued` | AuthenticatedEraCertificate | ∀-general | — |
| `Verification.source_exact` | AuthenticatedEraCertificate | ∀-general | — |
| `Verification.cut_mem` | AuthenticatedEraCertificate | ∀-general | — |
| `Verification.announcement` | AuthenticatedEraCertificate | ∀-general | — |
| `Verification.settled` | AuthenticatedEraCertificate | ∀-general | — |
| `Verification.settledCert` | AuthenticatedEraCertificate | ∀-general | — |
| `Verification.deliveryScope` | AuthenticatedEraCertificate | ∀-general | — |
| `Verification.sealSurvives` | AuthenticatedEraCertificate | ∀-general | — |
| `ReusableCertificate.sound` | AuthenticatedEraCertificate | ∀-general | — |
| `Verification.toReusableCertificate_key` | AuthenticatedEraCertificate | ∀-general | — |
| `Fixtures.accepted_unissued_cannot_be_progress` | AuthenticatedEraCertificate | finite-story | — |
| `Fixtures.authentication_does_not_manufacture_complete_cut` | AuthenticatedEraCertificate | finite-story | — |
| `FiniteGrowth.view_eq_state` | FiniteHistoryDelivery | ∀-general | — |
| `DeliveredGrowth.accepted_iff` | FiniteHistoryDelivery | ∀-general | — |
| `DeliveredGrowth.materialized_iff` | FiniteHistoryDelivery | ∀-general | — |
| `DeliveredGrowth.capacity_respected` | FiniteHistoryDelivery | ∀-general | — |
| `DeliveredGrowth.sameEventSet` | FiniteHistoryDelivery | ∀-general | — |
| `DeliveredGrowth.eventSetView_eq` | FiniteHistoryDelivery | ∀-general | — |
| `semantic_view_eq_of_recordDetermined` | FiniteHistoryDelivery | ∀-general | — |
| `MenuCandidate.row_price` | FiniteRepairMenu | ∀-general | — |
| `CheckedUniverse.stableIds` | FiniteRepairMenu | ∀-general | — |
| `CheckedUniverse.toCatalog` (def) | FiniteRepairMenu | ∀-general | — |
| `CheckedUniverse.mem_applicableEntries_iff` | FiniteRepairMenu | ∀-general | — |
| `CheckedUniverse.minimum_le_of_applicable` | FiniteRepairMenu | ∀-general | — |
| `CheckedUniverse.minimum_none_exhaustive` | FiniteRepairMenu | ∀-general | — |
| `Found.repair_price` | FiniteRepairMenu | ∀-general | — |
| `Found.row_price` | FiniteRepairMenu | ∀-general | — |
| `Result.exhaustive_of_isFound_false` | FiniteRepairMenu | ∀-general | — |
| `Examples.positive_finds_least_authored_id` | FiniteRepairMenu | finite-story | — |
| `Examples.authored_order_changes_choice_not_price_order` | FiniteRepairMenu | finite-story | — |
| `Examples.impossible_refusal_is_exactly_exhaustive` | FiniteRepairMenu | finite-story | — |
| `Examples.bound_refusal_is_exact` | FiniteRepairMenu | finite-story | — |
| `Examples.reversed_ids_are_refused` | FiniteRepairMenu | finite-story | — |

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
