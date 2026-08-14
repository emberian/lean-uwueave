/-
# Uwueave.Gated — "who may move node n": authorization as a gated derived view.

The dregg through-line, second half. `Authority.lean` built the token — an
attenuation lattice of grants with fail-closed revocation, replicated
coordination-free. `Move.lean` built the exercise — a move-op log whose
invariant-bearing view is derived, never replicated. This file composes them:
**a move op carries the grant id its actor exercises, and the op feed that
reaches replay is a derived view gated by Authority's `Active`.** A turn is
the exercise of an attenuable proof-carrying token over owned state; here is
the exercise, gated by the token.

No coordination appears, no auth server, no new lattice: the composed state
is three grow-only sets (grants, revocations, ops) glued by the product
instance — `MergeState` is inherited (`inferInstance`, zero new merge
proofs) — and every authorization decision is a predicate of that state,
recomputed at each replica, never itself replicated.

  * `GatedState` — the grant/revocation substrate × a move-op log; `GOp`
    carries `cite`, the id of the grant its actor exercises.
  * `permitted` — the gate: the cited grant is `Active` (Authority's derived
    view, reused verbatim) AND its scope covers the moved node.
    **Scope-covers is a `Nat` ceiling**: a grant of scope `σ` may move
    exactly the nodes with id `< σ`. Chosen as the minimal relation that
    makes attenuation *mean* something at the op layer: coverage is monotone
    in `σ`, so `chain_scope_descends` becomes "the movable set only narrows
    down a delegation chain" (`chain_covers`); strictness makes `σ = 0` the
    fully-attenuated dead token; and `scope_le_root` surfaces as a hard
    op-level bound (`gated_node_lt_root`). Only the MOVED node is gated;
    gating the destination too is a real policy variant, not taken.
  * `gatedOps` — the derived view: the sub-log of permitted ops, what
    actually feeds replay.

Four results:

  1. `gated_sec` — the composed system inherits SEC: `Move.derived_view_sec`
     instantiated over the whole `GatedState`, with the gate invariant
     (`GateClosed`: every op in the feed cites an active covering grant) as
     the invariant clause. Delivery order, duplication, batching — the gated
     feed is a function of the merged state, and the gate holds at every
     point of every schedule.
  2. `gated_antitone` (the centerpiece) — growing the revocation set never
     ENLARGES the gated feed: late revocations only ever remove moves from
     effect. `authority_view_antitone` lifted to op-effects — the
     fail-closed instability composes through the gate intact. Merge-shaped
     corollaries: `gated_merge_only_revokes`, `gated_sync_only_revokes`,
     `gated_out_is_forever`.
  3. `gated_monotone_grants` (+ `gated_monotone_log`) — new grants never
     retract previously-permitted ops; new ops never remove old ones. With
     2 this signs the view's every instability: grants and ops only add,
     revocations only subtract.
  4. The story (§4): Alice delegates to Bob; Bob moves a node his grant
     covers while Alice concurrently revokes that grant. Merged, Bob's move
     is gated out and Alice's own op stands — identically at every replica —
     and revoking the ISSUER instead kills Bob's move too, though his grant
     id sits in no revocation set (`demo_cascade_revoked` at the op layer).
  5. **The bridge (§5): this gate IS the shipping kernel's gate.** Format v3
     put the grant/revocation substrate in the request, a `permitted` filter
     ahead of the kernel's sort, and status `3` in the response;
     `kernel_admits_only_authorised` proves — with no hypotheses — that every
     op `uwueave_replay_kernel` replays is in this file's `gatedOps`, and
     `kernel_gate_agrees_gatedOps` proves the two coincide under `WF` +
     `UniqueGrant`. The theorems above are therefore about what the kernel
     does, not about a model beside it.

## The honest boundary

Each item is labelled **TERMINAL** (a theorem *of the model* — no work would
remove it) or **⟨UNDONE U-0051⟩** (work, in a caveat's clothes). The list used to open
with "this gates the abstract op layer, not the shipping kernel", followed by
the recipe for fixing that; the recipe was executed, and the item is gone
rather than reworded.

⚑ **A second item left the same way — read this as the forward pointer.** The
list also formerly marked conflicting grant issuance and composition with this
gate as open and unstarted.
`Uwueave/GatedEra.lean` **is that work, done** — it substitutes `Era.resolve`
for `Authority.Active` at the authority substrate and delivers
`ge_deterministic`, `ge_duel_resolved` (the survivor's op stands where
fail-closed denied both) and `ge_finalised_stable`, plus the finding
`antitone_forbids_enabling`. So the item is gone rather than reworded. What
survives it is a theorem, not a caveat: fail-closed composes as advertised —
after a duel this file's gate rejects **both** duellists' ops and every op
citing grants delegated under them (`Authority.duelling_admins_annihilate`) —
and arbitration's price is that it loses `gated_antitone`'s shrinkage
(`GatedEra.ge_not_antitone`).

  * **Signatures are a premise, not a theorem of this gate.**
    `Uwueave.Authenticity.authenticity_violation_extracts_forgery` now supplies
    the constructive handoff from an accepted, unissued signed record to a
    concrete forgery witness. `Uwueave.Byzantine.unauthenticated_submission_can_pass_the_gate`
    separately proves the exact attack here: a submitter not represented in
    `GOp` can cite somebody else's live grant and pass the ordinary gate.
    ⟨UNDONE U-0052 at the shipping boundary; model admission paid⟩
    `AuthenticatedAdmission.AuthenticatedGatedOp` now connects a received,
    accepted signed `MoveClaim` to the abstract gated feed under
    `Authenticity.AuthenticIssuer` and explicit `GrantHolder` binding. FORMAT
    v3 and `Exec.Op` carry no issuer, key epoch or signature lane, so no theorem
    authenticates the request reaching the kernel; no concrete EUF-CMA proof is
    present. The gate bounds what a cited grant can DO, not who may cite it.
  * **The kernel searches grants by FIRST match; `permitted` quantifies over
    all of them.** ⟨TERMINAL under content addressing, else ⟨PREMISE U-0053⟩⟩ On a
    substrate satisfying `UniqueGrant` the two coincide, and that is exactly
    the hypothesis `kernel_gate_agrees` carries. Without it the kernel can
    only admit FEWER ops than the abstraction (`kernel_admits_only_authorised`
    needs no hypothesis), so the seam is safe-side. Content-addressed grant
    ids (`id = hash(parent, scope, …)`) discharge it globally;
    `uniqueGrant_violation_extracts_collision` is the handoff.
  * **The kernel refuses a grant chain that does not descend.**
    ⟨TERMINAL, by design⟩ `Exec.activeFrom` recurses only when
    `parent < id` — `Authority.WF`'s creation-order clause — which is what
    makes it total without fuel. On a substrate violating `WF` it therefore
    reports *less* authority than `Active` would, and `kernel_gate_agrees`'s
    completeness direction carries `WF` for precisely this reason. Again
    safe-side, and deliberately so.
  * **⚠ The gate's antitonicity is about the FEED, not the applied set.**
    ⟨TERMINAL, and proved⟩ `gated_antitone` and `kernel_gated_antitone` say
    revocations only ever shrink the sub-log that reaches replay. They do NOT
    say revoking makes fewer moves happen: the cycle rule is not monotone in
    the log, so removing an op can un-block one it was shadowing.
    `Exec.applied_set_not_antitone` is the two-node witness — a revocation
    that ADDS an override. Any UI reading status `3` as "one fewer move
    happened" is wrong; what holds is that no unauthorised op is replayed,
    and that de-authorisation is forever (`Exec.gated_unauthorised_is_forever`).
  * **The shipping boundary binds the caller-variable substrate.** FORMAT-v4
    signs an opaque context commitment. `AuthenticatedRuntime` fixes that
    commitment with the document, genesis and an execution binding, rechecks
    the provider's pinned snapshot, and recomputes the live execution binding.
    That domain-separated digest frames the ordered topology, grants and
    revocations; pinned recovery repeats the checks and exact-compares the
    reconstructed admission with the stored record. This is implementation
    evidence, not proof of provider honesty: same-commitment immutability and
    historical availability, digest collision resistance, and external-pin
    custody remain deployment premises.
  * **Scope is a `Nat` ceiling on node ids — and in the kernel, on node
    INDICES.** ⟨SCOPE U-0055⟩ Enough to make covering decidable and the theorems
    honest, and now enough to make the kernel's coverage check one
    comparison. But note what the port made concrete: `GOp.node` is an id
    here and `Exec.Op.child` is an index into the request's node block, so a
    grant's meaning is relative to the indexing its request was built
    against. `gopOf` is honest about this (`node := op.child`) and the bridge
    is stated over the denoted state, so no theorem is wrong — but a
    deployment wanting scopes that mean the same thing at every replica
    either fixes a canonical indexing or uses the universal scope. A real
    capability language wants a lattice of scopes anyway (the poset gap
    `Authority.lean` already names), and that is where this gets fixed. Only
    the MOVED node is gated; gating the destination too is a policy variant,
    not taken.
  * **`gatedOps` is `Prop`-valued and undecidable in general.**
    ⟨TERMINAL — and no longer a gap⟩ `Active` over a function-backed
    `GrantSet` is an unbounded certificate search. The kernel does not decide
    it: it decides `Exec.activeFrom` over the grant ARRAY the request carries
    — the macaroon move, the token travelling with its chain — and §5 proves
    that decision sound for the `Prop`-valued gate with no hypotheses, and
    complete under `WF` + `UniqueGrant`. The undecidability is a fact about
    the abstraction, not a hole under the implementation.
  * **Below the Lean, the execution TCB — and it is NOT terminal.**
    ⟨UNDONE U-0160⟩ The former umbrella is now a registry-integrity
    obligation, not a claim that one aggregate test closes the execution TCB.
    A machine-readable Ledger 2 gate must preserve the exact mapping to Lean
    code generation ⟨DEBT-REF U-0161⟩, the host C toolchain
    ⟨DEBT-REF U-0162⟩, the Lean runtime ⟨DEBT-REF U-0163⟩, `shim.c`
    ⟨DEBT-REF U-0164⟩, ABI/FFI ⟨DEBT-REF U-0165⟩, Rust `unsafe`
    ⟨DEBT-REF U-0166⟩, storage/index glue ⟨DEBT-REF U-0167⟩, the
    filesystem/crash premise ⟨DEBT-REF U-0168⟩, the supported native scope
    ⟨DEBT-REF U-0169⟩, and canonical host durability
    ⟨DEBT-REF U-0170⟩. The two paid controls remain Lean-owned request
    encoding and fail-closed native-closure freshness. Nothing else is paid by
    this decomposition.
  * ⟨UNDONE U-0161⟩ Lean IR-to-C lowering for the exact `RuntimeInit` closure
    is unverified. Translation validation or a proved exporter must cover every
    module and exported function; differential outputs alone do not prove the
    lowering.
  * ⟨PREMISE U-0162⟩ Native evidence assumes the semantic correctness of the
    selected host C compiler, archiver, and linker. Each run must record their
    exact identities; a binary-distribution claim requires a new verified-
    compilation obligation.
  * ⟨PREMISE U-0163⟩ Native evidence assumes the selected toolchain's
    `libleanshared`, including allocation, reference counting, initialization,
    and exported-call semantics. Shim-owned lifecycle work remains separate.
  * ⟨UNDONE U-0164⟩ `shim.c` still needs generated or mechanically checked
    object construction, bounds, copies, allocation, consumption, and reference
    counting, with mutation negatives and sanitizer-backed integration gates.
  * ⟨UNDONE U-0165⟩ Rust, C, and generated Lean declarations still need one
    canonical interface description that checks symbols, signatures, layouts,
    calling conventions, and ownership on both supported native platforms.
  * ⟨UNDONE U-0166⟩ Direct unsafe shim calls remain in the benchmark target,
    and the crate lacks an exact AST inventory enforcing `unsafe` only at the
    dedicated FFI boundary. This row also depends on the shim and ABI rows.
  * ⟨UNDONE U-0167⟩ Remaining host storage and index transitions still need
    refinement to Lean-owned references or Lean-owned decisions, including
    rebuilt-versus-incremental index equality after every supported trace.

    ⚑ The qualifier is the part that falls off in transit. `docs/TRUST.md`
    cites *this section* as its seed, for writing "⟨TERMINAL, **at this
    layer**⟩" where a summary wrote "terminal" — and this bullet is the one
    place in the file that made the unqualified move anyway.

## The price, and why it points the safe direction

An op that was in the gated feed can leave it when a revocation syncs in
(`story_fail_closed`): a "permitted" move un-happens. This is the SAME shape
as `Move.view_not_stable` — a monotone substrate whose derived view is not
stable under growth — read through the duality Authority spells out at
`authority_view_antitone`: when the unstable view is a document, the
instability is a UX anomaly to design around; when it is a permission, the
instability IS the feature, provided it points one way. `gated_antitone` and
`gated_monotone_grants` prove it points one way: growth of the substrate can
add authorized moves and delete de-authorized ones, never the reverse of
either. Fail-closed, all the way through the composition.

Lineage: `Authority.lean` (the token) · `Move.lean` (the op-log pattern and
its price) · macaroons/biscuits (attenuate offline, verify locally) · the
dregg through-line — "a turn is the exercise of an attenuable proof-carrying
token over owned state, leaving a receipt". The receipt half is the log
itself: grow-only, nothing ever deleted, every gated-out op still on record.
-/
import Uwueave.Authority
import Uwueave.Move
import Uwueave.ExecRefine

namespace Uwueave.Gated

open Uwueave Uwueave.Catalog Uwueave.Authority

/-! ## §1. The composed state and the gate -/

/-- A gated move op: at Lamport time `t`, re-parent node `node` under `dest`
(`none` = root), **exercising the grant with id `cite`**. The gate reads
`(node, cite)`; `(t, dest)` are the payload the replay layer below the gate
consumes — `Move.lean`'s discipline: an op without its timestamp cannot be
ordered into a replay at all. -/
structure GOp where
  t     : Nat
  node  : Nat
  dest  : Option Nat
  cite  : Nat
  deriving DecidableEq, Repr

/-- The composed replicated state: grant set × revocation set × move-op log.
All three components are grow-only; `MergeState` is inherited from the
product and `GSet` instances — `inferInstance`, zero new merge proofs. -/
abbrev GatedState := GrantSet × Revoked × GSet GOp

example : MergeState GatedState := inferInstance

/-- The grant substrate of a composed state. -/
abbrev grants (st : GatedState) : GrantSet := st.1
/-- The revocation substrate of a composed state. -/
abbrev revoked (st : GatedState) : Revoked := st.2.1
/-- The move-op log of a composed state. -/
abbrev oplog (st : GatedState) : GSet GOp := st.2.2

/-- Scope-covers: a grant of scope `σ` may move exactly the nodes with id
strictly below `σ`. Strictness makes `σ = 0` the dead token (covers
nothing); monotonicity in `σ` makes attenuation shrink the movable set —
`chain_covers` and `gated_node_lt_root` surface both directions as
theorems. -/
abbrev covers (σ : Nat) (o : GOp) : Prop := o.node < σ

/-- The gate: op `o` is permitted in state `st` when some active grant
carries its cited id and that grant's scope covers the moved node. `Active`
is Authority's derived view, reused verbatim — the gate adds no new
judgement about the substrate, only the coverage conjunct. (On a
`UniqueGrant`-violating state the existential ranges over id-sharing
siblings; see the header's honesty note.) -/
abbrev permitted (st : GatedState) (o : GOp) : Prop :=
  ∃ p σ, Active (grants st) (revoked st) (o.cite, p, σ) ∧ covers σ o

/-- **The derived view**: the sub-log of permitted ops — what actually feeds
replay. Like every derived view in this library it is a predicate of the
replicated state, recomputed at each replica, never itself replicated. -/
abbrev gatedOps (st : GatedState) : GOp → Prop :=
  fun o => oplog st o = true ∧ permitted st o

/-- Attenuation composes with coverage: on a well-formed, collision-free
state, any node covered by a grant's scope is covered by every ancestor
scope on its delegation chain — `chain_scope_descends` surfaced at the op
layer: **the movable set only narrows down a chain.** -/
theorem chain_covers {ρ : Nat} {s : GrantSet} (hwf : WF ρ s)
    (huniq : UniqueGrant s) {g a : Grant} (hc : Chain s g a) {o : GOp}
    (h : covers g.2.2 o) : covers a.2.2 o :=
  Nat.lt_of_lt_of_le h (chain_scope_descends hwf huniq hc)

/-! ## §2. SEC of the composed system -/

/-- The composed derived view `gated_sec` runs through `derived_view_sec`:
the authority view and the gated op feed, together. The authority component
rides along so the gate invariant (`GateClosed`) is a property OF THE VIEW —
the discipline of `Move.derived_view_sec`, whose invariant slot speaks only
about what the interpreter produced. -/
def gatedView (st : GatedState) : (Grant → Prop) × (GOp → Prop) :=
  (Active (grants st) (revoked st), gatedOps st)

/-- The gate invariant: every op in the feed cites a grant active in the
view's own authority component, with a scope covering the moved node. -/
def GateClosed (v : (Grant → Prop) × (GOp → Prop)) : Prop :=
  ∀ o : GOp, v.2 o → ∃ p σ, v.1 (o.cite, p, σ) ∧ covers σ o

/-- The interpreter enforces the gate by construction — `derived_view_sec`'s
`henf` obligation, discharged the way `miniInterp_acyclic` discharges
acyclicity: the definition of the view IS the enforcement. The value is that
the property is stated of the view, so SEC can carry it through every merge
schedule. -/
theorem gate_enforces (st : GatedState) : GateClosed (gatedView st) :=
  fun _ h => h.2

/-- **The composed system inherits SEC** — `Move.derived_view_sec`
instantiated over the whole `GatedState` (the product lattice, `MergeState`
by `inferInstance`): deltas commute (clause 1) and are idempotent (clause 2)
through the composed view, and the gate invariant holds at every point of
every schedule (clause 3). Convergence of authorization decisions costs
nothing beyond what the log pattern already paid. -/
theorem gated_sec (base Δ₁ Δ₂ : GatedState) :
    gatedView ((base ⊔ Δ₁) ⊔ Δ₂) = gatedView ((base ⊔ Δ₂) ⊔ Δ₁)
    ∧ gatedView ((base ⊔ Δ₁) ⊔ Δ₁) = gatedView (base ⊔ Δ₁)
    ∧ GateClosed (gatedView ((base ⊔ Δ₁) ⊔ Δ₂)) :=
  Move.derived_view_sec gatedView GateClosed gate_enforces base Δ₁ Δ₂

/-! ## §3. The signed instability — fail-closed composes through the gate -/

/-- **The centerpiece: growing the revocation set never enlarges the gated
feed.** Over a fixed grant set and op log, every op in the feed under the
larger revocation set was already in it under the smaller — late revocations
only ever REMOVE moves from effect; they cannot authorize one, resurrect
one, or smuggle one into replay. `authority_view_antitone` lifted to
op-effects: the fail-closed instability composes through the gate. -/
theorem gated_antitone {gs : GrantSet} {r r' : Revoked} {l : GSet GOp}
    (hgrow : ∀ i, r i = true → r' i = true) {o : GOp}
    (h : gatedOps (gs, r', l) o) : gatedOps (gs, r, l) o := by
  obtain ⟨hlog, p, σ, hact, hcov⟩ := h
  exact ⟨hlog, p, σ, authority_view_antitone hgrow hact, hcov⟩

/-- `gated_antitone` at a revocation merge: syncing in a peer's revocations
only ever shrinks the feed — `Authority.merge_only_revokes` at the op
layer. -/
theorem gated_merge_only_revokes {gs : GrantSet} (r Δ : Revoked)
    {l : GSet GOp} {o : GOp} (h : gatedOps (gs, r ⊔ Δ, l) o) :
    gatedOps (gs, r, l) o :=
  gated_antitone (fun i hi => by show (r i || Δ i) = true; simp [hi]) h

/-- `gated_antitone` at a full-state sync: of the three channels a sync
opens — peer grants, peer revocations, peer ops — revocation is the only
subtractive one. Every op in the fully-merged feed is in the feed that takes
both peers' grants and ops but only one side's revocations. -/
theorem gated_sync_only_revokes {st peer : GatedState} {o : GOp}
    (h : gatedOps (st ⊔ peer) o) :
    gatedOps (grants st ⊔ grants peer, revoked st, oplog st ⊔ oplog peer) o :=
  gated_antitone
    (fun i hi => by show (revoked st i || revoked peer i) = true; simp [hi]) h

/-- Fail-closed is forever at the op layer: an op outside the feed under `r`
stays outside it under every larger revocation set (grants and log fixed) —
`revocation_is_forever`, lifted. -/
theorem gated_out_is_forever {gs : GrantSet} {r r' : Revoked} {l : GSet GOp}
    (hgrow : ∀ i, r i = true → r' i = true) {o : GOp}
    (hdead : ¬ gatedOps (gs, r, l) o) : ¬ gatedOps (gs, r', l) o :=
  fun h => hdead (gated_antitone hgrow h)

/-- **New grants never retract previously-permitted ops**: the positive
direction, `active_monotone_grants` lifted. With `gated_antitone` and
`gated_monotone_log` this signs every instability of the composed view:
grants and ops only add moves to the feed, revocations only remove them. -/
theorem gated_monotone_grants {gs gs' : GrantSet}
    (hgrow : ∀ a : Grant, gs a = true → gs' a = true) {r : Revoked}
    {l : GSet GOp} {o : GOp}
    (h : gatedOps (gs, r, l) o) : gatedOps (gs', r, l) o := by
  obtain ⟨hlog, p, σ, hact, hcov⟩ := h
  exact ⟨hlog, p, σ, active_monotone_grants hgrow hact, hcov⟩

/-- Growing the op log never removes a previously-permitted op — the trivial
third sign, recorded so the sign table is complete. -/
theorem gated_monotone_log {l l' : GSet GOp}
    (hgrow : ∀ o : GOp, l o = true → l' o = true) {gs : GrantSet}
    {r : Revoked} {o : GOp}
    (h : gatedOps (gs, r, l) o) : gatedOps (gs, r, l') o :=
  ⟨hgrow o h.1, h.2⟩

/-- **Nobody moves a node at or beyond the root ceiling, ever**: on a
well-formed grant substrate, every op in the gated feed moves a node
strictly below the root scope — `scope_le_root` composed through the gate,
at every replica, after every merge, with no runtime check
(`wf_iconfluent` keeps the premise true across all schedules). -/
theorem gated_node_lt_root {ρ : Nat} {st : GatedState}
    (hwf : WF ρ (grants st)) {o : GOp} (h : gatedOps st o) : o.node < ρ := by
  obtain ⟨-, p, σ, hact, hcov⟩ := h
  exact Nat.lt_of_lt_of_le hcov (active_scope_le_root hwf hact)

/-! ## §4. The story: a revocation races a move, and loses nothing

Alice holds grant 1 (root-issued, scope 9) and has delegated grant 2
(scope 4) to Bob — `Authority.demoChain`, reused. Bob moves node 3 (`< 4`,
covered) citing grant 2, while Alice, concurrently, revokes grant 2
(`Authority.aliceRevokesBob`, reused — the value is a revocation of id 2).
Alice's own op moves node 7 citing grant 1. Merge the replicas — in either
order, `story_replicas_agree` — and Bob's move is gated out of the feed
while Alice's stands. The move Bob's replica watched happen has un-happened
(`story_fail_closed`); that is `view_not_stable`'s shape pointing the safe
direction. -/

/-- Alice's op: move node 7 to root, exercising grant 1 (scope 9 covers 7). -/
def opAlice : GOp := { t := 1, node := 7, dest := none, cite := 1 }

/-- Bob's op: move node 3 under node 7, exercising grant 2 (scope 4
covers 3). -/
def opBob : GOp := { t := 2, node := 3, dest := some 7, cite := 2 }

/-- Bob's replica: the delegation chain, no revocations seen, his own move
in the log. -/
def bobReplica : GatedState :=
  (demoChain, (noRevs, fun o => o == opBob))

/-- Alice's replica: the same chain, her revocation of Bob's grant 2, her
own move in the log. Issued concurrently with Bob's — neither replica has
seen the other. -/
def aliceReplica : GatedState :=
  (demoChain, (aliceRevokesBob, fun o => o == opAlice))

/-- The sync of the two replicas. -/
def synced : GatedState := bobReplica ⊔ aliceReplica

/-- Before the sync, Bob's move is in his replica's gated feed: the log
holds it, grant 2 is active (`demo_delegate_active`, reused) and its scope
covers node 3. -/
theorem story_bob_before : gatedOps bobReplica opBob :=
  ⟨by decide, 1, 4, demo_delegate_active, by decide⟩

/-- **After the sync, Bob's move is gated out**: any active triple citing
grant 2 would need id 2 unrevoked, and the merged revocation set holds
it. -/
theorem story_bob_gated_out : ¬ gatedOps synced opBob := by
  rintro ⟨-, p, σ, hact, -⟩
  have h2 : revoked synced 2 = false := active_head_unrevoked hact
  exact absurd h2 (by decide)

/-- Alice's own move survives the same sync: grant 1 is present, unrevoked,
root-parented, and scope 9 covers node 7. -/
theorem story_alice_survives : gatedOps synced opAlice :=
  ⟨by decide, 0, 9, .root (by decide) (by decide), by decide⟩

/-- The two replicas compute the SAME feed from the sync, whichever
direction the gossip ran — `merge_comm` pushed through the view;
`gated_sec` clause (1) is the same fact for arbitrary delta schedules. -/
theorem story_replicas_agree :
    gatedOps (bobReplica ⊔ aliceReplica) = gatedOps (aliceReplica ⊔ bobReplica) :=
  congrArg gatedOps (merge_comm bobReplica aliceReplica)

/-- The story in one statement: the sync only ADDED information
(`bobReplica ⊑ synced`), Bob's move was in the feed before it and out after
it, and Alice's op is in — the derived view is not stable under growth
(`Move.view_not_stable`'s shape), and its instability removed, never added,
authority (`gated_antitone`'s direction). -/
theorem story_fail_closed :
    bobReplica ⊑ synced
    ∧ gatedOps bobReplica opBob
    ∧ ¬ gatedOps synced opBob
    ∧ gatedOps synced opAlice :=
  ⟨le_merge_left bobReplica aliceReplica, story_bob_before,
   story_bob_gated_out, story_alice_survives⟩

/-- The root's intervention, for the cascade coda: same chain, the ISSUER
grant 1 revoked (`Authority.revokeIssuer`, reused), no ops. -/
def rootReplica : GatedState := (demoChain, (revokeIssuer, fun _ => false))

/-- **The cascade coda**: had the revocation named the ISSUER — grant 1,
Alice's own — Bob's move dies too, though grant 2 sits in no revocation set:
its citation's only path to the root passes the revoked grant
(`demo_cascade_revoked` at the op layer). The whole subtree under a revoked
grant loses its moves — the macaroon semantics, deliberately. -/
theorem story_cascade : ¬ gatedOps (bobReplica ⊔ rootReplica) opBob := by
  rintro ⟨-, p, σ, hact, -⟩
  have hpres : (demoChain (opBob.cite, p, σ) || demoChain (opBob.cite, p, σ)) = true :=
    active_present hact
  simp [demoChain, opBob] at hpres
  obtain ⟨rfl, rfl⟩ := hpres
  rcases active_parent hact with h0 | ⟨q, σ', hpar⟩
  · exact absurd h0 (by decide)
  · have h1 : revoked (bobReplica ⊔ rootReplica) 1 = false :=
      active_head_unrevoked hpar
    exact absurd h1 (by decide)

/-! ## §5. The bridge: the shipping kernel's gate IS this gate

Until format v3 this file gated `Move.lean`'s abstract feed while
`Exec.absReplay` — the function behind `uwueave_replay_kernel` — replayed
everything it was handed. The header used to list that as an honest boundary
with a recipe attached. The recipe is executed: the request carries a
grant/revocation substrate, ops carry a citation, `Exec.permittedOp` filters
ahead of the sort, and status `3` reports the refusals
(`ExecRefine` §9). What remains is to prove the two gates are the SAME gate,
which is this section.

The correspondence has one seam and it is the one `Authority.lean` already
names: `Exec.findGrant` takes the FIRST record carrying a cited id, where
`permitted` quantifies existentially over all of them. On a state satisfying
`UniqueGrant` — the property content-addressed grant ids
(`id = hash(parent, scope, …)`) supply, and whose violations
`uniqueGrant_violation_extracts_collision` turns into collision witnesses —
the two coincide. So:

  * `kernel_admits_only_authorised` — **no hypotheses**: every op the kernel
    replays is in this file's gated feed. The safety direction is
    unconditional; a first-match search can only ever admit LESS.
  * `kernel_gate_agrees` / `kernel_gate_agrees_gatedOps` — under `WF` and
    `UniqueGrant`, the kernel's admitted sub-log is exactly `gatedOps`. -/

/-- A kernel grant array, read as this file's `GrantSet`. -/
def grantSetOf (gs : Array Exec.Grant) : GrantSet :=
  fun g => gs.any (fun e => (e.id, e.parent, e.scope) == g)

/-- A kernel revocation array, read as `Revoked` — *definitionally* the
kernel's own `Exec.isRevoked`, so no translation happens here. -/
def revokedOf (rs : Array Nat) : Revoked := Exec.isRevoked rs

/-- A kernel op, read as a `GOp`: the Lamport stamp, the moved node's index,
the destination (`-1` and every negative = root), and the citation. -/
def gopOf (op : Exec.Op) : GOp :=
  { t := op.lamport.toNat
    node := op.child
    dest := if op.dest < 0 then none else some op.dest.toNat
    cite := op.cite }

/-- A kernel op array, read as the move-op log. -/
def oplogOf (ops : Array Exec.Op) : GSet GOp :=
  fun o => ops.any (fun op => gopOf op == o)

/-- The composed state an encoded request denotes. -/
def stateOf (gs : Array Exec.Grant) (rs : Array Nat) (ops : Array Exec.Op) :
    GatedState :=
  (grantSetOf gs, revokedOf rs, oplogOf ops)

/-- What a found grant record witnesses: its id is the one searched for, and
its triple is present in the denoted grant set. -/
theorem present_of_findGrant {gs : Array Exec.Grant} {i : Nat} {g : Exec.Grant}
    (h : Exec.findGrant gs i = some g) :
    g.id = i ∧ grantSetOf gs (i, g.parent, g.scope) = true := by
  have hid : g.id = i := by
    have := Array.find?_some h
    simpa using this
  refine ⟨hid, ?_⟩
  have hmem : g ∈ gs := Array.mem_of_find?_eq_some h
  show gs.any (fun e => (e.id, e.parent, e.scope) == (i, g.parent, g.scope)) = true
  rw [Array.any_eq_true']
  exact ⟨g, hmem, by simp [hid]⟩

/-- A present triple guarantees the kernel's search finds *something* for its
id (not necessarily that triple — that is `UniqueGrant`'s job). -/
theorem findGrant_isSome {gs : Array Exec.Grant} {i p σ : Nat}
    (h : grantSetOf gs (i, p, σ) = true) : ∃ g, Exec.findGrant gs i = some g := by
  have hany : gs.any (fun e => (e.id, e.parent, e.scope) == (i, p, σ)) = true := h
  rw [Array.any_eq_true'] at hany
  obtain ⟨x, hx, hxe⟩ := hany
  have hid : x.id = i := by
    have := (beq_iff_eq (α := Nat × Nat × Nat) ..).mp hxe
    exact congrArg Prod.fst this
  have : (Exec.findGrant gs i).isSome := by
    rw [Exec.findGrant, Array.find?_isSome]
    exact ⟨x, hx, by simp [hid]⟩
  exact Option.isSome_iff_exists.mp this

/-- **Soundness of the executable carrier, with no hypotheses**: whenever the
kernel calls grant `i` active, `Authority.Active` holds of the very record it
found. The kernel's walk *is* an `Active` derivation — presence, unrevoked,
and either root-issued or an active parent — read off in the same order. -/
theorem kernel_active_sound {gs : Array Exec.Grant} {rs : Array Nat} :
    ∀ i, Exec.activeFrom gs rs i = true →
      ∃ g, Exec.findGrant gs i = some g
        ∧ Active (grantSetOf gs) (revokedOf rs) (i, g.parent, g.scope) := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro h
    cases hf : Exec.findGrant gs i with
    | none => rw [Exec.activeFrom, hf] at h; exact absurd h (by simp)
    | some g =>
      have hunfold : Exec.activeFrom gs rs i =
          (if Exec.isRevoked rs i then false
            else if g.parent == 0 then true
            else if _h : g.parent < i then Exec.activeFrom gs rs g.parent
              else false) := by
        rw [Exec.activeFrom, hf]
      rw [hunfold] at h
      obtain ⟨hid, hpres⟩ := present_of_findGrant hf
      by_cases hrev : Exec.isRevoked rs i = true
      · rw [if_pos hrev] at h; exact absurd h (by simp)
      · have hrev' : revokedOf rs i = false := by
          show Exec.isRevoked rs i = false
          simpa using hrev
        rw [if_neg hrev] at h
        by_cases hroot : (g.parent == 0) = true
        · have hp0 : g.parent = 0 := by simpa using hroot
          refine ⟨g, rfl, ?_⟩
          rw [hp0] at hpres ⊢
          exact .root hpres hrev'
        · rw [if_neg hroot] at h
          by_cases hlt : g.parent < i
          · rw [dif_pos hlt] at h
            obtain ⟨g', hf', hact'⟩ := ih g.parent hlt h
            obtain ⟨hid', -⟩ := present_of_findGrant hf'
            exact ⟨g, rfl, .step hpres hrev' hact'⟩
          · rw [dif_neg hlt] at h; exact absurd h (by simp)

/-- **Completeness of the executable carrier**, under the two premises
`Authority.lean` already carries: `WF` (creation order — what makes the
kernel's descending walk reach every ancestor the abstract chain does) and
`UniqueGrant` (what makes the first match *the* match). Induction on the
`Active` derivation. -/
theorem kernel_active_complete {ρ : Nat} {gs : Array Exec.Grant} {rs : Array Nat}
    (hwf : WF ρ (grantSetOf gs)) (huniq : UniqueGrant (grantSetOf gs))
    {g : Grant} (h : Active (grantSetOf gs) (revokedOf rs) g) :
    Exec.activeFrom gs rs g.1 = true := by
  induction h with
  | @root i σ hs hr =>
    obtain ⟨e, he⟩ := findGrant_isSome hs
    obtain ⟨hid, hpres⟩ := present_of_findGrant he
    obtain ⟨hp, -⟩ := huniq i 0 σ e.parent e.scope hs hpres
    rw [Exec.activeFrom, he]
    have hrev : Exec.isRevoked rs i = false := hr
    simp [hrev, ← hp]
  | @step i p σ q σ' hs hr _ ih =>
    obtain ⟨e, he⟩ := findGrant_isSome hs
    obtain ⟨hid, hpres⟩ := present_of_findGrant he
    obtain ⟨hp, -⟩ := huniq i p σ e.parent e.scope hs hpres
    have hrev : Exec.isRevoked rs i = false := hr
    have hunfold : Exec.activeFrom gs rs i =
        (if Exec.isRevoked rs i then false
          else if e.parent == 0 then true
          else if _h : e.parent < i then Exec.activeFrom gs rs e.parent
            else false) := by
      rw [Exec.activeFrom, he]
    rw [hunfold, if_neg (by simp [hrev])]
    by_cases hp0 : (e.parent == 0) = true
    · rw [if_pos hp0]
    · rw [if_neg hp0]
      have hlt : e.parent < i := by
        have h1 := (hwf i p σ hs).1
        omega
      rw [dif_pos hlt, ← hp]
      exact ih

/-- **The gate agrees, safety direction — no hypotheses.** Every op the
kernel admits is permitted by this file's gate, on the state the request
denotes. A first-match grant search can only under-approximate the
existential, so the shipping kernel never replays a move the abstraction
would refuse. -/
theorem kernel_permitted_sound {gs : Array Exec.Grant} {rs : Array Nat}
    (ops : Array Exec.Op) {op : Exec.Op} (h : Exec.permittedOp gs rs op = true) :
    permitted (stateOf gs rs ops) (gopOf op) := by
  cases hf : Exec.findGrant gs op.cite with
  | none => rw [Exec.permittedOp, hf] at h; exact absurd h (by simp)
  | some g =>
    rw [Exec.permittedOp, hf, Bool.and_eq_true] at h
    obtain ⟨g', hf', hact⟩ := kernel_active_sound op.cite h.1
    rw [hf] at hf'
    rw [← Option.some.inj hf'] at hact
    exact ⟨g.parent, g.scope, hact, by simpa [gopOf] using h.2⟩

/-- **The gate agrees, completeness direction** — under `WF` + `UniqueGrant`,
anything this file's gate permits, the kernel admits. -/
theorem kernel_permitted_complete {ρ : Nat} {gs : Array Exec.Grant}
    {rs : Array Nat} (hwf : WF ρ (grantSetOf gs))
    (huniq : UniqueGrant (grantSetOf gs)) (ops : Array Exec.Op) {op : Exec.Op}
    (h : permitted (stateOf gs rs ops) (gopOf op)) :
    Exec.permittedOp gs rs op = true := by
  obtain ⟨p, σ, hact, hcov⟩ := h
  rw [show (gopOf op).cite = op.cite from rfl] at hact
  have hchild : op.child < σ := hcov
  obtain ⟨e, he⟩ := findGrant_isSome (active_present hact)
  obtain ⟨hid, hpres⟩ := present_of_findGrant he
  obtain ⟨-, hσ⟩ := huniq op.cite p σ e.parent e.scope (active_present hact) hpres
  rw [Exec.permittedOp, he, Bool.and_eq_true]
  exact ⟨kernel_active_complete hwf huniq hact, by simp [← hσ, hchild]⟩

/-- **The abstract/executable gap, closed by theorem.** Under the premises
`Authority.lean` states and a deployment discharges cryptographically, an op
is in the shipping kernel's replayed sub-log **iff** it is in this file's
gated feed on the state its request denotes. `gated_antitone`,
`gated_monotone_grants` and `gated_node_lt_root` are therefore statements
about what `uwueave_replay_kernel` does, not about a model beside it. -/
theorem kernel_gate_agrees {ρ : Nat} {gs : Array Exec.Grant} {rs : Array Nat}
    (hwf : WF ρ (grantSetOf gs)) (huniq : UniqueGrant (grantSetOf gs))
    (ops : Array Exec.Op) (op : Exec.Op) :
    Exec.permittedOp gs rs op = true ↔ permitted (stateOf gs rs ops) (gopOf op) :=
  ⟨kernel_permitted_sound ops, kernel_permitted_complete hwf huniq ops⟩

/-- **No hypotheses**: every op the kernel replays is in the gated feed. This
is the half that matters for safety, and it needs neither `WF` nor
`UniqueGrant` — an ill-formed or collision-bearing substrate can only make
the kernel admit FEWER ops than the abstraction would, never more. -/
theorem kernel_admits_only_authorised {gs : Array Exec.Grant} {rs : Array Nat}
    {ops : Array Exec.Op} {op : Exec.Op} (h : op ∈ Exec.admittedOps gs rs ops) :
    gatedOps (stateOf gs rs ops) (gopOf op) := by
  rw [Exec.admittedOps, List.mem_filter] at h
  refine ⟨?_, kernel_permitted_sound ops h.2⟩
  show ops.any (fun o => gopOf o == gopOf op) = true
  rw [Array.any_eq_true']
  exact ⟨op, by simpa using h.1, by simp⟩

/-- The bridge in the vocabulary the kernel ships: the admitted sub-log and
`gatedOps` are the same set of ops (for ops the request actually carries). -/
theorem kernel_gate_agrees_gatedOps {ρ : Nat} {gs : Array Exec.Grant}
    {rs : Array Nat} (hwf : WF ρ (grantSetOf gs))
    (huniq : UniqueGrant (grantSetOf gs)) {ops : Array Exec.Op} {op : Exec.Op}
    (hmem : op ∈ ops.toList) :
    op ∈ Exec.admittedOps gs rs ops ↔ gatedOps (stateOf gs rs ops) (gopOf op) := by
  constructor
  · exact kernel_admits_only_authorised
  · intro h
    rw [Exec.admittedOps, List.mem_filter]
    exact ⟨hmem, kernel_permitted_complete hwf huniq ops h.2⟩

end Uwueave.Gated
