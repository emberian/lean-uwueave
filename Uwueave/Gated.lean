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

## Not modeled, honestly

  * **Signatures.** That the actor issuing an op actually HOLDS the grant it
    cites is authentication — a premise here, exactly as in Authority's
    header. An op is data; anyone may write any `cite` into the log. The
    gate bounds what a cited grant can DO, not who may cite it.
  * **Citation by id.** `permitted` accepts ANY active grant triple carrying
    the cited id; on a state violating `UniqueGrant` two triples share an id
    and the op is permitted if either covers it. Content addressing
    (`id = hash(parent, scope, …)`) discharges this globally — Authority's
    `uniqueGrant_violation_extracts_collision` is the handoff.
  * **Computability of the gate.** `gatedOps` is `Prop`-valued: `Active`
    over a function-backed `GrantSet` is an unbounded certificate search,
    not decidable in general. A deployment makes the gate computable the
    macaroon way — the op CARRIES its delegation chain, and the check is
    per-link presence + unrevokedness + narrowing, whose soundness is
    precisely `Active`'s two constructors. On concrete states (§4)
    everything decides.
  * **The Exec-kernel boundary** (report-only note). `Exec.lean`'s kernel
    takes `(base, op array)` and already reports per-op verdicts (v2 status
    block: applied / cycle-skipped / invalid). Gating at that boundary means
    either (a) the caller filters by `gatedOps` before `encodeRequest` — the
    gate stays view-level, the kernel unchanged — or (b) the request format
    grows the grant/revocation substrate and the status vocabulary grows a
    verdict `3 = skipped (unauthorized)`, a format flag day. Neither is done
    here; this file is the abstraction level (`Move.lean`'s) both would be
    checked against.
  * **Arbitration of grant conflicts.** Fail-closed composes: duelling
    admins annihilate (`Authority.duelling_admins_annihilate`), so after a
    duel the gate rejects BOTH duellists' ops — and every op citing grants
    delegated under them. A system wanting a survivor buys ERA's
    epoch-batched arbitration (`Era.lean`, `duelling_admins_resolved`); its
    arbitrated view would slot in where `Active` sits, leaving every theorem
    shape here intact.

Lineage: `Authority.lean` (the token) · `Move.lean` (the op-log pattern and
its price) · macaroons/biscuits (attenuate offline, verify locally) · the
dregg through-line — "a turn is the exercise of an attenuable proof-carrying
token over owned state, leaving a receipt". The receipt half is the log
itself: grow-only, nothing ever deleted, every gated-out op still on record.
-/
import Uwueave.Authority
import Uwueave.Move

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

end Uwueave.Gated
