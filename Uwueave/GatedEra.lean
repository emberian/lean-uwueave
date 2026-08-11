/-
# Uwueave.GatedEra — the gate, with its conflicts ARBITRATED instead of annihilated.

`Gated.lean` closed with a named debt: *"Conflicting grant operations are not
arbitrated. … `Era.lean` implements the resolution — one deterministic survivor
per replica (`Era.duelling_admins_resolved`) — and composing that arbitration
with this gate is real work, unstarted."* This file is that work, done.

## The composition

The substitution is at the AUTHORITY substrate, not at the op layer:

  * `Gated.lean` gates a move op on `Authority.Active` — "the grant this op
    cites is on a live, unrevoked delegation chain". Concurrent contradictory
    authority annihilates (`Authority.duelling_admins_annihilate`): fail-closed
    is a *policy*, and its price is both duellists.
  * Here the gate reads `Era.resolve` instead — "the arbitrated role of this
    op's actor is at least the op's requirement". ERA's promote/demote events
    ARE the grant operations of this system (an admin promoting a user to
    Writer IS a delegation; a demote to Reader IS a revocation), and the
    arbitration is deterministic: every replica holding the same event and cut
    sets computes the same roles, so it computes the same op feed.

  * `EOp` — a move op carrying `actor`, the user whose arbitrated role is read.
    There is no `cite`: authority here is a role the group assigns, not a token
    the op presents.
  * `GEState` — Era's replicated substrate (`GSet Cut × GSet Event`) × a
    move-op log. `MergeState` inherited (`inferInstance`, zero new merge
    proofs), exactly as in `Gated.GatedState`; `geEncode_merge` transports the
    delivery lists onto that lattice, riding `Era.encode_merge`.
  * `moveReq` — the op's requirement, **the minimal policy that exercises the
    role lattice**: a move is a write into the weave, so it needs Writer
    (§3 op 2 of the paper: "write … requires Writer or Admin"); a move that
    detaches a node to the ROOT restructures the shared top level and needs
    Admin. Everything general below is proved for an ARBITRARY `req : EOp → Nat`
    — only the concrete witnesses fix `moveReq` — so the policy choice is
    confined to §5-§7's decide-witnesses and no theorem depends on it.
  * `geGatedOps req cuts log ops` — the composed derived view: the sub-log of
    ops whose actor's arbitrated role clears the requirement.
  * `geFinalOps` — the same feed computed against `Era.resolveFinal`, the view
    of the finalised prefix alone.

## What is proved

  1. **`ge_deterministic`** — replicas holding the same event set and the same
     cut set permit exactly the SAME ops, whatever the delivery order,
     duplication or batching. Rides `Era.resolve_same_sets`; needs no honesty
     hypothesis on the arbiter. `ge_same_state_same_feed` is the same fact
     against the replicated lattice element (`Era.same_state_same_view`), and
     `ge_replicas_agree` / `ge_replicas_idem` are the merge-schedule
     corollaries.
  2. **`ge_duel_resolved`** — the duelling admins at the OP layer. Alice and
     Bob concurrently demote each other; ERA picks a survivor, and the gated
     op-set is the survivor's: Alice's move is in the feed, Bob's is out, at
     every replica and for every delivery permutation. The contrast is the
     point, and it is a theorem, not a remark: `ge_duel_failclosed_denies_both`
     runs the same duel through `Gated.gatedOps` on the annihilated state and
     BOTH ops are denied. `ge_duel_arbiter_flips` then shows the arbiter's cut
     placement — never a named winner — swapping which op survives.
  3. **`ge_finalised_stable`** — ops permitted under a finalised prefix STAY
     permitted as pending events arrive; the finalised feed is not merely
     non-shrinking but unchanged (`Era.final_view_immune`). Fail-closed cannot
     offer this at all, and that too is a theorem: `gated_revoking_the_cite_kills`
     shows that one revocation removes ANY op from a `Gated` feed, from any
     state and with no hypothesis, and `gated_kill_is_forever` that it never
     returns — so no prefix of that system is ever final.
  4. **The sign table, including where it FAILS.** `Gated.gated_antitone`'s
     analogue — "growth of the authority substrate never enlarges the feed" —
     is **FALSE** here, and `ge_not_antitone` proves it with a witness: a
     promote event arriving turns a denied op into a permitted one. The
     monotone analogue is false too (`ge_not_monotone`: a demote arriving
     turns a permitted op into a denied one), and cut growth flips verdicts in
     both directions (`ge_cut_growth_flips`). What survives is monotonicity in
     the OP log (`ge_monotone_ops`) and in the requirement
     (`ge_antitone_req`). The trade, packaged: `ge_trade_agreement_over_shrinkage`.

## The trade, stated plainly

Fail-closed guarantees SHRINKAGE: `Gated.gated_antitone` says growth of the
substrate can only remove authority, so a permitted op is a fact about the
whole future of that replica's revocation set — and the price is that a duel
kills both duellists and no prefix is ever safe from a late revocation.
Arbitration guarantees AGREEMENT: `ge_deterministic` says every replica reads
the same feed and `ge_duel_resolved` says a duel keeps a survivor — and the
price is that growth is not one-directional, because a system that can PROMOTE
cannot be antitone. `antitone_forbids_enabling` states that half abstractly:
for ANY permission rule antitone in event growth, an op denied on a sub-log is
denied on every extension — so no promotion can ever take effect. You cannot
have both, and this file does not pretend otherwise; it picks agreement and
shows the bill.

## Honest scope — see §8 for the itemised version

Everything Era does not model, this file does not model either: no hash DAG, no
causal-closure computation of epochs, no signatures, no backdating detection,
no liveness. Two things are specific to the composition and named where they
bite: the attenuation CHAIN of `Authority.lean` has no analogue here (Era's
roles are flat), and `actor` is a bare `Nat` that anyone may write into an op —
authenticity is a premise here exactly as `cite` was in `Gated.lean`, and it
bites harder, because `cite` at least had to name a live delegation chain.

Lineage: `Gated.lean` (the gate this replaces the substrate of) ·
`Authority.lean` (the fail-closed branch of the same fork) · `Era.lean` (the
arbitration, and every theorem this file rides) · ERA (Kegan Dougal, PaPoC
2026, arXiv:2601.22963).
-/
import Uwueave.Era
import Uwueave.Gated

namespace Uwueave.GatedEra

open Uwueave Uwueave.Catalog

/-! ## §1. The op, the state, the transport -/

/-- An arbitrated move op: at Lamport time `t`, re-parent node `node` under
`dest` (`none` = the root), performed by user `actor`. The gate reads
`(actor, dest)` — the actor's arbitrated role and the op's requirement;
`(t, node)` are the payload the replay layer below the gate consumes, the
`Move.lean` discipline (an op without its timestamp cannot be ordered into a
replay at all).

There is deliberately no `cite` field. `Gated.GOp` carried the id of a grant
its holder exercises, because in `Authority.lean` authority IS a token; here
authority is a ROLE the arbitrated group state assigns to a user, so the op
names the user and the state supplies the rest. -/
structure EOp where
  t     : Nat
  node  : Nat
  dest  : Option Nat
  actor : Nat
  deriving DecidableEq, Repr

/-- The composed replicated state: ERA's cut records × ERA's events × the
move-op log. All three components are grow-only and `MergeState` is inherited
from `Era.EraState` and the `GSet` instance — `inferInstance`, zero new merge
proofs, exactly as `Gated.GatedState` inherits its own. -/
abbrev GEState := Era.EraState × GSet EOp

example : MergeState GEState := inferInstance

/-- A replica's composed state from its delivery lists. As in `Era.lean` the
lists are the TRANSPORT and the lattice element is the convergence object:
`Era.resolve` is a function of the lists that only depends on their member
sets, so it is well defined on encoded states (`ge_same_state_same_feed`)
without being computable from a `GSet`, which is not enumerable. -/
def geEncode (cuts : List Era.Cut) (log : List Era.Event) (ops : GSet EOp) :
    GEState := (Era.encode cuts log, ops)

/-- Syncing two replicas' lists IS merging their `GEState`s — `Era.encode_merge`
with the op log carried alongside by the product instance. -/
theorem geEncode_merge (cuts cuts' : List Era.Cut) (log log' : List Era.Event)
    (ops ops' : GSet EOp) :
    geEncode cuts log ops ⊔ geEncode cuts' log' ops'
      = geEncode (cuts ++ cuts') (log ++ log') (ops ⊔ ops') := by
  show (Era.encode cuts log ⊔ Era.encode cuts' log', ops ⊔ ops')
      = (Era.encode (cuts ++ cuts') (log ++ log'), ops ⊔ ops')
  rw [Era.encode_merge]

/-! ## §2. The gate — arbitration where `Gated` had a fail-closed intersection -/

/-- The requirement of an op: **a move needs Writer; a move that detaches a
node to the ROOT needs Admin.** The minimal policy that exercises the role
lattice above a single test — the first clause is the paper's own §3 op 2 ("a
move is a write into the weave"), the second is the one place this file spends
a policy choice, so that "role ≥ requirement" is a real comparison in a lattice
rather than a Boolean.

The choice is confined to the witnesses: every general theorem below quantifies
over an arbitrary `req : EOp → Nat`, so a deployment substituting its own
policy keeps all of them. Only `covers`'s job changed shape — `Gated.covers`
compared a node id against a delegated scope ceiling; here the comparison is
between the op's demanded role and the actor's arbitrated one. -/
def moveReq (o : EOp) : Nat :=
  if o.dest.isNone then Era.admin else Era.writer

/-- The gate against an already-resolved group view: op `o` passes when it is
in the log and its actor's role in `v` is at least `req o`. Factored out of
`geGatedOps` so the full feed and the finalised feed are the same predicate at
two different views — which is what makes `ge_finalised_stable` a rewrite. -/
abbrev geOpsOf (req : EOp → Nat) (v : Era.GroupView) (ops : GSet EOp) :
    EOp → Prop :=
  fun o => ops o = true ∧ req o ≤ v.role o.actor

/-- **The composed derived view**: the sub-log of ops permitted by the
ARBITRATED group state. `Era.resolve` canonicalises the delivered events into
the execution order the arbiter's cuts induce, folds them with authorisation
checking, and the resulting role assignment is what the gate reads. This is
`Gated.gatedOps` with `Authority.Active` replaced by ERA's deterministic
verdict — a derived view of a replicated state, recomputed at each replica,
never itself replicated. -/
abbrev geGatedOps (req : EOp → Nat) (cuts : List Era.Cut)
    (log : List Era.Event) (ops : GSet EOp) : EOp → Prop :=
  geOpsOf req (Era.resolve cuts log) ops

/-- The feed of the FINALISED prefix alone: the same gate read against
`Era.resolveFinal`, which executes only the events the arbiter has placed in an
epoch. §6's stability theorem is about this feed, and `ge_final_not_full` shows
it is genuinely a different one. -/
abbrev geFinalOps (req : EOp → Nat) (cuts : List Era.Cut)
    (log : List Era.Event) (ops : GSet EOp) : EOp → Prop :=
  geOpsOf req (Era.resolveFinal cuts log) ops

/-! ## §3. (a) Determinism — every replica permits the same ops -/

/-- **All replicas with the same event and cut sets permit exactly the same
ops.** Any delivery order, any duplication, any batching on either component:
the composed feed is a function of the two sets. `Era.resolve_same_sets` lifted
to op-effects — and note the mechanism, which is ERA's and not a commutation
argument: promote/demote genuinely do not commute (§3.2), so the theorem is
true because `resolve` canonicalises into the execution order BEFORE folding.
No honesty hypothesis on the arbiter is needed; an equivocating one still
yields agreement, because the epoch of an event is the least cut naming it. -/
theorem ge_deterministic {cuts cuts' : List Era.Cut}
    {log log' : List Era.Event} (hc : ∀ c, c ∈ cuts ↔ c ∈ cuts')
    (hl : ∀ e, e ∈ log ↔ e ∈ log') (req : EOp → Nat) (ops : GSet EOp) :
    geGatedOps req cuts log ops = geGatedOps req cuts' log' ops := by
  show geOpsOf req (Era.resolve cuts log) ops
      = geOpsOf req (Era.resolve cuts' log') ops
  rw [Era.resolve_same_sets hc hl]

/-- Determinism against the replicated state proper: replicas whose `GEState`s
are EQUAL permit the same ops — the composed gate is well defined on the
lattice, not merely on lists. `Era.same_state_same_view` with the op component
carried through. -/
theorem ge_same_state_same_feed {req : EOp → Nat} {cuts cuts' : List Era.Cut}
    {log log' : List Era.Event} {ops ops' : GSet EOp}
    (h : geEncode cuts log ops = geEncode cuts' log' ops') :
    geGatedOps req cuts log ops = geGatedOps req cuts' log' ops' := by
  have hera : Era.encode cuts log = Era.encode cuts' log' := congrArg Prod.fst h
  have hops : ops = ops' := congrArg Prod.snd h
  show geOpsOf req (Era.resolve cuts log) ops
      = geOpsOf req (Era.resolve cuts' log') ops'
  rw [Era.same_state_same_view hera, hops]

/-- Gossip direction is invisible: two replicas that sync the same pair of
states in opposite orders compute the same feed. The composed-lattice reading
of `ge_deterministic`, and the analogue of `Gated.story_replicas_agree` for the
arbitrated gate. -/
theorem ge_replicas_agree (req : EOp → Nat) (cuts cuts' : List Era.Cut)
    (log log' : List Era.Event) (ops ops' : GSet EOp) :
    geGatedOps req (cuts ++ cuts') (log ++ log') (ops ⊔ ops')
      = geGatedOps req (cuts' ++ cuts) (log' ++ log) (ops' ⊔ ops) := by
  rw [merge_comm ops ops']
  exact ge_deterministic
    (fun c => by rw [List.mem_append, List.mem_append]; exact Or.comm)
    (fun e => by rw [List.mem_append, List.mem_append]; exact Or.comm) req _

/-- Re-delivering a whole batch is invisible — idempotence of the transport
through the composed gate. -/
theorem ge_replicas_idem (req : EOp → Nat) (cuts : List Era.Cut)
    (log : List Era.Event) (ops : GSet EOp) :
    geGatedOps req (cuts ++ cuts) (log ++ log) (ops ⊔ ops)
      = geGatedOps req cuts log ops := by
  rw [merge_idem ops]
  exact ge_deterministic
    (fun c => by rw [List.mem_append]; exact ⟨fun h => h.elim id id, Or.inl⟩)
    (fun e => by rw [List.mem_append]; exact ⟨fun h => h.elim id id, Or.inl⟩) req _

/-! ## §4. The sign table that DOES hold -/

/-- Growing the op log never removes a permitted op — the one direction that
survives the substrate swap unchanged (`Gated.gated_monotone_log`). -/
theorem ge_monotone_ops {req : EOp → Nat} {cuts : List Era.Cut}
    {log : List Era.Event} {ops ops' : GSet EOp}
    (hgrow : ∀ o : EOp, ops o = true → ops' o = true) {o : EOp}
    (h : geGatedOps req cuts log ops o) : geGatedOps req cuts log ops' o :=
  ⟨hgrow o h.1, h.2⟩

/-- Syncing in a peer's ops only ever adds to the feed — `ge_monotone_ops` at a
merge. -/
theorem ge_merge_only_adds_ops {req : EOp → Nat} {cuts : List Era.Cut}
    {log : List Era.Event} (ops ops' : GSet EOp) {o : EOp}
    (h : geGatedOps req cuts log ops o) :
    geGatedOps req cuts log (ops ⊔ ops') o :=
  ge_monotone_ops (fun a ha => by show (ops a || ops' a) = true; simp [ha]) h

/-- Lowering the requirement only ever permits more: the gate is antitone in
`req`. This is the sign that makes the requirement design safe to specialise —
a deployment tightening `moveReq` (raising some op's bar) can only shrink its
own feed, never smuggle an op in. -/
theorem ge_antitone_req {req req' : EOp → Nat} (hle : ∀ o : EOp, req' o ≤ req o)
    {cuts : List Era.Cut} {log : List Era.Event} {ops : GSet EOp} {o : EOp}
    (h : geGatedOps req cuts log ops o) : geGatedOps req' cuts log ops o :=
  ⟨h.1, Nat.le_trans (hle o) h.2⟩

/-! ## §5. (b) The duel, resolved at the op layer

`Era.duelLog` verbatim: Alice joins (first joiner, so Admin), Bob joins
(Reader), Alice promotes Bob to Admin — then, concurrently, each demotes the
other to Reader. `Authority.duelling_admins_annihilate` says fail-closed kills
both; `Era.duelling_admins_resolved` says arbitration keeps one. Here is what
that difference does to a MOVE. -/

/-- Alice's op: move node 7 under node 5. A plain re-parent, so `moveReq` asks
for Writer. -/
def opAlice : EOp := { t := 1, node := 7, dest := some 5, actor := Era.alice }

/-- Bob's op: move node 3 under node 7. Also a plain re-parent, also Writer —
the two ops are deliberately identical in requirement, so the ONLY thing that
separates them is the arbitrated verdict. -/
def opBob : EOp := { t := 2, node := 3, dest := some 7, actor := Era.bob }

/-- Both duellists' ops are in the log. Whether either reaches replay is the
gate's business, not the log's — the receipt half of the through-line: nothing
is ever deleted, and a gated-out op stays on record. -/
def duelOps : GSet EOp := fun o => o == opAlice || o == opBob

/-- The duel fixture's arbitrated roles, pinned by name — `Era`'s own two
verdicts, cited rather than re-evaluated. Every `decide`-witness in §5 and §7
reads exactly these four numbers, so a reader can check that the witnesses pass
for the stated reason and not by accident of the requirement. -/
theorem ge_duel_roles :
    (Era.resolve Era.setupCuts Era.duelLog).role Era.alice = Era.admin
    ∧ (Era.resolve Era.setupCuts Era.duelLog).role Era.bob = Era.reader
    ∧ (Era.resolve Era.laterCuts Era.duelLog).role Era.alice = Era.reader
    ∧ (Era.resolve Era.laterCuts Era.duelLog).role Era.bob = Era.admin :=
  ⟨Era.duel_pending_verdict.1, Era.duel_pending_verdict.2,
   Era.duel_finalised_verdict.1, Era.duel_finalised_verdict.2⟩

/-- **The duel, at the op layer.** Any two replicas that received the duel's
five events — in any order, with any duplication — compute the SAME op feed,
and that feed is the survivor's: Alice's move is permitted (she is the
arbitrated Admin) and Bob's is denied (demoted to Reader before his op's
requirement is read). Compare `ge_duel_failclosed_denies_both`, where the same
duel through `Gated.gatedOps` denies both moves: arbitration buys a live op
feed where fail-closed leaves an empty one. -/
theorem ge_duel_resolved (l l' : List Era.Event)
    (hl : ∀ e, e ∈ l ↔ e ∈ Era.duelLog) (hl' : ∀ e, e ∈ l' ↔ e ∈ Era.duelLog) :
    geGatedOps moveReq Era.setupCuts l duelOps
        = geGatedOps moveReq Era.setupCuts l' duelOps
      ∧ geGatedOps moveReq Era.setupCuts l duelOps opAlice
      ∧ ¬ geGatedOps moveReq Era.setupCuts l duelOps opBob := by
  have h1 : geGatedOps moveReq Era.setupCuts l duelOps
      = geGatedOps moveReq Era.setupCuts Era.duelLog duelOps :=
    ge_deterministic (fun _ => Iff.rfl) hl moveReq duelOps
  have h2 : geGatedOps moveReq Era.setupCuts l' duelOps
      = geGatedOps moveReq Era.setupCuts Era.duelLog duelOps :=
    ge_deterministic (fun _ => Iff.rfl) hl' moveReq duelOps
  refine ⟨h1.trans h2.symm, ?_, ?_⟩
  · rw [h1]; exact ⟨by decide, by decide⟩
  · rw [h1]; rintro ⟨-, hrole⟩; exact absurd hrole (by decide)

/-- **The arbiter's cut placement carries the op-layer verdict too.** Same five
events, one more announcement record (`Era.laterCuts` finalises Bob's demote
into epoch 2 while Alice's stays pending), and the surviving op flips: Bob's
move is now permitted and Alice's denied. The arbiter never named a winner and
never touched an op — it only ordered events. `Era.duel_finalised_verdict` at
the op layer. -/
theorem ge_duel_arbiter_flips :
    geGatedOps moveReq Era.setupCuts Era.duelLog duelOps opAlice
    ∧ ¬ geGatedOps moveReq Era.setupCuts Era.duelLog duelOps opBob
    ∧ ¬ geGatedOps moveReq Era.laterCuts Era.duelLog duelOps opAlice
    ∧ geGatedOps moveReq Era.laterCuts Era.duelLog duelOps opBob := by
  refine ⟨⟨by decide, by decide⟩, ?_, ?_, ⟨by decide, by decide⟩⟩
  · rintro ⟨-, hrole⟩; exact absurd hrole (by decide)
  · rintro ⟨-, hrole⟩; exact absurd hrole (by decide)

/-! ### The contrast, as a theorem: what fail-closed does to the same duel -/

/-- Alice's move in `Gated`'s vocabulary: it cites grant 1, her root-issued
admin grant (`Authority.aliceRoot`, scope 9 covering node 7). -/
def fcOpAlice : Gated.GOp := { t := 1, node := 7, dest := some 5, cite := 1 }

/-- Bob's move in `Gated`'s vocabulary: it cites grant 2, his own root-issued
admin grant (`Authority.bobRoot`, scope 9 covering node 3). -/
def fcOpBob : Gated.GOp := { t := 2, node := 3, dest := some 7, cite := 2 }

/-- The duel as `Gated.lean` sees it after the sync: both admin grants present,
both revocations present (`Authority.duelling_admins_annihilate`'s state), both
ops in the log. -/
def fcState : Gated.GatedState :=
  (Authority.aliceRoot ⊔ Authority.bobRoot,
   Authority.aliceRevokesBob ⊔ Authority.bobRevokesAlice,
   fun o => o == fcOpAlice || o == fcOpBob)

/-- **Fail-closed denies BOTH moves.** Both ops are in the log and neither is in
the gated feed: each cites a grant whose id the merged revocation set holds, so
`Authority.active_head_unrevoked` refutes any active triple. This is
`Authority.duelling_admins_annihilate` surfaced at the op layer — the exact
cost `Gated.lean` named and could not pay — and it is what
`ge_duel_resolved` buys back. -/
theorem ge_duel_failclosed_denies_both :
    Gated.oplog fcState fcOpAlice = true ∧ Gated.oplog fcState fcOpBob = true
    ∧ ¬ Gated.gatedOps fcState fcOpAlice ∧ ¬ Gated.gatedOps fcState fcOpBob := by
  refine ⟨by decide, by decide, ?_, ?_⟩
  · rintro ⟨-, p, σ, hact, -⟩
    have hu : Gated.revoked fcState 1 = false :=
      Authority.active_head_unrevoked hact
    exact absurd hu (by decide)
  · rintro ⟨-, p, σ, hact, -⟩
    have hu : Gated.revoked fcState 2 = false :=
      Authority.active_head_unrevoked hact
    exact absurd hu (by decide)

/-! ### The requirement lattice is exercised, not collapsed

A third user, so the middle of the role lattice is inhabited: `carol` joins as
a Reader and Alice promotes her to Writer. (User id 3; unrelated to the role
code `Era.admin = 3`.) A Writer may re-parent a node under another node and may
NOT detach one to the root; an Admin may do both. -/

/-- The third user's id. -/
def carol : Nat := 3

/-- Carol joins — a later joiner, so a Reader (§3 op 1). -/
def eCarolJoins : Era.Event := Era.joinEv 6 carol

/-- Alice, the Admin, promotes Carol to Writer — a delegation in ERA's grammar. -/
def eCarolWriter : Era.Event := Era.promoteEv 7 Era.alice carol Era.writer

/-- Alice Admin, Bob Reader, Carol Writer. No cuts: everything is pending, so
the within-epoch tiebreak (event id) is the whole order. -/
def tierLog : List Era.Event := [Era.e1, Era.e2, eCarolJoins, eCarolWriter]

/-- Carol re-parents node 2 under node 1 — a plain move, Writer suffices. -/
def opCarolMove : EOp := { t := 3, node := 2, dest := some 1, actor := carol }

/-- Carol detaches node 2 to the root — `moveReq` asks for Admin. -/
def opCarolDetach : EOp := { t := 4, node := 2, dest := none, actor := carol }

/-- Alice detaches node 2 to the root — she is Admin, so this passes. -/
def opAliceDetach : EOp := { t := 5, node := 2, dest := none, actor := Era.alice }

def tierOps : GSet EOp :=
  fun o => o == opCarolMove || o == opCarolDetach || o == opAliceDetach

/-- The tier fixture's arbitrated roles, pinned: Alice Admin, Carol Writer.
The separation below is then visibly a requirement difference (Writer vs Admin)
on a single actor, not a role difference between actors. -/
theorem ge_tier_roles :
    (Era.resolve [] tierLog).role Era.alice = Era.admin
    ∧ (Era.resolve [] tierLog).role carol = Era.writer := by decide

/-- **The requirement is a real comparison in the role lattice.** The Writer's
plain move is permitted, her root-detach is not, and the Admin's root-detach
is — three verdicts from one arbitrated view, separated by the requirement
rather than by the actor alone. Without this the gate would be a single
Boolean test and "role ≥ requirement" would be decoration. -/
theorem ge_tiers_separate :
    geGatedOps moveReq [] tierLog tierOps opCarolMove
    ∧ ¬ geGatedOps moveReq [] tierLog tierOps opCarolDetach
    ∧ geGatedOps moveReq [] tierLog tierOps opAliceDetach := by
  refine ⟨⟨by decide, by decide⟩, ?_, ⟨by decide, by decide⟩⟩
  rintro ⟨-, hrole⟩
  exact absurd hrole (by decide)

/-! ## §6. (c) Finality — a stability fail-closed cannot offer -/

/-- **Ops permitted under a finalised prefix stay permitted.** Delivering any
batch of still-pending events leaves the finalised feed not merely
non-shrinking but UNCHANGED: `Era.final_view_immune` says the finalised view is
immune to unblessed arrivals, and the gate is a function of that view. This is
what arbitration gives back — the fail-closed composition has no notion of a
settled prefix at all (`gated_revoking_the_cite_kills`). -/
theorem ge_finalised_stable (req : EOp → Nat) (cuts : List Era.Cut)
    (log fresh : List Era.Event)
    (hfresh : ∀ e ∈ fresh, Era.finalized cuts e = false) (ops : GSet EOp) :
    geFinalOps req cuts (log ++ fresh) ops = geFinalOps req cuts log ops := by
  show geOpsOf req (Era.resolveFinal cuts (log ++ fresh)) ops
      = geOpsOf req (Era.resolveFinal cuts log) ops
  rw [Era.final_view_immune cuts log fresh hfresh]

/-- The pointwise reading, which is the sentence the header promises: an op
permitted under the finalised prefix is still permitted after the pending batch
arrives. -/
theorem ge_finalised_op_survives {req : EOp → Nat} {cuts : List Era.Cut}
    {log fresh : List Era.Event}
    (hfresh : ∀ e ∈ fresh, Era.finalized cuts e = false) {ops : GSet EOp}
    {o : EOp} (h : geFinalOps req cuts log ops o) :
    geFinalOps req cuts (log ++ fresh) ops o := by
  rw [ge_finalised_stable req cuts log fresh hfresh ops]; exact h

/-- The duel's setup is exactly this shape: epoch 1 holds both joins and the
promotion, and the two contradictory demotes are pending. Bob's move is
permitted by the finalised prefix, and stays permitted when the whole pending
duel arrives. -/
theorem ge_duel_final_stable :
    geFinalOps moveReq Era.setupCuts [Era.e1, Era.e2, Era.e3] duelOps opBob
    ∧ geFinalOps moveReq Era.setupCuts
        ([Era.e1, Era.e2, Era.e3] ++ [Era.e4, Era.e5]) duelOps opBob := by
  refine ⟨⟨by decide, by decide⟩, ?_⟩
  exact ge_finalised_op_survives (by decide) ⟨by decide, by decide⟩

/-- ⚠ **The finalised feed is not the full feed.** Bob's move clears the
finalised prefix (where he is still Admin) and fails the full view (where the
pending duel has demoted him). `ge_finalised_stable` is a statement about the
FINALISED feed and nothing more; the full feed moves with every pending
arrival, which is §7's whole subject. Stated so the stability result cannot be
misread as stability of what actually reaches replay. -/
theorem ge_final_not_full :
    geFinalOps moveReq Era.setupCuts Era.duelLog duelOps opBob
    ∧ ¬ geGatedOps moveReq Era.setupCuts Era.duelLog duelOps opBob := by
  refine ⟨⟨by decide, by decide⟩, ?_⟩
  rintro ⟨-, hrole⟩
  exact absurd hrole (by decide)

/-- **No prefix of the fail-closed composition is ever final.** One revocation —
of the grant the op cites — removes that op from a `Gated` feed, from ANY
state: no hypothesis is needed, so in particular the kill is available for
every op the feed currently holds. `Gated.lean` therefore cannot state anything
of `ge_finalised_stable`'s shape. This is the positive content of "fail-closed
guarantees shrinkage" and simultaneously its price. -/
theorem gated_revoking_the_cite_kills {gs : Authority.GrantSet}
    {r : Authority.Revoked} {l : GSet Gated.GOp} {o : Gated.GOp} :
    ¬ Gated.gatedOps (gs, r ⊔ (fun i => i == o.cite), l) o := by
  rintro ⟨-, p, σ, hact, -⟩
  have hu : (r ⊔ (fun i => i == o.cite)) o.cite = false :=
    Authority.active_head_unrevoked hact
  have hu' : (r o.cite || (o.cite == o.cite)) = false := hu
  simp at hu'

/-- …and the kill is permanent: every larger revocation set keeps the op out
(`Gated.gated_out_is_forever`). So under fail-closed a permitted op is one
revocation from a death it never recovers from — the exact opposite of
`ge_finalised_op_survives`, where a settled prefix is immune to everything
still pending. -/
theorem gated_kill_is_forever {gs : Authority.GrantSet}
    {r r' : Authority.Revoked} {l : GSet Gated.GOp} {o : Gated.GOp}
    (hgrow : ∀ i, (r ⊔ (fun i => i == o.cite)) i = true → r' i = true) :
    ¬ Gated.gatedOps (gs, r', l) o :=
  Gated.gated_out_is_forever hgrow gated_revoking_the_cite_kills

/-! ## §7. (d) The sign table that FAILS, and the trade

`Gated.gated_antitone` is that file's centerpiece: growth of the authority
substrate never enlarges the feed. Its analogue here is FALSE, and the reason
is structural rather than incidental — ERA can PROMOTE, so an arriving event
can create authority that did not exist. The monotone analogue is false too,
because ERA can DEMOTE. Both are proved, with witnesses. -/

/-- The antitone analogue of `Gated.gated_antitone`, transposed to this
substrate: growth of the EVENT set (cuts and op log fixed) never enlarges the
feed. Named as a `Prop` so it can be refuted by name. -/
def AntitoneInEvents : Prop :=
  ∀ (req : EOp → Nat) (cuts : List Era.Cut) (l l' : List Era.Event)
    (ops : GSet EOp), (∀ e ∈ l, e ∈ l') →
      ∀ o, geGatedOps req cuts l' ops o → geGatedOps req cuts l ops o

/-- The monotone analogue: growth of the event set never shrinks the feed. -/
def MonotoneInEvents : Prop :=
  ∀ (req : EOp → Nat) (cuts : List Era.Cut) (l l' : List Era.Event)
    (ops : GSet EOp), (∀ e ∈ l, e ∈ l') →
      ∀ o, geGatedOps req cuts l ops o → geGatedOps req cuts l' ops o

/-- **Antitonicity forbids enabling — the abstract half of the trade.** For ANY
permission rule antitone under event growth, an op denied on a sub-log is
denied on every extension of it. So a system whose gate shrinks under growth
can never let an arriving event turn a denial into a permission: no promotion,
no re-grant, no repair. (Formally this is the contrapositive of the hypothesis
and nothing more; its content is the reading, and its force is the
instantiation below — the promotion witness is not hypothetical, it is ERA's
§3 op 3 doing exactly its job.) -/
theorem antitone_forbids_enabling {P : List Era.Event → EOp → Prop}
    (hanti : ∀ l l' : List Era.Event, (∀ e ∈ l, e ∈ l') → ∀ o, P l' o → P l o)
    {l l' : List Era.Event} (hsub : ∀ e ∈ l, e ∈ l') {o : EOp}
    (hno : ¬ P l o) : ¬ P l' o :=
  fun h => hno (hanti l l' hsub o h)

/-- Both joins only: Alice is Admin, Bob a Reader. -/
def preLog : List Era.Event := [Era.e1, Era.e2]

/-- …plus Alice's promotion of Bob to Admin (`Era.e3`). -/
def promLog : List Era.Event := [Era.e1, Era.e2, Era.e3]

/-- …plus Alice's demotion of Bob back to Reader (`Era.e4`). -/
def demLog : List Era.Event := [Era.e1, Era.e2, Era.e3, Era.e4]

/-- The promote/demote fixture's arbitrated roles, pinned by name: Reader,
then Admin, then Reader again, all with the cut set empty so the order is the
event-id tiebreak alone. The three witnesses below turn exactly these three
numbers into three verdicts. -/
theorem ge_witness_roles :
    (Era.resolve [] preLog).role Era.bob = Era.reader
    ∧ (Era.resolve [] promLog).role Era.bob = Era.admin
    ∧ (Era.resolve [] demLog).role Era.bob = Era.reader := by decide

/-- Before the promotion, Bob is a Reader and his move is DENIED. -/
theorem ge_promote_denied_before :
    ¬ geGatedOps moveReq [] preLog duelOps opBob := by
  rintro ⟨-, hrole⟩
  exact absurd hrole (by decide)

/-- After the promotion, the same op on the same log-plus-one-event is
PERMITTED. Growth of the event set created authority. -/
theorem ge_promote_permitted_after :
    geGatedOps moveReq [] promLog duelOps opBob :=
  ⟨by decide, by decide⟩

/-- After the demotion, it is denied again. Growth of the event set destroyed
authority. -/
theorem ge_demote_denied_after :
    ¬ geGatedOps moveReq [] demLog duelOps opBob := by
  rintro ⟨-, hrole⟩
  exact absurd hrole (by decide)

/-- ⚠ **`Gated.gated_antitone` has NO analogue here — refuted, with a witness.**
`preLog ⊆ promLog`, Bob's op is permitted on the larger and denied on the
smaller: event growth ENLARGED the feed. This is not a gap in the proof effort;
it is what having a `promote` operation means, and `antitone_forbids_enabling`
says the two cannot coexist. The guarantee `Gated.lean` sells — "late arrivals
only ever remove moves from effect" — is precisely what arbitration spends. -/
theorem ge_not_antitone : ¬ AntitoneInEvents := fun h =>
  antitone_forbids_enabling
    (P := fun l o => geGatedOps moveReq [] l duelOps o)
    (fun l l' hsub o hp => h moveReq [] l l' duelOps hsub o hp)
    (l := preLog) (l' := promLog) (by decide)
    ge_promote_denied_before ge_promote_permitted_after

/-- ⚠ **And the monotone analogue fails too**: `promLog ⊆ demLog`, Bob's op is
permitted on the smaller and denied on the larger. The composed feed is neither
antitone nor monotone in the event set — every instability of the view is
signed in `Gated.lean` and NONE of them is signed here. What replaces the sign
table is `ge_deterministic`: replicas do not disagree about the unstable thing,
and `ge_finalised_stable`: the finalised part of it does not move. -/
theorem ge_not_monotone : ¬ MonotoneInEvents := fun h =>
  ge_demote_denied_after
    (h moveReq [] promLog demLog duelOps (by decide) opBob
      ge_promote_permitted_after)

/-- The exact scope of the two refutations, pinned so neither is read as more
than it is. `AntitoneInEvents` and `MonotoneInEvents` quantify over `req`, so
refuting them takes one policy — and a DEGENERATE policy satisfies both, by
declining to consult the arbitrated view at all: `fun _ => 0` clears every
role, so the feed is just the op log and is trivially unmoved by any event.
`ge_not_antitone` and `ge_not_monotone` therefore say that the general
statements are false, refuted by a policy that does read the role; they do not
say that every `req` fails them. -/
theorem ge_trivial_req_is_both (cuts : List Era.Cut) (l : List Era.Event)
    (ops : GSet EOp) :
    geGatedOps (fun _ => 0) cuts l ops = fun o => ops o = true := by
  funext o
  show (ops o = true ∧ 0 ≤ (Era.resolve cuts l).role o.actor) = (ops o = true)
  exact propext ⟨fun h => h.1, fun h => ⟨h, Nat.zero_le _⟩⟩

/-- ⚠ **Cut growth is not one-directional either.** `Era.setupCuts ⊆
Era.laterCuts` — one extra announcement record, no new events — and the feed
swaps which duellist's op it holds. `Era.lean` declines to claim prefix
stability under cut growth (an equivocating arbiter backdates; the paper
answers with signatures and fraud proofs, out of scope there and here); this is
that non-claim's shape at the op layer. Growing the ARBITER's information is
not growing information about permissions. -/
theorem ge_cut_growth_flips :
    (∀ c ∈ Era.setupCuts, c ∈ Era.laterCuts)
    ∧ geGatedOps moveReq Era.setupCuts Era.duelLog duelOps opAlice
    ∧ ¬ geGatedOps moveReq Era.laterCuts Era.duelLog duelOps opAlice
    ∧ ¬ geGatedOps moveReq Era.setupCuts Era.duelLog duelOps opBob
    ∧ geGatedOps moveReq Era.laterCuts Era.duelLog duelOps opBob := by
  obtain ⟨ha, hb, hc, hd⟩ := ge_duel_arbiter_flips
  exact ⟨by decide, ha, hc, hb, hd⟩

/-- **The trade, in one statement.** Arbitration buys AGREEMENT: every replica
with the same sets permits the same ops (1), and a duel keeps a survivor whose
op is in the feed (2) where fail-closed denies both duellists' ops (5). It
pays with SHRINKAGE: growth of the event set is neither antitone (3) nor
monotone (4), so no `gated_antitone` is available to sign the instability.
`Gated.lean` makes the opposite purchase and `gated_revoking_the_cite_kills`
prices it — under fail-closed every permitted op is one revocation from death,
forever.

This is an exhibition of the incompatibility on ERA's own scenario, not a
general impossibility theorem: what IS general is
`antitone_forbids_enabling` — any antitone rule forbids every promotion — and
that is the load-bearing half. A full impossibility ("no rule is both antitone
and duel-resolving") is undone and doable; §8 gives its shape. -/
theorem ge_trade_agreement_over_shrinkage :
    (∀ (req : EOp → Nat) (cuts cuts' : List Era.Cut)
       (log log' : List Era.Event) (ops : GSet EOp),
        (∀ c, c ∈ cuts ↔ c ∈ cuts') → (∀ e, e ∈ log ↔ e ∈ log') →
        geGatedOps req cuts log ops = geGatedOps req cuts' log' ops)
    ∧ geGatedOps moveReq Era.setupCuts Era.duelLog duelOps opAlice
    ∧ ¬ AntitoneInEvents
    ∧ ¬ MonotoneInEvents
    ∧ ¬ Gated.gatedOps fcState fcOpAlice ∧ ¬ Gated.gatedOps fcState fcOpBob := by
  obtain ⟨-, -, hfcA, hfcB⟩ := ge_duel_failclosed_denies_both
  exact ⟨fun req _ _ _ _ ops hc hl => ge_deterministic hc hl req ops,
         ge_duel_arbiter_flips.1, ge_not_antitone, ge_not_monotone, hfcA, hfcB⟩

/-! ## §8. Honest scope

**What of `Era.lean` this file relies on.** `resolve_same_sets` (§3's
determinism, and it carries no arbiter-honesty hypothesis),
`same_state_same_view` and `encode_merge` (the lattice-level readings),
`final_view_immune` (§6), the role codes and the `authorised`/`applyEvent`
semantics of the paper's §3, and — for every concrete verdict — kernel
evaluation of `resolve` itself. Every non-claim of `Era.lean` is inherited
verbatim: no hash DAG (event ids stand in for hashes), no computation of epoch
membership from causal closure, no signatures, no backdating detection, no
arbiter lists or transparency, no liveness. This file adds no assumption of its
own about ERA.

**What is a premise, not a theorem.** That the writer of an op IS the user its
`actor` field names. `actor` is a bare `Nat` and anyone may write any value
into it; the gate bounds what a role can DO, never who may claim it. This is
`Gated.lean`'s signature premise, and it bites harder here: there, a forged
`cite` still had to name a grant on a live delegation chain, so forgery was
bounded by the grant substrate; here nothing bounds it below the signature
layer. A deployment discharges it exactly as `Authority.lean` says — the
transport authenticates the event and op author — and until it does, this gate
is an authorisation model with an authentication hole, said plainly.

**The attenuation chain is gone, and that is a loss.** `Authority.lean`'s
delegation DAG — per-grant scope, narrowing along every chain
(`chain_scope_descends`), a root ceiling nobody exceeds (`scope_le_root`),
cascade revocation down a subtree — has NO analogue here. ERA's roles are flat
and global: a Writer is a Writer everywhere, there is no per-object scope and
no chain to narrow. `Gated.chain_covers` and `Gated.gated_node_lt_root` are
theorems this file cannot state. Undone, doable, and here is the shape: gate on
the CONJUNCTION — `geGatedOps req cuts log ops o ∧ Gated.permitted st o` over a
state pairing `GEState` with `Gated.GatedState`, `MergeState` again by
`inferInstance`. Every theorem above survives on the left conjunct and every
`Gated` theorem on the right; the composed sign table is the intersection
(shrinkage from the Authority conjunct, non-monotonicity from the Era one), and
the duel's outcome depends on which substrate the duel is fought in — a duel of
roles keeps a survivor, a duel of revocations still annihilates. It is roughly
twenty lines and it was not done because the brief's composition REPLACES the
fail-closed intersection rather than conjoining with it; a system wanting both
scoped attenuation and arbitrated roles should write it.

**The requirement is a policy, and a thin one.** `moveReq` reads only
`o.dest`. Not modelled: per-node ownership ("who may move THIS node"),
destination gating (`Gated.lean` declines it too), and any requirement that
depends on the tree the moves have built. The first two are undone and
trivially doable — `req : EOp → Nat` already takes the whole op, so a
node-indexed or destination-indexed policy is a different `req` and NO theorem
above changes, since all of them quantify over `req`. The third is real work:
a requirement reading the current tree needs `req : Move.Parent → EOp → Nat`,
which makes the gate mutually recursive with the replay it feeds; the shape is
to stratify — resolve roles, filter, replay, and prove the composite still a
function of the two sets, for which `Move.derived_view_sec` supplies the outer
clause and `ge_deterministic` the inner one.

**A general impossibility is undone and doable.** §7 exhibits
"antitone XOR duel-resolving" on ERA's scenario. The general statement wants:
for any permission rule `P` over event sets that (i) is antitone in event
growth and (ii) agrees with `authorised`'s verdict on some log where a promote
takes effect, a contradiction. `antitone_forbids_enabling` is (i)'s consequence
already; what is missing is a clean formulation of (ii) that does not simply
re-assume the witness. Perhaps two hours of work; not attempted here rather
than half-attempted.

**This gates the abstract op layer, not the shipping kernel.** As in
`Gated.lean`: the feed modelled here is `Move.lean`'s, and the executable path
is `Exec.absReplay` behind `uwueave_replay_kernel` with `EraKernel` already
compiling ERA's resolution. Gating there means the request encoding carries the
cut and event lists, a permitted-filter runs ahead of the sort, and the v2
status vocabulary grows a fourth code — skipped-unauthorised, exactly
`EraKernel`'s ✗ mark — so a UI can SHOW the move arbitration removed. An
ordinary flag-day rebuild; listed because it is the next thing to build, not
because adjacency implies it.

**Computability.** Unlike `Gated.permitted` (a `Prop`-valued unbounded
certificate search over `Active`), this gate is decidable outright on delivered
lists: `Era.resolve` computes, `≤` on `Nat` decides, and every witness above is
`decide`. That is a real gain of the substrate swap and it is why the duel
verdicts here are machine-evaluated rather than hand-derived.

**What arbitration does not give.** Full-view stability (`ge_final_not_full`,
`ge_cut_growth_flips`), any bound on what a compromised arbiter can reorder
beyond Era's own least-cut determinism, and liveness of any kind. Determinism
needs no honest arbiter; a STABLE verdict does.
-/

end Uwueave.GatedEra
