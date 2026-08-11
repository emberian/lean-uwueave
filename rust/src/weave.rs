//! The loom document, composed — `Weave<T>`: four substrates, one type, one
//! merge, one reader.
//!
//! `Uwueave/WeaveState.lean` classifies a *whole* multiplayer loom document —
//! nodes, contents, activation, bookmarks, pins, grants, a shared quota — and
//! delivers two answers about it: everything but two fields runs
//! coordination-free (`weaveDocFreeVerdict`, over `core_iconfluent`), and the
//! two that do not are named, with the seam that confines them
//! (`weaveDocSeamVerdict` / `weaveDoc_segmented`). The rest of this crate
//! implements the *ingredients* — [`crate::causal`], [`crate::movelog`],
//! [`crate::seq`], [`crate::era`] — as four unrelated pieces. This module is
//! the meal: the type a UI actually holds.
//!
//! ## The citation table — which theorem licenses which part
//!
//! | part | Lean |
//! |---|---|
//! | [`Weave::add_node`], the node DAG | `Acyclicity.causal_dag_free`; `WeaveState.nodesVerdict` — insertion is free, DAG-ness is structural |
//! | nodes survive every merge (a demoted user's node included) | `Catalog.gset_mem_iconfluent` via `nodesVerdict` — a seen node never vanishes |
//! | [`Weave::move_node`], the reparent log | `Acyclicity.acyclicity_not_iconfluent` refutes mutable parents; `Move.derived_view_sec` licenses the op-log; `Exec.absReplay_acyclic` is why the derived view has no cycle |
//! | [`WeaveView::replay`], the retroactive skip | `Move.view_not_stable` — priced, not hidden; surfaced per-op through [`OpOutcome`] |
//! | [`ViewNode::text`], per-node text | `SeqKernel.linearizeK_*` (`_nodup`, `_anchor_precedes`, `_sublist_emitAll`); `Sequence.sequence_view_sec` for convergence; `Sequence.interleaving_anomaly` / `run_order_by_id` are the priced anomalies |
//! | [`Weave::set_activation`], per-user | `Weave.per_user_activation_free`; and per-user is a *theorem*, not taste — `Weave.active_path_not_iconfluent` refutes a shared replicated active path outright |
//! | [`Weave::bookmark`] + its merge check | `Spec.pointsAtExisting_iconfluent` lifted by `WeaveState.keyed_cross_iconfluent` — the cross-field row: a bookmark never dangles *because* nodes only grow |
//! | [`Weave::record_membership`] / [`WeaveView::roles`] | `Era.duelling_admins_resolved` (one deterministic survivor), `Era.resolve_same_sets` (a function of the two sets, not of delivery) |
//! | [`WeaveView::gate`], move ops gated by role | `GatedEra.geGatedOps` — `ge_deterministic` (every replica reads the same feed), `ge_merge_only_adds_ops` (**the gate is a view, never a filter on storage**), `ge_antitone_req` (tightening a requirement can only shrink a feed), `ge_duel_resolved` (the duel keeps a survivor where `Authority.duelling_admins_annihilate` kills both) |
//! | [`Weave::merge`] refusing wholesale on collision | `causal.rs`'s discipline, itself the `Sequence`/`Authority` collision-extractor seam: a same-id-different-bytes encounter voids every convergence statement, so it is corruption, not a merge |
//! | [`Weave::apply_seam_change`] — the two meetings | `WeaveState.weaveDocSeamVerdict`: `weaveDoc_segmented` (same-seam merges preserve the whole invariant set *and the seam*) plus `escalatesGlobally` (global freedom is refuted, with the two-document witness) |
//! | pin, as `Option` rather than a set | `WeaveState.pinsVerdict` = `Spec.atMostOneClash`, and its three named exits; this is exit three (coordinate the pin event), with the type making two pins unrepresentable |
//! | [`Weave::spent`] never waiting | `Segmented.budget_segmented` — spends are free inside an allocation; `budget_not_iconfluent` is why re-allocation is a meeting |
//!
//! ## The two coordination points, and the fact that the API says so
//!
//! Everything above except two fields merges without asking anyone: nodes,
//! text, moves, membership events, activation, bookmarks and spends. The
//! exceptions are **the pin** and **the quota allocation** — together, the
//! [`Seam`]. `weaveDoc_segmented` says merges that hold the seam fixed
//! preserve the entire invariant set; it says nothing whatever about merges
//! that do not, and `weaveDocVerdict` exhibits two complete legal documents
//! whose sync breaks the pin rule. So [`Weave::merge`] **refuses** when the
//! two seams differ ([`WeaveMergeError::SeamDisagreement`]) instead of
//! unioning two pins and calling the result a document. Changing a seam is
//! [`Weave::apply_seam_change`], which every participating replica applies
//! identically — that application *is* the coordination event the theorem
//! prices. How agreement is reached and ordered is the meeting itself and is
//! out of this crate's scope; what the crate refuses to do is pretend the
//! meeting happened.
//!
//! ## What is deliberately not here
//!
//! * **`Authority.lean`'s grant DAG has no Rust substrate**, so the
//!   permission layer is ERA roles alone. That is the `GatedEra.lean` fork
//!   taken on purpose (agreement over shrinkage — see its §"the trade"), not
//!   an omission of convenience: the price is stated there and inherited
//!   here, namely that growth of the membership substrate is **not**
//!   one-directional (`ge_not_antitone`: a promote arriving flips a denied op
//!   to permitted; `ge_not_monotone`: a demote flips it back).
//! * **Node contents are not MV-registers.** `WeaveState.contentsVerdict`
//!   models per-node contents as a multi-value register so concurrent edits
//!   fork visibly; here a node's payload `T` is fixed at creation (it is part
//!   of the content address — [`crate::causal`]), and mutable per-node prose
//!   is the [`crate::seq`] text attached to it. No MV-register substrate
//!   exists in this crate to compose.
//! * **Authenticity is a premise.** A [`UserId`] is a bare `u64` anyone may
//!   write into an op, exactly as `GatedEra.lean` says of its `actor` and
//!   `Authority.lean` says of signatures. Nothing here is a proof that the
//!   user who signed an op is the user it names.
//! * A [`MoveOp`]'s actor **is** its `replica` field. The miniature
//!   identifies one user with one replica id; that identification also makes
//!   the actor the replay order's tiebreak, which is a real design
//!   consequence and is why it is stated here rather than buried.

#![deny(missing_docs)]

use crate::causal::{CausalNode, CausalWeave, InsertError, MergeError, MergeStats, NodeId};
use crate::era::{
    EraEvent, EraGroup, EraMergeError, EraMergeStats, EraRecordError, EraResolution, EraRole,
};
use crate::movelog::{MoveLog, MoveOp, OpOutcome};
use crate::seq::{SeqCrdt, SeqDeleteError, SeqInsertError, SeqMergeError, SeqMergeStats};
use std::collections::{BTreeMap, BTreeSet};

/// A participant. A bare integer, as in `Era.lean`'s miniature — and, per the
/// module docs, an unauthenticated one: authenticity is a premise this crate
/// does not discharge.
pub type UserId = u64;

// ---------------------------------------------------------------------------
// Per-user activation — the free field with the instructive refutation
// ---------------------------------------------------------------------------

/// One user's activation flag for one node: an LWW register, timestamped.
///
/// `Catalog.LWW` verbatim, down to the tie-break — its `Lt` is "later
/// timestamp, or same timestamp and larger value", so on an exact tie the
/// *active* flag wins (`false < true`). The join therefore **selects** one
/// side, which is the whole reason `lww_every_invariant_iconfluent` holds and
/// this field needs no invariant argument of its own.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ActivationFlag {
    /// The write's timestamp. Ordering is the caller's Lamport clock.
    pub ts: u64,
    /// Whether the node is active (expanded / on this user's view path).
    pub active: bool,
}

impl ActivationFlag {
    /// A flag written at `ts`.
    pub fn new(ts: u64, active: bool) -> Self {
        Self { ts, active }
    }

    /// `Catalog.LWW.Lt`: later timestamp, or equal timestamp and larger value.
    fn lt(self, other: Self) -> bool {
        self.ts < other.ts || (self.ts == other.ts && !self.active && other.active)
    }

    /// `Catalog.LWW.join` — the lexicographic max, a genuine semilattice join
    /// (`join_comm` / `join_assoc` / `join_idem`) that always returns one of
    /// its two arguments (`join_selects`).
    pub fn join(self, other: Self) -> Self {
        if self.lt(other) {
            other
        } else {
            self
        }
    }
}

// ---------------------------------------------------------------------------
// The seam — the document's entire coordination surface
// ---------------------------------------------------------------------------

/// **The document seam**: the pin and the quota allocation —
/// `WeaveState.docSeam` exactly.
///
/// `weaveDoc_segmented` proves that merges of legal documents agreeing on
/// this projection preserve the whole invariant set *and* leave the
/// projection where it was. Replicas therefore run free between changes to
/// it, and every change to it is a meeting.
///
/// The pin is an `Option`, not a set. `WeaveState.pinsVerdict` keeps the
/// "at most one pinned node" ceiling as a `GSet` on purpose — the library's
/// demo of what a clash looks like in situ, with `pins_clash` as the repro —
/// and names three exits for an implementation: per-user pins, an
/// MV-register pin, or a coordinated pin event. This is the third, and the
/// type makes the refuted shape unrepresentable rather than merely refused.
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Seam {
    /// The community pin, at most one by construction.
    pub pin: Option<NodeId>,
    /// The storage budget's division among users. Its sum is the budget, and
    /// [`SeamChange::Reallocate`] preserves that sum — `Segmented.BudgetInv`'s
    /// second conjunct.
    ///
    /// Kept **canonical**: a user allocated nothing is absent rather than
    /// present at `0`. Seam equality decides whether two replicas may merge,
    /// so it must be a fact about the division and not about how someone
    /// spelled it.
    pub allocation: BTreeMap<UserId, u64>,
}

impl Seam {
    /// The budget: the sum of the allocation. `BudgetInv B`'s `B`, kept as a
    /// derived quantity so it cannot drift from the allocation it constrains.
    pub fn budget(&self) -> u64 {
        self.allocation.values().copied().fold(0u64, u64::saturating_add)
    }

    /// This user's slice of the budget (`0` for a user with no allocation).
    pub fn allocated(&self, user: UserId) -> u64 {
        self.allocation.get(&user).copied().unwrap_or(0)
    }
}

/// ⚠ **A coordination event.** One of the two changes `weaveDocSeamVerdict`
/// says replicas must agree on: every participant applies the *same*
/// `SeamChange`, and until they all have, [`Weave::merge`] between an
/// applier and a non-applier refuses.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SeamChange {
    /// Pin a node, or clear the pin. `WeaveState.pinsVerdict`'s clash is
    /// exactly two replicas doing this concurrently and syncing.
    SetPin(Option<NodeId>),
    /// Re-divide the budget. `Segmented.budget_not_iconfluent`: two legal
    /// allocations merge into an over-budget one, so this cannot be free.
    Reallocate(BTreeMap<UserId, u64>),
}

/// Why a [`SeamChange`] could not be applied. Every variant leaves the seam
/// untouched.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SeamError {
    /// The node to pin is not on this replica. A replica that has not yet
    /// synced the node cannot join the agreement about it — sync first.
    UnknownNode(NodeId),
    /// The proposed allocation does not sum to the current budget. Budget
    /// changes are not modelled: `BudgetInv B` fixes `B`.
    BudgetChanged {
        /// The budget this document has.
        expected: u64,
        /// The budget the proposed allocation would imply.
        got: u64,
    },
    /// The proposed allocation gives a user less than that user has already
    /// spent — the fiber's own invariant (`s.2 u ≤ s.1 u`) violated at the
    /// moment of the re-allocation. Spends are grow-only; an allocation
    /// cannot retroactively un-spend them.
    AllocationBelowSpend {
        /// The user whose slice would fall below their spend.
        user: UserId,
        /// The proposed slice.
        allocated: u64,
        /// What that user has already spent.
        spent: u64,
    },
}

// ---------------------------------------------------------------------------
// Capabilities — the gate, which is a view
// ---------------------------------------------------------------------------

/// What a user is trying to do, in the role lattice `Era.lean` defines.
///
/// The mapping to roles is `GatedEra.moveReq` generalised: a write into the
/// weave needs Writer (the paper's §3 op 2), and restructuring the shared top
/// level — detaching a node to the root — needs Admin. Tightening a
/// requirement is always safe: `ge_antitone_req` says a higher bar can only
/// shrink a feed, never smuggle an op in.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub enum Capability {
    /// Read the document, bookmark, move your own cursor. Needs membership.
    Read,
    /// Add nodes, edit text, re-parent a node under another node.
    Write,
    /// Detach a node to the root — restructuring the shared top level.
    Detach,
    /// Group management by fiat. (ERA judges membership events at their point
    /// of execution, so this is the *local* bar, not the arbitration.)
    Administer,
}

impl Capability {
    /// The role this capability demands.
    pub fn required_role(self) -> EraRole {
        match self {
            Capability::Read => EraRole::Reader,
            Capability::Write => EraRole::Writer,
            Capability::Detach => EraRole::Admin,
            Capability::Administer => EraRole::Admin,
        }
    }
}

/// The capability a move op demands — `GatedEra.moveReq` verbatim: a move is
/// a write, and a move to the root is a restructure.
pub fn move_capability(dest: Option<NodeId>) -> Capability {
    if dest.is_none() {
        Capability::Detach
    } else {
        Capability::Write
    }
}

/// The gate's verdict on one stored move op — `GatedEra.geGatedOps`'s
/// membership test, made observable.
///
/// A denial is **not** a deletion: the op stays in the log, merges like any
/// other datum, and returns to the feed if its actor is promoted again
/// (`ge_not_antitone` is precisely that this can happen, and is why ERA's
/// arbitration cannot promise shrinkage the way `Gated.gated_antitone` does).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GateOutcome {
    /// The actor's arbitrated role clears the op's requirement; the op is in
    /// the feed that reaches replay.
    Permitted,
    /// The actor's arbitrated role does not clear it. The op is stored, and
    /// invisible to the view.
    Denied {
        /// What the op demanded.
        required: EraRole,
        /// What the arbitration gave its actor.
        actual: EraRole,
    },
}

// ---------------------------------------------------------------------------
// Errors
// ---------------------------------------------------------------------------

/// Why a local operation was refused.
///
/// Op-validation is the application's job — `Weave.lean`'s "reading the
/// verdicts" says it in as many words: FREE means *the merge* preserves the
/// invariant, never that an operation cannot violate it locally. Everything
/// here is that local judgement; none of it filters what a merge accepts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WeaveOpError {
    /// The actor's arbitrated role does not clear the capability's bar.
    PermissionDenied {
        /// Who tried.
        actor: UserId,
        /// What they tried to do.
        capability: Capability,
        /// The role that would have sufficed.
        required: EraRole,
        /// The role the arbitration gives them.
        actual: EraRole,
    },
    /// The named node is not on this replica.
    UnknownNode(NodeId),
    /// This user's spend would exceed their allocation. Local and immediate —
    /// the spend never waits for a peer (`Segmented.budget_segmented`), it
    /// just runs out.
    QuotaExceeded {
        /// Whose budget.
        user: UserId,
        /// Their slice of the budget.
        allocated: u64,
        /// What they have already spent.
        spent: u64,
        /// What this operation asked for.
        requested: u64,
    },
    /// The node DAG refused the insertion.
    Insert(InsertError),
    /// The text CRDT refused the insertion.
    TextInsert(SeqInsertError),
    /// The text CRDT refused the deletion.
    TextDelete(SeqDeleteError),
    /// The membership substrate refused the event (eid re-used for different
    /// content — the uniqueness premise violated).
    Membership(EraRecordError),
}

/// Why a merge was refused — **wholesale**, with nothing half-applied.
///
/// `causal.rs` sets the discipline and this type keeps it across all four
/// substrates: the composite merge is computed on a scratch copy and
/// committed only if every component succeeded, so a failure anywhere leaves
/// the document exactly as it was.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum WeaveMergeError {
    /// ⚠ The two replicas disagree about the pin or the allocation.
    ///
    /// This is the theorem refusing to be misquoted. `weaveDoc_segmented`
    /// licenses merges *within* a fiber of `docSeam`; `weaveDocVerdict`
    /// exhibits two complete legal documents outside one whose merge breaks
    /// the pin rule. Agreeing on the seam ([`Weave::apply_seam_change`], at
    /// both replicas) is the coordination event that makes this merge legal.
    SeamDisagreement {
        /// This replica's seam.
        mine: Box<Seam>,
        /// The other replica's seam.
        theirs: Box<Seam>,
    },
    /// The node DAG refused (id collision, or a delta that was not causally
    /// closed).
    Nodes(MergeError),
    /// A per-node text CRDT refused.
    Text {
        /// The node whose text refused.
        node: NodeId,
        /// The refusal.
        source: SeqMergeError,
    },
    /// The membership substrate refused (eid collision).
    Membership(EraMergeError),
    /// The other replica carries text for a node it does not carry. Its node
    /// set merged first, so this cannot arise from this API — it is a
    /// corrupted or hand-built peer.
    TextForUnknownNode(NodeId),
    /// The other replica bookmarks a node absent from the merged node set —
    /// the cross-field row (`Spec.pointsAtExisting_iconfluent`) violated by
    /// the peer. Free-because-nodes-only-grow is a theorem *about states that
    /// satisfy it*; a peer that already dangles is not one, so the merge
    /// refuses rather than importing a dangling reference.
    DanglingBookmark {
        /// The bookmarking user.
        user: UserId,
        /// The absent node.
        node: NodeId,
    },
    /// The merged spend of some user exceeds their allocation — the peer was
    /// already over budget, so `budget_segmented`'s hypothesis (`I y`) fails
    /// and its conclusion is not available.
    SpendOverAllocation {
        /// The over-spent user.
        user: UserId,
        /// Their slice.
        allocated: u64,
        /// The merged spend.
        spent: u64,
    },
}

/// What a merge did, for tests and telemetry.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct MergeReport {
    /// The node DAG's own statistics.
    pub nodes: MergeStats,
    /// The per-node text statistics, summed over every node merged.
    pub text: SeqMergeStats,
    /// Nodes whose text this replica had never seen and now holds.
    pub texts_created: usize,
    /// The membership substrate's own statistics.
    pub membership: EraMergeStats,
    /// Move ops learned (the log is a set; this is the growth).
    pub moves_learned: usize,
    /// `(user, node)` bookmarks learned.
    pub bookmarks_learned: usize,
    /// Activation registers whose value the merge changed.
    pub activations_advanced: usize,
}

// ---------------------------------------------------------------------------
// The document
// ---------------------------------------------------------------------------

/// **A multiplayer loom document.**
///
/// One type over the crate's four substrates, plus the two plain maps the
/// theory says need no machinery at all:
///
/// * a [`CausalWeave<T>`] of nodes — the branching structure, append-only and
///   content-addressed, free by `Acyclicity.causal_dag_free`;
/// * a [`MoveLog`] of reparenting ops — grow-only storage, whose effective
///   parent map is *derived* through the Lean replay kernel
///   (`Move.derived_view_sec`), because mutable parents are refuted
///   (`acyclicity_not_iconfluent`);
/// * a [`SeqCrdt`] of text per node, linearized by the Lean sequence kernel;
/// * an [`EraGroup`] of membership events and arbiter cuts, resolved by the
///   Lean ERA kernel (`duelling_admins_resolved`);
/// * per-user activation ([`ActivationFlag`], keyed LWW — free by
///   `per_user_activation_free`, and per-user *because*
///   `active_path_not_iconfluent`);
/// * per-user bookmarks (grow-only id sets, with the cross-field row
///   `pointsAtExisting_iconfluent` checked at both ends);
/// * the [`Seam`] — pin and allocation — and the per-user spend it bounds.
///
/// Everything but the seam merges without asking anyone. See the module docs
/// for the full citation table.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Weave<T> {
    nodes: CausalWeave<T>,
    text: BTreeMap<NodeId, SeqCrdt>,
    moves: MoveLog,
    group: EraGroup,
    activation: BTreeMap<UserId, BTreeMap<NodeId, ActivationFlag>>,
    bookmarks: BTreeMap<UserId, BTreeSet<NodeId>>,
    seam: Seam,
    spend: BTreeMap<UserId, u64>,
}

impl<T: AsRef<[u8]> + Clone + PartialEq> Weave<T> {
    /// A fresh document with an agreed genesis allocation. The budget is the
    /// allocation's sum.
    ///
    /// Constructing the document is itself the zeroth coordination event:
    /// every replica must start from the *same* genesis seam, or their first
    /// merge refuses with [`WeaveMergeError::SeamDisagreement`] — which is the
    /// correct answer, not an inconvenience. A user with no allocation may
    /// read, bookmark and navigate but cannot store anything.
    pub fn new<A: IntoIterator<Item = (UserId, u64)>>(allocation: A) -> Self {
        Self {
            nodes: CausalWeave::new(),
            text: BTreeMap::new(),
            moves: MoveLog::new(),
            group: EraGroup::new(),
            activation: BTreeMap::new(),
            bookmarks: BTreeMap::new(),
            seam: Seam {
                pin: None,
                allocation: allocation.into_iter().filter(|(_, q)| *q > 0).collect(),
            },
            spend: BTreeMap::new(),
        }
    }

    // -- substrate access (read-only; mutation goes through the gated API) --

    /// The node DAG.
    pub fn nodes(&self) -> &CausalWeave<T> {
        &self.nodes
    }
    /// The move-op log — *all* ops, including ones the gate currently denies.
    /// Storage is not a filter (`GatedEra.ge_merge_only_adds_ops`).
    pub fn moves(&self) -> &MoveLog {
        &self.moves
    }
    /// The membership substrate (events and arbiter cuts).
    pub fn group(&self) -> &EraGroup {
        &self.group
    }
    /// One node, if present.
    pub fn node(&self, id: &NodeId) -> Option<&CausalNode<T>> {
        self.nodes.get(id)
    }
    /// One node's text CRDT, if any text was ever attached.
    pub fn text_crdt(&self, node: &NodeId) -> Option<&SeqCrdt> {
        self.text.get(node)
    }
    /// One node's visible text, linearized by the Lean sequence kernel.
    /// `None` for a node that has no text CRDT; `Some(vec![])` for one whose
    /// text is entirely tombstoned.
    pub fn text(&self, node: &NodeId) -> Option<Vec<u8>> {
        self.text.get(node).map(|s| s.text())
    }
    /// The seam — pin and allocation. Changing it is
    /// [`Weave::apply_seam_change`], and it is a meeting.
    pub fn seam(&self) -> &Seam {
        &self.seam
    }
    /// What a user has spent of their allocation.
    pub fn spent(&self, user: UserId) -> u64 {
        self.spend.get(&user).copied().unwrap_or(0)
    }
    /// A user's bookmarks. Every id in it names a node this replica holds —
    /// the cross-field row, maintained at insertion and at merge.
    pub fn bookmarks(&self, user: UserId) -> impl Iterator<Item = &NodeId> {
        self.bookmarks.get(&user).into_iter().flatten()
    }
    /// A user's activation flag for a node, if they ever wrote one.
    pub fn activation(&self, user: UserId, node: &NodeId) -> Option<ActivationFlag> {
        self.activation.get(&user).and_then(|m| m.get(node)).copied()
    }

    // -- membership ---------------------------------------------------------

    /// Record a group-management event (join / write / promote / demote).
    ///
    /// Deliberately **ungated**: ERA judges authorisation at each event's
    /// point of execution during `resolve`, and an unauthorised event is kept
    /// and marked (`EraEventStatus::SkippedUnauthorised`, the paper's ✗) —
    /// that *is* the arbitration. A local pre-filter here would replace a
    /// deterministic arbitration with a replica-local one and break
    /// `ge_deterministic`.
    pub fn record_membership(&mut self, event: EraEvent) -> Result<(), WeaveOpError> {
        self.group.record(event).map_err(WeaveOpError::Membership)
    }

    /// Record an arbiter announcement: event `eid` lies in epoch `epoch`'s
    /// closed past (`Era.lean` §2). Infallible and idempotent; even an
    /// equivocating arbiter only re-orders deterministically (the least-epoch
    /// rule), never diverges.
    pub fn record_cut(&mut self, epoch: u64, eid: u64) {
        self.group.record_cut(epoch, eid);
    }

    /// The arbitrated group state: roles, the started flag, and each event's
    /// ✗ or ✓ in execution order.
    ///
    /// A pure function of the two substrates (`Era.resolve_same_sets`), so it
    /// is recomputed rather than cached — a cache would be a second shape of
    /// the same fact, and this crate keeps one shape. Callers that need it
    /// per-frame should hold the [`EraResolution`] themselves.
    pub fn resolution(&self) -> EraResolution {
        self.group.resolve()
    }

    /// A user's arbitrated role — [`EraRole::Outsider`] for anyone the group
    /// never admitted.
    pub fn role(&self, user: UserId) -> EraRole {
        role_in(&self.resolution(), user)
    }

    /// May this user do this, right now, on this replica's view of the group?
    pub fn may(&self, user: UserId, capability: Capability) -> bool {
        self.role(user) >= capability.required_role()
    }

    // -- the free operations ------------------------------------------------

    /// Append a node. Parents are fixed at creation and must already be
    /// present; the id is the content address.
    ///
    /// Free at merge (`causal_dag_free`, `nodesVerdict`): no cycle check, no
    /// coordination, at any number of replicas. Charged against the actor's
    /// storage allocation, and only when the node is genuinely new (the store
    /// is idempotent on identical content, so re-inserting costs nothing).
    pub fn add_node(
        &mut self,
        actor: UserId,
        parents: Vec<NodeId>,
        contents: T,
    ) -> Result<NodeId, WeaveOpError> {
        self.check(actor, Capability::Write)?;
        let bytes = contents.as_ref().len() as u64;
        self.afford(actor, bytes)?;
        let before = self.nodes.len();
        let id = self.nodes.insert(parents, contents).map_err(WeaveOpError::Insert)?;
        if self.nodes.len() > before {
            self.charge(actor, bytes);
        }
        Ok(id)
    }

    /// Insert text into a node, after `anchor` (`None` = the start of that
    /// node's text). Creates the node's text CRDT on first use.
    ///
    /// Convergence is `Sequence.sequence_view_sec` and the order is the Lean
    /// kernel's (`SeqKernel.linearizeK`); its two priced anomalies apply
    /// verbatim — sibling order is id arbitration no user chose
    /// (`run_order_by_id`), and two concurrent runs can come out strictly
    /// alternated (`interleaving_anomaly`).
    pub fn insert_text(
        &mut self,
        actor: UserId,
        node: NodeId,
        anchor: Option<NodeId>,
        contents: &[u8],
    ) -> Result<NodeId, WeaveOpError> {
        self.check(actor, Capability::Write)?;
        if !self.nodes.contains(&node) {
            return Err(WeaveOpError::UnknownNode(node));
        }
        let bytes = contents.len() as u64;
        self.afford(actor, bytes)?;
        let (id, grew) = {
            let seq = self.text.entry(node).or_default();
            let before = seq.len();
            let id = seq.insert(anchor, contents).map_err(WeaveOpError::TextInsert)?;
            (id, seq.len() > before)
        };
        if grew {
            self.charge(actor, bytes);
        }
        Ok(id)
    }

    /// Tombstone one text element. Grow-only and remove-wins, per
    /// [`crate::seq`]; the element keeps its place in the anchor forest, so
    /// everything anchored under it stays where it was
    /// (`linearizeK_sublist_emitAll`). Storage is not refunded — spends are
    /// monotone, and so are tombstones.
    pub fn delete_text(
        &mut self,
        actor: UserId,
        node: NodeId,
        element: NodeId,
    ) -> Result<(), WeaveOpError> {
        self.check(actor, Capability::Write)?;
        match self.text.get_mut(&node) {
            None => Err(WeaveOpError::UnknownNode(node)),
            Some(seq) => seq.delete(&element).map_err(WeaveOpError::TextDelete),
        }
    }

    /// Re-parent a node: record a move op at Lamport time `lamport`, by
    /// `actor`, moving `child` under `dest` (`None` = to the root).
    ///
    /// The op is *stored*, not applied — the effective parent map is derived
    /// at [`Weave::view`] time by the Lean replay kernel, which orders ops by
    /// `(lamport, actor, child, dest)` and skips any that would close a cycle.
    /// Two consequences worth stating at the call site: an older op arriving
    /// later can retroactively un-happen a move you watched succeed
    /// (`Move.view_not_stable`), and a demotion can take this op out of the
    /// feed without deleting it (`GatedEra`, and [`GateOutcome::Denied`]).
    ///
    /// The actor is carried as the op's `replica` field — see the module
    /// docs' last bullet for what that identification costs.
    pub fn move_node(
        &mut self,
        actor: UserId,
        lamport: u64,
        child: NodeId,
        dest: Option<NodeId>,
    ) -> Result<MoveOp, WeaveOpError> {
        self.check(actor, move_capability(dest))?;
        if !self.nodes.contains(&child) {
            return Err(WeaveOpError::UnknownNode(child));
        }
        if let Some(d) = dest {
            if !self.nodes.contains(&d) {
                return Err(WeaveOpError::UnknownNode(d));
            }
        }
        let op = MoveOp { lamport, replica: actor, child, dest };
        self.moves.record(op);
        Ok(op)
    }

    /// Bookmark a node for a user. Grow-only; un-bookmarking is OR-Set
    /// territory (`ORSet.lean`) and is not modelled.
    ///
    /// The node must exist here — that is the cross-field row
    /// (`Spec.pointsAtExisting_iconfluent`) held at its issuing end. Its
    /// merging end is free *because* nodes only grow, which is exactly what
    /// no per-field lift could have told you.
    pub fn bookmark(&mut self, user: UserId, node: NodeId) -> Result<(), WeaveOpError> {
        self.check(user, Capability::Read)?;
        if !self.nodes.contains(&node) {
            return Err(WeaveOpError::UnknownNode(node));
        }
        self.bookmarks.entry(user).or_default().insert(node);
        Ok(())
    }

    /// Set a user's own activation flag for a node at timestamp `ts`.
    ///
    /// Per-user by theorem, not by taste: a *shared* replicated active path is
    /// refuted outright (`Weave.active_path_not_iconfluent` — two users
    /// activate sibling branches and the merge lights both, which is no longer
    /// a path), while the keyed map is free
    /// (`Weave.per_user_activation_free`). Your cursor is yours; a sync never
    /// teleports your view because someone else navigated.
    ///
    /// The node must exist here (local op-validation), but the *merge* carries
    /// no such row — the schema's only cross-field row is `bookmarks`, so a
    /// flag for a node this replica has not seen yet is imported, not refused.
    pub fn set_activation(
        &mut self,
        user: UserId,
        node: NodeId,
        ts: u64,
        active: bool,
    ) -> Result<(), WeaveOpError> {
        self.check(user, Capability::Read)?;
        if !self.nodes.contains(&node) {
            return Err(WeaveOpError::UnknownNode(node));
        }
        let flag = ActivationFlag::new(ts, active);
        let slot = self.activation.entry(user).or_default().entry(node).or_insert(flag);
        *slot = slot.join(flag);
        Ok(())
    }

    // -- the two meetings ---------------------------------------------------

    /// ⚠ **Apply an agreed seam change — a coordination event.**
    ///
    /// This is one of the two operations `weaveDocSeamVerdict` says cannot be
    /// free: pinning, and re-dividing the budget. Every participating replica
    /// applies the identical [`SeamChange`]; until they have, merges across
    /// the disagreement refuse. There is deliberately no merge-time
    /// resolution of divergent seams — `weaveDocVerdict` is the proof that
    /// one would have to invent a policy, and `Necessity.necessity` is the
    /// proof that no library cleverness supplies it.
    ///
    /// Note what this method does *not* take: an actor. Gating an agreed
    /// outcome on a locally-resolved role would make its acceptance
    /// replica-dependent, which is the very divergence the seam exists to
    /// close. Who may call the meeting, and in what order meetings happen, is
    /// the meeting's business.
    pub fn apply_seam_change(&mut self, change: &SeamChange) -> Result<(), SeamError> {
        match change {
            SeamChange::SetPin(None) => {
                self.seam.pin = None;
                Ok(())
            }
            SeamChange::SetPin(Some(id)) => {
                if !self.nodes.contains(id) {
                    return Err(SeamError::UnknownNode(*id));
                }
                self.seam.pin = Some(*id);
                Ok(())
            }
            SeamChange::Reallocate(allocation) => {
                let got = allocation.values().copied().fold(0u64, u64::saturating_add);
                let expected = self.seam.budget();
                if got != expected {
                    return Err(SeamError::BudgetChanged { expected, got });
                }
                for (user, spent) in &self.spend {
                    let allocated = allocation.get(user).copied().unwrap_or(0);
                    if *spent > allocated {
                        return Err(SeamError::AllocationBelowSpend {
                            user: *user,
                            allocated,
                            spent: *spent,
                        });
                    }
                }
                self.seam.allocation =
                    allocation.iter().filter(|(_, q)| **q > 0).map(|(u, q)| (*u, *q)).collect();
                Ok(())
            }
        }
    }

    // -- merge --------------------------------------------------------------

    /// **The composite join.** Every substrate's merge, under one refusal.
    ///
    /// Order matters and is fixed: nodes first, so that text keys and
    /// bookmarks can be checked against the *merged* node set; then text,
    /// moves, membership, bookmarks, activation and spends. The whole thing
    /// runs on a scratch copy and is committed only if every component
    /// succeeded — `causal.rs`'s "refuse wholesale rather than half-apply",
    /// extended to the composite, at the cost of one clone per merge.
    ///
    /// Nothing here filters by permission. A demoted user's node, text and
    /// move ops merge like anyone else's: the gate is a derived view
    /// (`GatedEra.geGatedOps`), and `ge_merge_only_adds_ops` is the statement
    /// that syncing only ever adds to what a replica holds. What the role
    /// change does is change the *feed*, at [`Weave::view`].
    pub fn merge(&mut self, other: &Self) -> Result<MergeReport, WeaveMergeError> {
        if self.seam != other.seam {
            return Err(WeaveMergeError::SeamDisagreement {
                mine: Box::new(self.seam.clone()),
                theirs: Box::new(other.seam.clone()),
            });
        }
        let mut next = self.clone();
        let mut text = SeqMergeStats::default();
        let mut texts_created = 0usize;
        let mut bookmarks_learned = 0usize;
        let mut activations_advanced = 0usize;

        let nodes = next.nodes.merge(&other.nodes).map_err(WeaveMergeError::Nodes)?;

        for (node, their_text) in &other.text {
            if !next.nodes.contains(node) {
                return Err(WeaveMergeError::TextForUnknownNode(*node));
            }
            let mine = next.text.entry(*node).or_insert_with(|| {
                texts_created += 1;
                SeqCrdt::new()
            });
            let stats = mine
                .merge(their_text)
                .map_err(|source| WeaveMergeError::Text { node: *node, source })?;
            text.inserted += stats.inserted;
            text.already_present += stats.already_present;
            text.tombstones_learned += stats.tombstones_learned;
        }

        let moves_before = next.moves.len();
        next.moves.merge(&other.moves);
        let moves_learned = next.moves.len() - moves_before;

        let membership = next.group.merge(&other.group).map_err(WeaveMergeError::Membership)?;

        for (user, theirs) in &other.bookmarks {
            for node in theirs {
                if !next.nodes.contains(node) {
                    return Err(WeaveMergeError::DanglingBookmark { user: *user, node: *node });
                }
            }
            let mine = next.bookmarks.entry(*user).or_default();
            for node in theirs {
                if mine.insert(*node) {
                    bookmarks_learned += 1;
                }
            }
        }

        for (user, theirs) in &other.activation {
            let mine = next.activation.entry(*user).or_default();
            for (node, flag) in theirs {
                match mine.get_mut(node) {
                    None => {
                        mine.insert(*node, *flag);
                        activations_advanced += 1;
                    }
                    Some(slot) => {
                        let joined = slot.join(*flag);
                        if joined != *slot {
                            *slot = joined;
                            activations_advanced += 1;
                        }
                    }
                }
            }
        }

        // Spends: the pointwise max of two grow-only counters — `Escrow`'s
        // join. Legal within a shared allocation (`budget_segmented`), and
        // the check below is that hypothesis, not a policy: a peer already
        // over its slice is outside the theorem.
        for (user, theirs) in &other.spend {
            let slot = next.spend.entry(*user).or_insert(0);
            *slot = (*slot).max(*theirs);
            let allocated = next.seam.allocated(*user);
            if *slot > allocated {
                return Err(WeaveMergeError::SpendOverAllocation {
                    user: *user,
                    allocated,
                    spent: *slot,
                });
            }
        }

        *self = next;
        Ok(MergeReport {
            nodes,
            text,
            texts_created,
            membership,
            moves_learned,
            bookmarks_learned,
            activations_advanced,
        })
    }

    // -- the reader ---------------------------------------------------------

    /// **The view a UI calls**: nodes in document order with their effective
    /// parents and visible text, who may do what, what the gate denied, and
    /// what the replay skipped.
    ///
    /// Three derived layers, in order:
    ///
    /// 1. the group resolution (`Era.resolve`, through the ERA kernel);
    /// 2. the **gated feed** — the sub-log of move ops whose actor's
    ///    arbitrated role clears the op's requirement, which is
    ///    `GatedEra.geGatedOps` exactly, and `ge_deterministic` is why every
    ///    replica holding the same state computes the same one;
    /// 3. the replay of that feed (`Exec.absReplay`, through the move
    ///    kernel), whose output is acyclic by `absReplay_acyclic` and
    ///    order-/redelivery-blind by `kernel_derived_view_sec`.
    ///
    /// Effective parent is `Exec.effParent`: the replay's override where one
    /// exists, else the node's first structural parent. Document order is a
    /// depth-first walk from the roots with siblings in id order —
    /// deterministic arbitration, the same choice `SeqKernel` makes for text
    /// (`run_order_by_id`), and equally not anyone's intention.
    ///
    /// Cost: two kernel calls for moves (one to enumerate the log through its
    /// trace, one to replay the gated feed — collapsed to one when the gate
    /// denies nothing, which `kernel_derived_view_sec` licenses since the feed
    /// is then the same op *set*), one for the group, and one per node that
    /// has text. Nothing is cached; [`Weave::text`] is the single-node read.
    ///
    /// # Panics
    ///
    /// If the effective-parent relation does not reach every node — i.e. it
    /// has a cycle. `Exec.absReplay_acyclic` says it cannot, given the
    /// grounded base [`crate::causal`] maintains by construction, so this is
    /// the same "refuse rather than reinterpret" the other kernels' decoders
    /// take: a lying tree is worse than a stopped one.
    pub fn view(&self) -> WeaveView<'_, T> {
        let resolution = self.group.resolve();

        // Enumerate the log: the traced replay reports exactly one outcome
        // per stored op, which is this crate's only public enumeration of a
        // `MoveLog` (a `MoveLog::ops()` accessor would save this call; keeping
        // a second copy of the log here to avoid it would be two shapes of one
        // fact, which is worse).
        let all = self.moves.replay_traced(&self.nodes);
        let mut feed = MoveLog::new();
        let mut gate = Vec::with_capacity(all.outcomes.len());
        for (op, _) in &all.outcomes {
            let required = move_capability(op.dest).required_role();
            let actual = role_in(&resolution, op.replica);
            if actual >= required {
                feed.record(*op);
                gate.push((*op, GateOutcome::Permitted));
            } else {
                gate.push((*op, GateOutcome::Denied { required, actual }));
            }
        }
        let traced =
            if feed.len() == all.outcomes.len() { all } else { feed.replay_traced(&self.nodes) };

        // Effective parents, then the forest they induce.
        let mut effective: BTreeMap<NodeId, Option<NodeId>> = BTreeMap::new();
        let mut children: BTreeMap<NodeId, BTreeSet<NodeId>> = BTreeMap::new();
        let mut roots: BTreeSet<NodeId> = BTreeSet::new();
        for node in self.nodes.nodes() {
            let parent = match traced.view.get(&node.id()) {
                Some(override_) => *override_,
                None => node.parents().first().copied(),
            };
            effective.insert(node.id(), parent);
            match parent {
                Some(p) => {
                    children.entry(p).or_default().insert(node.id());
                }
                None => {
                    roots.insert(node.id());
                }
            }
        }

        // Reverse indices for the per-node rows.
        let mut bookmarked: BTreeMap<NodeId, Vec<UserId>> = BTreeMap::new();
        for (user, nodes) in &self.bookmarks {
            for node in nodes {
                bookmarked.entry(*node).or_default().push(*user);
            }
        }
        let mut active: BTreeMap<NodeId, Vec<UserId>> = BTreeMap::new();
        for (user, flags) in &self.activation {
            for (node, flag) in flags {
                if flag.active {
                    active.entry(*node).or_default().push(*user);
                }
            }
        }

        let mut rows: Vec<ViewNode<'_, T>> = Vec::with_capacity(self.nodes.len());
        let mut seen: BTreeSet<NodeId> = BTreeSet::new();
        let mut stack: Vec<(NodeId, usize)> = roots.iter().rev().map(|id| (*id, 0)).collect();
        while let Some((id, depth)) = stack.pop() {
            if !seen.insert(id) {
                continue;
            }
            if let Some(kids) = children.get(&id) {
                for kid in kids.iter().rev() {
                    stack.push((*kid, depth + 1));
                }
            }
            let node = match self.nodes.get(&id) {
                Some(n) => n,
                // Unreachable: every id came from `self.nodes`.
                None => continue,
            };
            rows.push(ViewNode {
                id,
                depth,
                effective_parent: effective.get(&id).copied().flatten(),
                structural_parents: node.parents(),
                contents: node.contents(),
                text: self.text.get(&id).map(|s| s.text()).unwrap_or_default(),
                pinned: self.seam.pin == Some(id),
                bookmarked_by: bookmarked.remove(&id).unwrap_or_default(),
                active_for: active.remove(&id).unwrap_or_default(),
            });
        }
        assert_eq!(
            rows.len(),
            self.nodes.len(),
            "the effective-parent relation does not reach every node, i.e. it has a cycle; \
             `Exec.absReplay_acyclic` says the kernel cannot produce one over a grounded base, \
             so this input is corrupt and no honest tree can be rendered from it"
        );

        WeaveView {
            nodes: rows,
            roles: resolution.roles,
            started: resolution.started,
            gate,
            replay: traced.outcomes,
            pin: self.seam.pin,
            allocation: self.seam.allocation.clone(),
            spend: self.spend.clone(),
        }
    }

    // -- internals ----------------------------------------------------------

    /// The local half of the gate: op-validation, which `Weave.lean` names as
    /// the application's job. It never runs at merge.
    fn check(&self, actor: UserId, capability: Capability) -> Result<(), WeaveOpError> {
        let actual = self.role(actor);
        let required = capability.required_role();
        if actual >= required {
            Ok(())
        } else {
            Err(WeaveOpError::PermissionDenied { actor, capability, required, actual })
        }
    }

    /// Would this spend fit in the user's slice? Answered locally and
    /// immediately — a spend never waits (`budget_segmented`), it only runs
    /// out.
    fn afford(&self, user: UserId, bytes: u64) -> Result<(), WeaveOpError> {
        let allocated = self.seam.allocated(user);
        let spent = self.spent(user);
        if spent.saturating_add(bytes) > allocated {
            Err(WeaveOpError::QuotaExceeded { user, allocated, spent, requested: bytes })
        } else {
            Ok(())
        }
    }

    fn charge(&mut self, user: UserId, bytes: u64) {
        let slot = self.spend.entry(user).or_insert(0);
        *slot = slot.saturating_add(bytes);
    }
}

/// A user's role in a resolution — outsiders are everyone the group never
/// named.
fn role_in(resolution: &EraResolution, user: UserId) -> EraRole {
    resolution.roles.get(&user).copied().unwrap_or(EraRole::Outsider)
}

// ---------------------------------------------------------------------------
// The view
// ---------------------------------------------------------------------------

/// One node as a reader sees it: where it hangs *now*, what it says, and who
/// cares about it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ViewNode<'a, T> {
    /// The content address.
    pub id: NodeId,
    /// Depth in the derived forest; roots are `0`.
    pub depth: usize,
    /// The parent the replay put it under — `Exec.effParent`: the override if
    /// the gated feed produced one, else the first structural parent. `None`
    /// is the root.
    pub effective_parent: Option<NodeId>,
    /// The parents fixed at creation, which no move ever changes — they are
    /// part of the id.
    pub structural_parents: &'a [NodeId],
    /// The node's immutable payload.
    pub contents: &'a T,
    /// The visible text attached to this node, tombstones filtered, in the
    /// Lean kernel's order. Empty when the node has no text CRDT.
    pub text: Vec<u8>,
    /// Whether this node is *the* pinned node.
    pub pinned: bool,
    /// Users who have bookmarked it.
    pub bookmarked_by: Vec<UserId>,
    /// Users for whom it is currently active.
    pub active_for: Vec<UserId>,
}

/// **The document, ready to render.** A snapshot — every field is derived,
/// nothing here is replicated.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct WeaveView<'a, T> {
    /// Every node, depth-first from the roots, siblings in id order.
    pub nodes: Vec<ViewNode<'a, T>>,
    /// The arbitrated roles of every user the group has named
    /// (`Era.duelling_admins_resolved`: one deterministic survivor of a duel,
    /// the same one at every replica).
    pub roles: BTreeMap<UserId, EraRole>,
    /// Has any join executed? (`Era.GroupView.started`.)
    pub started: bool,
    /// Every stored move op with the gate's verdict —
    /// `GatedEra.geGatedOps`'s membership test, itemised. Denials are
    /// *visible*, because the op is still there.
    pub gate: Vec<(MoveOp, GateOutcome)>,
    /// Every op in the gated feed with the replay kernel's verdict. A
    /// [`OpOutcome::SkippedCycle`] here is `Move.view_not_stable` happening
    /// to a specific op — the move an older remote op retroactively
    /// un-happened.
    pub replay: Vec<(MoveOp, OpOutcome)>,
    /// The community pin (seam).
    pub pin: Option<NodeId>,
    /// The storage allocation (seam).
    pub allocation: BTreeMap<UserId, u64>,
    /// What each user has spent of it.
    pub spend: BTreeMap<UserId, u64>,
}

impl<'a, T> WeaveView<'a, T> {
    /// A user's arbitrated role; [`EraRole::Outsider`] if the group never
    /// named them.
    pub fn role(&self, user: UserId) -> EraRole {
        self.roles.get(&user).copied().unwrap_or(EraRole::Outsider)
    }

    /// May this user do this, on the state this view was taken from?
    pub fn may(&self, user: UserId, capability: Capability) -> bool {
        self.role(user) >= capability.required_role()
    }

    /// One row, by id.
    pub fn node(&self, id: &NodeId) -> Option<&ViewNode<'a, T>> {
        self.nodes.iter().find(|n| &n.id == id)
    }

    /// The ids in document order — what a tree widget iterates.
    pub fn order(&self) -> Vec<NodeId> {
        self.nodes.iter().map(|n| n.id).collect()
    }

    /// The move ops the gate denied, with what they needed and what their
    /// actor has. Stored, merged, replicated — and not in effect.
    pub fn denied_moves(&self) -> impl Iterator<Item = (&MoveOp, EraRole, EraRole)> {
        self.gate.iter().filter_map(|(op, outcome)| match outcome {
            GateOutcome::Permitted => None,
            GateOutcome::Denied { required, actual } => Some((op, *required, *actual)),
        })
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    const ALICE: UserId = 1;
    const BOB: UserId = 2;
    const CAROL: UserId = 3;
    const DAVE: UserId = 4;

    type Doc = Weave<Vec<u8>>;

    /// A document both replicas start from: the genesis seam (agreed at
    /// construction), Alice admin by first join, Bob promoted to Writer, and
    /// a root with two children.
    fn base() -> (Doc, NodeId, NodeId, NodeId) {
        let mut w: Doc = Weave::new([(ALICE, 4096), (BOB, 4096)]);
        w.record_membership(EraEvent::join(1, ALICE)).unwrap();
        w.record_membership(EraEvent::join(2, BOB)).unwrap();
        w.record_membership(EraEvent::promote(3, ALICE, BOB, EraRole::Writer)).unwrap();
        w.record_cut(1, 1);
        w.record_cut(1, 2);
        w.record_cut(1, 3);
        let root = w.add_node(ALICE, vec![], b"root".to_vec()).unwrap();
        let n1 = w.add_node(ALICE, vec![root], b"n1".to_vec()).unwrap();
        let n2 = w.add_node(ALICE, vec![root], b"n2".to_vec()).unwrap();
        (w, root, n1, n2)
    }

    /// **The convergence test.** Two replicas go offline and diverge on every
    /// substrate at once — nodes, text, moves, membership, bookmarks,
    /// activation, spends — then merge in both directions and agree on
    /// everything a reader can see. The transport differs (ERA keeps arrival
    /// order); the *view* is the convergence object, exactly as
    /// `Era.resolve_same_sets` / `GatedEra.ge_replicas_agree` frame it.
    #[test]
    fn two_replicas_diverge_on_every_substrate_and_agree_both_ways() {
        let (shared, root, n1, n2) = base();
        let mut a = shared.clone();
        let mut b = shared.clone();

        // Alice, offline: a node, text, a bookmark, her cursor, a late move.
        let a1 = a.add_node(ALICE, vec![n1], b"alice's leaf".to_vec()).unwrap();
        let ha = a.insert_text(ALICE, root, None, b"hello ").unwrap();
        a.insert_text(ALICE, root, Some(ha), b"world").unwrap();
        a.bookmark(ALICE, a1).unwrap();
        a.set_activation(ALICE, n1, 7, true).unwrap();
        a.move_node(ALICE, 9, n1, Some(n2)).unwrap();
        a.record_membership(EraEvent::join(10, CAROL)).unwrap();

        // Bob, offline: his own node, a concurrent edit of the same node's
        // text, his own bookmark and cursor, and an OLDER move — the
        // `view_not_stable` shape, inside the composite.
        let b1 = b.add_node(BOB, vec![n2], b"bob's leaf".to_vec()).unwrap();
        b.insert_text(BOB, root, None, b"oh, ").unwrap();
        b.bookmark(BOB, n2).unwrap();
        b.set_activation(BOB, n2, 3, true).unwrap();
        b.move_node(BOB, 4, n2, Some(n1)).unwrap();
        b.record_membership(EraEvent::join(11, DAVE)).unwrap();

        let mut ab = a.clone();
        ab.merge(&b).unwrap();
        let mut ba = b.clone();
        ba.merge(&a).unwrap();

        assert_ne!(ab, ba, "the transports differ — the agreement below is the theorem");

        let va = ab.view();
        let vb = ba.view();
        assert_eq!(va, vb, "every derived field agrees, both merge directions");

        // Spelled out, so a failure says which substrate broke.
        assert_eq!(va.order(), vb.order(), "document order");
        assert_eq!(ab.nodes().len(), 5, "root + 2 + both offline leaves");
        assert!(ab.nodes().contains(&a1) && ab.nodes().contains(&b1), "both leaves merged");
        assert_eq!(ab.text(&root), ba.text(&root), "text converges");
        assert_eq!(ab.text(&root).unwrap().len(), b"oh, hello world".len(), "no write lost");
        assert_eq!(va.roles, vb.roles, "roles converge");
        assert_eq!(va.role(CAROL), EraRole::Reader, "Carol's join, seen only by Alice");
        assert_eq!(va.role(DAVE), EraRole::Reader, "Dave's join, seen only by Bob");
        assert_eq!(
            ab.bookmarks(ALICE).copied().collect::<Vec<_>>(),
            ba.bookmarks(ALICE).copied().collect::<Vec<_>>(),
            "bookmarks converge"
        );
        assert_eq!(ab.activation(BOB, &n2), ba.activation(BOB, &n2), "activation converges");
        assert_eq!(ab.spent(ALICE), ba.spent(ALICE), "spends converge");
        assert!(ab.nodes().grounded(), "the DAG is still grounded after merging");

        // Every bookmark points at a node that exists — the cross-field row,
        // observed on the merged document (`pointsAtExisting_iconfluent`).
        for user in [ALICE, BOB] {
            for id in ab.bookmarks(user) {
                assert!(ab.nodes().contains(id), "no bookmark dangles");
            }
        }

        // `Move.view_not_stable` inside the composite: Bob's older op (t=4)
        // wins the order and Alice's (t=9) is retroactively skipped.
        let outcome = |op_child: NodeId| {
            va.replay.iter().find(|(o, _)| o.child == op_child).map(|(_, s)| *s)
        };
        assert_eq!(outcome(n2), Some(OpOutcome::Applied), "the older op applied");
        assert_eq!(outcome(n1), Some(OpOutcome::SkippedCycle), "the newer one was skipped");
        assert_eq!(va.node(&n2).unwrap().effective_parent, Some(n1), "the view shows it");
    }

    /// **The permission test.** A demoted user's contribution merges as
    /// DATA — the gate is a view, not a filter on storage
    /// (`GatedEra.ge_merge_only_adds_ops`) — while every derived surface
    /// reflects the demotion: the roster, the capability query, the gated
    /// move feed, and the effective parent the move would have set.
    #[test]
    fn demoted_users_work_still_merges_the_gate_is_a_view() {
        let (shared, _root, n1, n2) = base();
        let mut bob_replica = shared.clone();
        let mut alice_replica = shared.clone();

        // Bob, a Writer at the time, contributes offline.
        let bnode = bob_replica.add_node(BOB, vec![n1], b"bob was here".to_vec()).unwrap();
        bob_replica.insert_text(BOB, n1, None, b"bob's prose").unwrap();
        let bmove = bob_replica.move_node(BOB, 5, n1, Some(n2)).unwrap();

        // On his own replica the op is in the feed and in effect.
        let before = bob_replica.view();
        assert_eq!(before.role(BOB), EraRole::Writer);
        assert_eq!(before.node(&n1).unwrap().effective_parent, Some(n2), "his move applied");
        assert_eq!(before.denied_moves().count(), 0);

        // Alice, concurrently, demotes him.
        alice_replica.record_membership(EraEvent::demote(4, ALICE, BOB, EraRole::Reader)).unwrap();

        let mut merged = bob_replica.clone();
        merged.merge(&alice_replica).unwrap();
        let mut other_way = alice_replica.clone();
        other_way.merge(&bob_replica).unwrap();
        assert_eq!(merged.view(), other_way.view(), "both directions agree");

        // The data is all there — `nodesVerdict`: a seen node never vanishes,
        // and no merge ever consulted a role to decide that.
        assert!(merged.nodes().contains(&bnode), "his node merged");
        assert_eq!(merged.text(&n1).unwrap(), b"bob's prose", "his text merged");
        assert_eq!(merged.moves().len(), 1, "his move op is still stored");

        // The view reflects the role change, everywhere it should.
        let after = merged.view();
        assert_eq!(after.role(BOB), EraRole::Reader, "the roster changed");
        assert!(!merged.may(BOB, Capability::Write), "and the capability query with it");
        assert_eq!(
            after.denied_moves().collect::<Vec<_>>(),
            vec![(&bmove, EraRole::Writer, EraRole::Reader)],
            "the op is denied, named, and visible — not deleted"
        );
        assert_eq!(
            after.node(&n1).unwrap().effective_parent,
            after.node(&n1).unwrap().structural_parents.first().copied(),
            "the gated-out move is not in effect: n1 is back at its structural parent"
        );
        assert!(after.node(&bnode).is_some(), "his node is in the rendered tree");

        // Future ops of his are refused locally — op-validation, the half of
        // the gate that is not a view.
        assert!(matches!(
            merged.add_node(BOB, vec![n1], b"more".to_vec()),
            Err(WeaveOpError::PermissionDenied { actor: BOB, required: EraRole::Writer, .. })
        ));
        // But he can still read, bookmark and navigate.
        assert!(merged.bookmark(BOB, n1).is_ok());
        assert!(merged.set_activation(BOB, n1, 2, true).is_ok());
    }

    /// A move to the ROOT needs Admin, not Writer (`GatedEra.moveReq`): the
    /// same op, from the same user, differs only in destination.
    #[test]
    fn detaching_to_the_root_needs_admin() {
        let (mut w, _root, n1, _n2) = base();
        assert!(matches!(
            w.move_node(BOB, 1, n1, None),
            Err(WeaveOpError::PermissionDenied { capability: Capability::Detach, .. })
        ));
        assert!(w.move_node(BOB, 1, n1, Some(_n2)).is_ok(), "the same move under a node is fine");
        assert!(w.move_node(ALICE, 2, n1, None).is_ok(), "the admin may detach");
    }

    /// **The seam refuses to pretend.** `weaveDocVerdict`'s witness pair, at
    /// the keyboard: two replicas each pin a node, and the merge that would
    /// show two pins does not happen. Agreeing (both applying the same
    /// change) is what makes the merge legal again.
    #[test]
    fn divergent_pins_refuse_to_merge_and_agreement_repairs_it() {
        let (shared, _root, n1, n2) = base();
        let mut a = shared.clone();
        let mut b = shared.clone();

        a.apply_seam_change(&SeamChange::SetPin(Some(n1))).unwrap();
        b.apply_seam_change(&SeamChange::SetPin(Some(n2))).unwrap();

        let snapshot = a.clone();
        match a.merge(&b) {
            Err(WeaveMergeError::SeamDisagreement { .. }) => {}
            other => panic!("expected SeamDisagreement, got {other:?}"),
        }
        assert_eq!(a, snapshot, "refused wholesale, nothing half-applied");

        // The meeting: both apply the same change.
        a.apply_seam_change(&SeamChange::SetPin(Some(n2))).unwrap();
        a.merge(&b).unwrap();
        assert_eq!(a.seam().pin, Some(n2));
        assert!(a.view().node(&n2).unwrap().pinned);
        assert!(!a.view().node(&n1).unwrap().pinned, "at most one pin, structurally");
    }

    /// Spends never wait inside an allocation, and re-allocation is the only
    /// coordination the budget needs — with both of the refusals that keep
    /// `BudgetInv` true across it.
    #[test]
    fn spends_are_free_reallocation_is_a_meeting() {
        let (shared, root, _n1, _n2) = base();
        let mut a = shared.clone();
        let mut b = shared.clone();

        // Each spends against their own slice, offline, without waiting.
        a.insert_text(ALICE, root, None, &[b'a'; 100]).unwrap();
        b.insert_text(BOB, root, None, &[b'b'; 200]).unwrap();
        a.merge(&b).unwrap();
        // Alice already paid for `base`'s three nodes ("root", "n1", "n2" = 8
        // bytes); Bob paid for nothing there.
        assert_eq!(a.spent(ALICE), 8 + 100, "her nodes in `base`, plus this text");
        assert_eq!(a.spent(BOB), 200);

        // Seam equality decides whether two replicas may merge, so it is a
        // fact about the division, not about how it was spelled.
        let spelled: Doc = Weave::new([(ALICE, 10), (BOB, 0)]);
        let omitted: Doc = Weave::new([(ALICE, 10)]);
        assert_eq!(spelled.seam(), omitted.seam());

        // Running out is local and immediate — never a wait.
        let mut poor: Doc = Weave::new([(ALICE, 8)]);
        poor.record_membership(EraEvent::join(1, ALICE)).unwrap();
        assert!(matches!(
            poor.add_node(ALICE, vec![], vec![0u8; 9]),
            Err(WeaveOpError::QuotaExceeded { allocated: 8, requested: 9, .. })
        ));

        // Re-allocation: the budget is fixed, and nobody's slice may drop
        // below what they already spent.
        assert_eq!(
            a.apply_seam_change(&SeamChange::Reallocate(BTreeMap::from([
                (ALICE, 4096),
                (BOB, 5000)
            ]))),
            Err(SeamError::BudgetChanged { expected: 8192, got: 9096 })
        );
        assert_eq!(
            a.apply_seam_change(&SeamChange::Reallocate(BTreeMap::from([
                (ALICE, 8192),
                (BOB, 0)
            ]))),
            Err(SeamError::AllocationBelowSpend { user: BOB, allocated: 0, spent: 200 })
        );
        let agreed = SeamChange::Reallocate(BTreeMap::from([(ALICE, 7000), (BOB, 1192)]));
        a.apply_seam_change(&agreed).unwrap();
        b.apply_seam_change(&agreed).unwrap();
        // A replica that missed the meeting cannot merge; one that made it can.
        assert!(matches!(
            a.clone().merge(&shared),
            Err(WeaveMergeError::SeamDisagreement { .. })
        ));
        a.merge(&b).unwrap();
        assert_eq!(a.seam().allocated(ALICE), 7000);
    }

    /// The cross-field row at its merging end: a peer whose bookmark dangles
    /// is refused rather than imported. (Built by hand — the API cannot
    /// produce one, which is the row holding at its issuing end.)
    #[test]
    fn a_dangling_bookmark_is_refused_wholesale() {
        let (shared, _root, n1, _n2) = base();
        let mut peer = shared.clone();
        let ghost = [9u8; 32];
        peer.bookmarks.entry(ALICE).or_default().insert(ghost);
        let mut target = shared.clone();
        assert_eq!(
            target.merge(&peer),
            Err(WeaveMergeError::DanglingBookmark { user: ALICE, node: ghost })
        );
        assert_eq!(target, shared, "nothing half-applied");
        assert!(shared.clone().merge(&{
            let mut ok = shared.clone();
            ok.bookmark(ALICE, n1).unwrap();
            ok
        })
        .is_ok());
    }
}
