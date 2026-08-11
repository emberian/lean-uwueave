//! # uwueave — the coordination-free fragment of a weave, implemented as proved.
//!
//! Companion crate to the Uwueave Lean development (`../Uwueave/`), which
//! classifies weave/loom invariants by *invariant confluence* — the
//! Bailis-necessary-and-sufficient test for whether a replicated structure can
//! maintain an invariant with zero coordination. This crate implements the
//! fragment the theorems say is free, and implements the non-free features the
//! way the theorems say survives (the op-log / derived-view pattern), refusing
//! the shapes they refute.
//!
//! What each module corresponds to:
//!
//! * [`causal`] — an append-only, content-addressed DAG store.
//!   `Grounded` (every edge descends in rank) is enforced *by construction* at
//!   insert; the Lean results `grounded_iconfluent` + `grounded_acyclic` are
//!   why its `merge` needs no cycle check, at any number of replicas.
//! * [`movelog`] — node moving as a grow-only operation log whose
//!   timestamp-ordered, cycle-skipping replay is **authored in Lean**
//!   (`Uwueave/Exec.lean`), compiled to C by lake, and called through a
//!   three-function shim. This crate does not contain a replay
//!   implementation.
//!   `derived_view_sec` is the guarantee; `view_not_stable` is the priced,
//!   documented anomaly (an older remote op can retroactively skip a move you
//!   watched happen) — and the kernel's v3 per-op trace
//!   ([`MoveLog::replay_traced`]) makes that anomaly observable, naming the
//!   exact op each replay skipped.
//!
//!   Format v3 also moved **authorization** inside the kernel: the log
//!   carries a grant/revocation substrate ([`Grant`], `MoveLog::issue`,
//!   `MoveLog::revoke`), each op cites the grant it exercises, and the kernel
//!   filters unauthorised ops ahead of its sort, naming them
//!   [`OpOutcome::SkippedUnauthorised`]. `Uwueave/Gated.lean` §5 proves that
//!   in-kernel gate agrees with the abstract `gatedOps` model — safety with
//!   no hypotheses, both directions under `WF` + `UniqueGrant` — so the gate
//!   this crate ships is the gate the theorems are about. ⚠ There is no
//!   ungated path: an op citing no grant does not replay.
//! * [`seq`] — an RGA-style sequence CRDT with tombstones: a grow-only,
//!   content-addressed element set (union merge + tombstone-OR) whose visible
//!   linearization is **authored in Lean** (`Uwueave/SeqKernel.lean`),
//!   compiled to C by lake, and called through the same shim. This crate does
//!   not contain a linearization implementation. `Uwueave/Sequence.lean` is
//!   the abstract model, and its priced anomalies stay priced:
//!   `interleaving_anomaly` (concurrent runs can strictly alternate) is
//!   reproduced through the real kernel in [`seq`]'s tests, and
//!   `run_order_by_id` (sibling order is id arbitration, not intention)
//!   applies verbatim — the id here being a blake3 content address.
//!
//!   ⚠ Build note, until the root Lean module imports `Uwueave.SeqKernel`:
//!   `lake build` (the default target) does not emit `SeqKernel.c`, so run
//!   `lake build Uwueave.SeqKernel` from the repo root before `cargo build`
//!   (build.rs compiles every `.c` in the emitted-IR tree, so once emitted it
//!   is picked up — and kept fresh only by re-running that command).
//! * [`era`] — ERA epoch-resolved arbitration for group management (join /
//!   write / promote / demote, the duelling-admins conflict): two grow-only
//!   substrates (events value-keyed by eid, arbiter cut records) whose
//!   resolution — epoch assignment, execution order, authorised execution,
//!   the surviving admin — is **authored in Lean**
//!   (`Uwueave/EraKernel.lean`, whose decision layer is *literally*
//!   `Era.resolve`), compiled to C by lake, and called through the same
//!   shim. This crate does not contain an arbitration implementation.
//!   `Era.duelling_admins_resolved` is the guarantee (one deterministic
//!   survivor at every replica); the kernel's `(eid, status)` trace makes
//!   the paper's ✗ marks observable, naming each event the arbitration
//!   skipped.
//!
//!   ⚠ Build note, until the root Lean module imports `Uwueave.EraKernel`:
//!   same stale-C hazard as SeqKernel above — run
//!   `lake build Uwueave.EraKernel` from the repo root before `cargo build`
//!   to (re-)emit `EraKernel.c`. Root wiring kills the hazard for good
//!   (plain `lake build` then keeps the C fresh); that wiring is the
//!   orchestrator's, not this module's.
//!
//! ## What is and is not claimed
//!
//! The replay **semantics** are Lean-authored and compiled in (no Rust twin
//! exists to drift), and the once-open refinement debts are paid:
//! `Move.lean` §3 machine-checks the 2-node bridge both ways (table =
//! kernel-shaped replay; the shipping `absReplay` on the encoded sub-logs =
//! the table's answers), `ExecRefine` §6 proves SEC for the kernel itself
//! (the replay is a function of the op *set* — order- and redelivery-blind,
//! `kernel_derived_view_sec`), and `ExecRefine` §8 proves the input codec
//! round-trips the canonical encoder (`replay_encodeRequest`).
//!
//! What remains unverified is exactly the TCB: this crate's storage/index
//! glue, the marshaller (checked in debug builds byte-for-byte against the
//! *proven* canonical encoder via `Exec.requestCanonicalKernel` — a
//! differential, not a proof: Rust has no formal semantics), the C shim, and
//! Lean's C backend. The tests replay the Lean witnesses
//! scenario-for-scenario through the real kernel, which makes them good
//! tests and zero formal evidence.

pub mod causal;
pub mod era;
mod ffi;
pub mod movelog;
pub mod seq;
pub mod weave;

pub use causal::{CausalWeave, InsertError, MergeError, NodeId};
pub use era::{
    EraEvent, EraEventStatus, EraGroup, EraMergeError, EraMergeStats, EraRecordError,
    EraResolution, EraRole,
};
pub use movelog::{Grant, MoveLog, MoveOp, OpOutcome, TracedReplay};
pub use seq::{SeqCrdt, SeqDeleteError, SeqInsertError, SeqMergeError, SeqMergeStats};
