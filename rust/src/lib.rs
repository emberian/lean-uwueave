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
//! * [`auth`] — three narrow Lean-owned UWV4 boundaries. The legacy kind-1
//!   endpoint bounds and canonically classifies signed-request bytes with five
//!   decode refusals. The context-bound kind-3 endpoint additionally enforces
//!   eight shape and three host-width refusals and returns the exact canonical
//!   kind-4 projection. The admission-trace endpoint validates the complete
//!   canonical v2 certificate, including that projection and the exact
//!   FORMAT-v3 request, response, selected slot, operation, and status. Rust
//!   parses only Lean-owned response grammars; this module does not itself
//!   verify signatures, decide authority or membership, execute a move, or
//!   persist anything.
//! * [`auth_verifier`] — a deployment-owned verifier seam plus one
//!   context/document/genesis/issuer/epoch-scoped keyed-BLAKE3 symmetric-MAC
//!   profile. Its acceptance is trusted host evidence, not a public-key
//!   signature proof or an authorization decision.
//! * [`auth_runtime`] — the fail-closed raw kind-3 admission orchestrator. It
//!   orders Lean projection, exact-byte verification, durable retry/collision
//!   classification, fixed document/genesis/context/execution scope, immutable
//!   context pinning, stable-id resolution, independent authority and
//!   membership checks, concrete Lean move preflight, mandatory semantic-trace
//!   validation, durable append, then in-memory commit. Verified retry is a
//!   separate prior-certificate reference rather than a claim that later
//!   policy stages reran. Externally pinned recovery rechecks every stored
//!   certificate, repeats the providers and shipping kernel, and requires an
//!   exact rebuilt record before replaying each stored move.
//!   Policy providers, the verifier, the external pin, host storage, and the
//!   FFI remain trusted deployment boundaries.
//! * [`causal`] — an append-only, content-addressed DAG store.
//!   `Grounded` (every edge descends in rank) is enforced *by construction* at
//!   insert; the Lean results `grounded_iconfluent` + `grounded_acyclic` are
//!   why its `merge` needs no cycle check, at any number of replicas.
//! * [`movelog`] — node moving as a grow-only operation log whose
//!   timestamp-ordered, cycle-skipping replay is **authored in Lean**
//!   (`Uwueave/Exec.lean`), compiled to C by lake, and called through a
//!   small C shim. This crate does not contain a replay
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
//!   The root Lean module imports `Uwueave.SeqKernel`, so a plain `lake build`
//!   keeps the generated C fresh before Cargo compiles it.
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
//!   The root Lean module also imports `Uwueave.EraKernel`, so the same plain
//!   `lake build` refreshes this generated C boundary.
//! * [`persistence`] — five deliberately distinct pure-Rust journal domains:
//!   canonical Lean-owned Preoscript artifacts, typed operation/checkpoint
//!   reconstruction of the authoritative [`MoveLog`] substrate, causally
//!   closed history, durable out-of-order arrival, and checked authenticated
//!   moves. The authenticated domain adds nonce/operation indexes, an unkeyed
//!   prior-head chain, and reopen relative to an exact caller-supplied external
//!   pin. Domain separation prevents one format being decoded as another;
//!   flush/sync, torn-tail recovery, external pin custody, and stable-media
//!   behavior remain deployment policies rather than filesystem theorems.
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

#![deny(unsafe_code)]
#![deny(unsafe_op_in_unsafe_fn)]

pub mod auth;
pub mod auth_runtime;
pub mod auth_verifier;
pub mod causal;
pub mod era;
#[allow(unsafe_code)]
mod ffi;
pub mod movelog;
pub mod persistence;
pub mod seq;
pub mod status;
pub mod weave;

pub use causal::{CausalWeave, InsertError, MergeError, NodeId, NodeIdDisplay};
pub use era::{
    EraEvent, EraEventStatus, EraGroup, EraMergeError, EraMergeStats, EraRecordError,
    EraResolution, EraRole,
};
pub use movelog::{
    CertifiedReplay, Grant, MoveLog, MoveOp, OpOutcome, ProspectiveCertifiedReplay,
    ReplayRequestSlot, TracedReplay,
};
pub use seq::{SeqCrdt, SeqDeleteError, SeqInsertError, SeqMergeError, SeqMergeStats};

/// Safe, deliberately hidden adapters used only by the repository's native
/// measurement example. Keeping the example on this side of the FFI boundary
/// ensures that every Rust `unsafe` operation remains in `ffi.rs`.
#[doc(hidden)]
pub mod native_bench {
    /// Return the byte length produced by one Lean replay-kernel call.
    pub fn replay_output_len(input: &[u8]) -> usize {
        crate::ffi::replay_kernel(input).len()
    }

    /// Ask the Lean compatibility endpoint whether one request is canonical.
    pub fn request_canonical(input: &[u8]) -> bool {
        crate::ffi::request_canonical(input)
    }

    /// Return the byte length produced by one Lean sequence-kernel call.
    pub fn seq_output_len(input: &[u8]) -> usize {
        crate::ffi::seq_kernel(input).len()
    }
}
