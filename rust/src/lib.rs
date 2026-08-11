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
//!   watched happen) — and the kernel's v2 per-op trace
//!   ([`MoveLog::replay_traced`]) makes that anomaly observable, naming the
//!   exact op each replay skipped.
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
mod ffi;
pub mod movelog;

pub use causal::{CausalWeave, InsertError, MergeError, NodeId};
pub use movelog::{MoveLog, MoveOp, OpOutcome, TracedReplay};
