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
//!   watched happen).
//!
//! ## What is and is not claimed
//!
//! The Lean theorems are about the *design*; the replay **semantics** are
//! Lean-authored and compiled in (no Rust twin exists to drift). What remains
//! unverified: this crate's storage/index/codec glue, the C shim, Lean's C
//! backend, and the refinement of `Exec.lean`'s kernel to `Move.lean`'s
//! abstract model — the last is named open work in `Exec.lean`'s header. The
//! tests replay the Lean witnesses scenario-for-scenario through the real
//! kernel, which makes them good tests and zero formal evidence.

pub mod causal;
mod ffi;
pub mod movelog;

pub use causal::{CausalWeave, InsertError, MergeError, NodeId};
pub use movelog::{MoveLog, MoveOp};
