//! # leanuweave — the coordination-free fragment of a weave, implemented as proved.
//!
//! Companion crate to the Leanuweave Lean development (`../Leanuweave/`), which
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
//! * [`movelog`] — node moving as a grow-only operation log with
//!   timestamp-ordered, cycle-skipping replay (the Kleppmann move-op shape).
//!   `derived_view_sec` is the guarantee; `view_not_stable` is the priced,
//!   documented anomaly (an older remote op can retroactively skip a move you
//!   watched happen).
//!
//! ## What is and is not claimed
//!
//! The Lean theorems are about the *design*: the merge semilattice, the
//! invariants, the counterexamples. **This Rust is an unverified implementation
//! of that design.** The tests replay the Lean witnesses scenario-for-scenario,
//! which makes them good tests and zero formal evidence. No claim of
//! "translation validation" or refinement is made — there is no formal
//! semantics of Rust to state one in.

pub mod causal;
pub mod movelog;

pub use causal::{CausalWeave, InsertError, MergeError, NodeId};
pub use movelog::{MoveLog, MoveOp};
