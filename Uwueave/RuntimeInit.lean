/-
# Uwueave.RuntimeInit -- the complete native runtime initializer

This deliberately data-free module is the single source of truth for the
Lean object graph linked by the Rust crate.  Its generated initializer visits
exactly the transitive import closure of the five exported runtime kernels.
`rust/build.rs` reads Lake's generated setup description for this module and
asks Lake for one native object per member of that same closure; the C shim
calls only this module's initializer.

Keep declarations and executable data out of this file.  Runtime behavior
belongs to the imported kernels, while this root owns only initialization and
link-closure selection.
-/
import Uwueave.Exec
import Uwueave.SeqKernel
import Uwueave.EraKernel
import Uwueave.Preo.ArtifactJournalKernel
import Uwueave.RuntimeAuthV4Kernel
