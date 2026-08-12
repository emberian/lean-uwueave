//! The small FFI surface to the Lean-compiled kernels. See `shim.c` for the
//! C side; see `Uwueave/Exec.lean` (move replay), `Uwueave/SeqKernel.lean`
//! (sequence linearization) and `Uwueave/EraKernel.lean` (ERA arbitration)
//! for runtime semantics, plus `Uwueave/Preo/ArtifactJournalKernel.lean` for
//! canonical artifact-v2 admission. Those Lean modules own the byte-level
//! contracts; this file only owns typed calls and memory transfer.

use std::sync::Once;

extern "C" {
    fn shim_uweave_init();
    fn shim_uweave_encode_request(
        first_parent: *const i64,
        first_parent_len: usize,
        ops: *const ReplayOpInput,
        ops_len: usize,
        grants: *const ReplayGrantInput,
        grants_len: usize,
        revocations: *const u64,
        revocations_len: usize,
        out_len: *mut usize,
    ) -> *mut u8;
    fn shim_uweave_replay(input: *const u8, len: usize, out_len: *mut usize) -> *mut u8;
    fn shim_uweave_free(p: *mut u8);
    #[cfg(test)]
    fn shim_uweave_request_canonical(input: *const u8, len: usize) -> u8;
    fn shim_uweave_seq(input: *const u8, len: usize, out_len: *mut usize) -> *mut u8;
    fn shim_uweave_era(input: *const u8, len: usize, out_len: *mut usize) -> *mut u8;
    fn shim_uweave_preo_artifact_v2_validate_one(input: *const u8, len: usize) -> u8;
}

static INIT: Once = Once::new();

/// One typed move record at the Rust/C boundary. This is not FORMAT v3: Lean
/// owns the canonical request encoder and decides its byte layout.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ReplayOpInput {
    pub(crate) lamport: u64,
    pub(crate) replica: u64,
    pub(crate) child: u64,
    pub(crate) dest: i64,
    pub(crate) cite: u64,
}

/// One typed grant record at the Rust/C boundary.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct ReplayGrantInput {
    pub(crate) id: u64,
    pub(crate) parent: u64,
    pub(crate) scope: u64,
}

fn ensure_initialized() {
    INIT.call_once(|| {
        // SAFETY: `Once` serializes the process-global Lean runtime
        // initialization and invokes it exactly once through this safe API.
        // The shim takes no pointers and either completes or aborts.
        unsafe { shim_uweave_init() }
    });
}

/// Copy a shim-owned allocation into Rust and return it to the allocator that
/// created it.
///
/// # Safety
///
/// `ptr` must be the non-null result of one of this module's byte-returning
/// shim calls, valid for reads of `len` bytes and not previously freed.
unsafe fn take_shim_bytes(ptr: *mut u8, len: usize) -> Vec<u8> {
    assert!(
        !ptr.is_null(),
        "Lean shim violated its non-null output contract"
    );
    // SAFETY: the caller establishes the shim allocation contract above; the
    // copy does not outlive the allocation.
    let out = unsafe { std::slice::from_raw_parts(ptr, len) }.to_vec();
    // SAFETY: `ptr` came from the shim's `malloc` and ownership has not been
    // returned before this point. The C contract pairs it with this function.
    unsafe { shim_uweave_free(ptr) };
    out
}

/// Have Lean produce the canonical FORMAT-v3 request from typed values.
/// Rust chooses node indices and which resolvable operations to send, but it
/// does not construct the request header, counts, blocks, or bytes.
pub(crate) fn encode_replay_request(
    first_parent: &[i64],
    ops: &[ReplayOpInput],
    grants: &[ReplayGrantInput],
    revocations: &[u64],
) -> Vec<u8> {
    ensure_initialized();
    let mut out_len = 0usize;
    // SAFETY: every pointer comes from a live slice and is readable for its
    // paired element count; `ReplayOpInput` and `ReplayGrantInput` are
    // `repr(C)` and exactly match shim.c. `out_len` is writable. The shim
    // consumes none of the Rust inputs and returns a non-null malloc-owned
    // buffer valid for the reported byte length.
    let ptr = unsafe {
        shim_uweave_encode_request(
            first_parent.as_ptr(),
            first_parent.len(),
            ops.as_ptr(),
            ops.len(),
            grants.as_ptr(),
            grants.len(),
            revocations.as_ptr(),
            revocations.len(),
            &mut out_len,
        )
    };
    // SAFETY: established by `shim_uweave_encode_request`'s ABI contract.
    unsafe { take_shim_bytes(ptr, out_len) }
}

/// Run the Lean replay kernel on an encoded request (see `Exec.lean` for the
/// word layout). Initializes the Lean runtime on first use.
pub fn replay_kernel(input: &[u8]) -> Vec<u8> {
    ensure_initialized();
    let mut out_len: usize = 0;
    // SAFETY: `input` is readable for `input.len()` bytes and `out_len` is
    // writable. The initialized shim does not retain either pointer and
    // returns a non-null malloc-owned buffer of the reported length.
    let ptr = unsafe { shim_uweave_replay(input.as_ptr(), input.len(), &mut out_len) };
    // SAFETY: established by `shim_uweave_replay`'s ABI contract.
    unsafe { take_shim_bytes(ptr, out_len) }
}

/// Ask the Lean kernel whether bytes are the *canonical* request encoding:
/// decode, re-encode with the proved `Exec.encodeRequest`, and compare. The
/// production replay path no longer needs this differential because Lean now
/// produces its request bytes; this endpoint remains a compatibility audit
/// and a focused test oracle.
#[cfg(test)]
pub fn request_canonical(input: &[u8]) -> bool {
    ensure_initialized();
    // SAFETY: `input` is readable for `input.len()` bytes. The initialized
    // shim consumes no Rust memory and returns a scalar byte.
    unsafe { shim_uweave_request_canonical(input.as_ptr(), input.len()) == 1 }
}

/// Run the Lean sequence kernel on an encoded request (see
/// `Uwueave/SeqKernel.lean` for the SEQ FORMAT v1 word layout). Initializes
/// the Lean runtime on first use.
pub fn seq_kernel(input: &[u8]) -> Vec<u8> {
    ensure_initialized();
    let mut out_len: usize = 0;
    // SAFETY: `input` is readable for `input.len()` bytes and `out_len` is
    // writable. The initialized shim returns a non-null malloc-owned buffer
    // of the reported length and retains neither Rust pointer.
    let ptr = unsafe { shim_uweave_seq(input.as_ptr(), input.len(), &mut out_len) };
    // SAFETY: established by `shim_uweave_seq`'s ABI contract.
    unsafe { take_shim_bytes(ptr, out_len) }
}

/// Run the Lean ERA arbitration kernel on an encoded request (see
/// `Uwueave/EraKernel.lean` for the ERA FORMAT v1 word layout). Initializes
/// the Lean runtime on first use.
pub fn era_kernel(input: &[u8]) -> Vec<u8> {
    ensure_initialized();
    let mut out_len: usize = 0;
    // SAFETY: `input` is readable for `input.len()` bytes and `out_len` is
    // writable. The initialized shim returns a non-null malloc-owned buffer
    // of the reported length and retains neither Rust pointer.
    let ptr = unsafe { shim_uweave_era(input.as_ptr(), input.len(), &mut out_len) };
    // SAFETY: established by `shim_uweave_era`'s ABI contract.
    unsafe { take_shim_bytes(ptr, out_len) }
}

/// Ask the Lean-owned artifact codec whether bytes are exactly one canonical
/// `ArtifactDurable` format-v2 frame. Rust uses this narrow predicate rather
/// than implementing a second `ArtifactEncoding` decoder.
pub(crate) fn preo_artifact_v2_validate_one(input: &[u8]) -> bool {
    ensure_initialized();
    // SAFETY: `input` is readable for `input.len()` bytes. The initialized
    // shim copies it into a Lean ByteArray, retains no pointer, consumes the
    // Lean input, and reduces the exactly-one-byte output to a scalar.
    unsafe { shim_uweave_preo_artifact_v2_validate_one(input.as_ptr(), input.len()) == 1 }
}
