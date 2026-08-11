//! The small FFI surface to the Lean-compiled kernels. See `shim.c` for the
//! C side; see `Uwueave/Exec.lean` (move replay), `Uwueave/SeqKernel.lean`
//! (sequence linearization) and `Uwueave/EraKernel.lean` (ERA arbitration)
//! for the semantics — and for the byte-level contracts both sides speak.

use std::sync::Once;

extern "C" {
    fn shim_uweave_init();
    fn shim_uweave_replay(input: *const u8, len: usize, out_len: *mut usize) -> *mut u8;
    fn shim_uweave_free(p: *mut u8);
    fn shim_uweave_request_canonical(input: *const u8, len: usize) -> u8;
    fn shim_uweave_seq(input: *const u8, len: usize, out_len: *mut usize) -> *mut u8;
    fn shim_uweave_era(input: *const u8, len: usize, out_len: *mut usize) -> *mut u8;
}

static INIT: Once = Once::new();

/// Run the Lean replay kernel on an encoded request (see `Exec.lean` for the
/// word layout). Initializes the Lean runtime on first use.
pub fn replay_kernel(input: &[u8]) -> Vec<u8> {
    INIT.call_once(|| unsafe { shim_uweave_init() });
    let mut out_len: usize = 0;
    unsafe {
        let ptr = shim_uweave_replay(input.as_ptr(), input.len(), &mut out_len);
        let out = std::slice::from_raw_parts(ptr, out_len).to_vec();
        shim_uweave_free(ptr);
        out
    }
}

/// Ask the Lean kernel whether these bytes are the *canonical* request
/// encoding: decode, re-encode with the proven `Exec.encodeRequest`, compare
/// byte-for-byte. Since `ExecRefine` proves the decoders invert
/// `encodeRequest` exactly, `true` means the bytes are exactly the canonical
/// encoding of what the kernel will decode from them — this is the
/// differential the Rust marshaller checks itself against in debug builds.
pub fn request_canonical(input: &[u8]) -> bool {
    INIT.call_once(|| unsafe { shim_uweave_init() });
    unsafe { shim_uweave_request_canonical(input.as_ptr(), input.len()) == 1 }
}

/// Run the Lean sequence kernel on an encoded request (see
/// `Uwueave/SeqKernel.lean` for the SEQ FORMAT v1 word layout). Initializes
/// the Lean runtime on first use.
pub fn seq_kernel(input: &[u8]) -> Vec<u8> {
    INIT.call_once(|| unsafe { shim_uweave_init() });
    let mut out_len: usize = 0;
    unsafe {
        let ptr = shim_uweave_seq(input.as_ptr(), input.len(), &mut out_len);
        let out = std::slice::from_raw_parts(ptr, out_len).to_vec();
        shim_uweave_free(ptr);
        out
    }
}

/// Run the Lean ERA arbitration kernel on an encoded request (see
/// `Uwueave/EraKernel.lean` for the ERA FORMAT v1 word layout). Initializes
/// the Lean runtime on first use.
pub fn era_kernel(input: &[u8]) -> Vec<u8> {
    INIT.call_once(|| unsafe { shim_uweave_init() });
    let mut out_len: usize = 0;
    unsafe {
        let ptr = shim_uweave_era(input.as_ptr(), input.len(), &mut out_len);
        let out = std::slice::from_raw_parts(ptr, out_len).to_vec();
        shim_uweave_free(ptr);
        out
    }
}
