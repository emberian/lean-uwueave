//! The three-function surface to the Lean-compiled kernel. See `shim.c` for
//! the C side; see `Leanuweave/Exec.lean` for the semantics (and for the
//! byte-level contract both sides speak).

use std::sync::Once;

extern "C" {
    fn shim_uweave_init();
    fn shim_uweave_replay(input: *const u8, len: usize, out_len: *mut usize) -> *mut u8;
    fn shim_uweave_free(p: *mut u8);
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
