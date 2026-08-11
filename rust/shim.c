/* The entire C surface between Rust and the Lean-compiled kernel.
 *
 * Everything that must touch lean.h's static-inline helpers lives here, so the
 * Rust side links three plain functions and nothing else. The Lean runtime is
 * initialized once via the root module initializer (which pulls in the whole
 * import closure, Exec included).
 */
#include <lean/lean.h>
#include <stdlib.h>
#include <string.h>

/* Exported by libleanshared but not declared in lean.h. */
extern void lean_initialize_runtime_module(void);

extern lean_object *initialize_uwueave_Uwueave(uint8_t builtin);
extern lean_object *uwueave_replay_kernel(lean_object *bytes);
extern lean_object *uwueave_request_canonical(lean_object *bytes);

static int g_initialized = 0;

void shim_uweave_init(void) {
  if (g_initialized)
    return;
  lean_initialize_runtime_module();
  lean_object *res = initialize_uwueave_Uwueave(1);
  if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
  } else {
    lean_io_result_show_error(res);
    abort();
  }
  lean_io_mark_end_initialization();
  g_initialized = 1;
}

/* Feed `len` bytes to the Lean replay kernel; returns a malloc'd buffer the
 * caller frees with shim_uweave_free, its length in *out_len. */
uint8_t *shim_uweave_replay(const uint8_t *in, size_t len, size_t *out_len) {
  lean_object *arr = lean_alloc_sarray(1, len, len);
  memcpy(lean_sarray_cptr(arr), in, len);
  lean_object *out = uwueave_replay_kernel(arr); /* consumes arr */
  size_t n = lean_sarray_size(out);
  uint8_t *buf = (uint8_t *)malloc(n ? n : 1);
  memcpy(buf, lean_sarray_cptr(out), n);
  lean_dec_ref(out);
  *out_len = n;
  return buf;
}

void shim_uweave_free(uint8_t *p) { free(p); }

/* Ask the Lean kernel whether `len` bytes are the canonical request encoding
 * (decode → re-encode with the proven `encodeRequest` → compare). Returns 1
 * iff canonical. Used by the Rust side as a debug-build self-check of its
 * marshaller against the proven encoder. */
uint8_t shim_uweave_request_canonical(const uint8_t *in, size_t len) {
  lean_object *arr = lean_alloc_sarray(1, len, len);
  memcpy(lean_sarray_cptr(arr), in, len);
  lean_object *out = uwueave_request_canonical(arr); /* consumes arr */
  uint8_t v = lean_sarray_size(out) > 0 ? lean_sarray_cptr(out)[0] : 0;
  lean_dec_ref(out);
  return v;
}
