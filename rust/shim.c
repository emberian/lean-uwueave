/* The entire C surface between Rust and the Lean-compiled kernel.
 *
 * Everything that must touch lean.h's static-inline helpers lives here, so the
 * Rust side links plain C functions and no Lean object layout. The Lean runtime is
 * initialized once via the root module initializer (which pulls in the whole
 * import closure, Exec included).
 */
#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

/* Exported by libleanshared but not declared in lean.h. */
extern void lean_initialize_runtime_module(void);

extern lean_object *initialize_uwueave_Uwueave(uint8_t builtin);
extern lean_object *initialize_uwueave_Uwueave_SeqKernel(uint8_t builtin);
extern lean_object *initialize_uwueave_Uwueave_EraKernel(uint8_t builtin);
extern lean_object *uwueave_encode_request(lean_object *first_parent_words,
                                           lean_object *op_fields,
                                           lean_object *grant_fields,
                                           lean_object *revocation_words);
extern lean_object *uwueave_replay_kernel(lean_object *bytes);
extern lean_object *uwueave_request_canonical(lean_object *bytes);
extern lean_object *uwueave_seq_kernel(lean_object *bytes);
extern lean_object *uwueave_era_resolve(lean_object *bytes);

static int g_initialized = 0;

/* These two records are the typed Rust/C ABI, not the FORMAT-v3 wire
 * encoding. Keep them in lockstep with ffi.rs's repr(C) definitions. */
typedef struct {
  uint64_t lamport;
  uint64_t replica;
  uint64_t child;
  int64_t dest;
  uint64_t cite;
} shim_replay_op;

typedef struct {
  uint64_t id;
  uint64_t parent;
  uint64_t scope;
} shim_replay_grant;

_Static_assert(sizeof(shim_replay_op) == 5 * sizeof(uint64_t),
               "shim_replay_op ABI drift");
_Static_assert(offsetof(shim_replay_op, dest) == 3 * sizeof(uint64_t),
               "shim_replay_op field-order drift");
_Static_assert(sizeof(shim_replay_grant) == 3 * sizeof(uint64_t),
               "shim_replay_grant ABI drift");

/* SAFETY CONTRACT: the caller serializes this process-global initializer and
 * invokes it before every other shim function. Rust enforces that with Once.
 * Initialization failure aborts rather than exposing a half-initialized Lean
 * runtime. */
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
  /* SeqKernel is already in the root module's import closure. Keep its
   * initializer explicit at this FFI boundary: Lean module initialization is
   * idempotently guarded, and the direct call makes this shim robust if the
   * root aggregation is reorganized. */
  res = initialize_uwueave_Uwueave_SeqKernel(1);
  if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
  } else {
    lean_io_result_show_error(res);
    abort();
  }
  /* EraKernel is likewise already in the root closure. Its explicit,
   * idempotently guarded initialization is retained for the same local FFI
   * robustness as SeqKernel above. */
  res = initialize_uwueave_Uwueave_EraKernel(1);
  if (lean_io_result_is_ok(res)) {
    lean_dec_ref(res);
  } else {
    lean_io_result_show_error(res);
    abort();
  }
  lean_io_mark_end_initialization();
  g_initialized = 1;
}

/* Allocate an object array whose elements are boxed UInt64 values. `values`
 * must be readable for `len` elements when len > 0. The returned owned Lean
 * object is consumed by the exported Lean function it is passed to. */
static lean_object *box_u64_array(const uint64_t *values, size_t len) {
  lean_object *arr = lean_alloc_array(len, len);
  for (size_t i = 0; i < len; ++i)
    lean_array_set_core(arr, i, lean_box_uint64(values[i]));
  return arr;
}

/* Convert typed ABI records into the primitive lanes accepted by Lean. The
 * lane shapes (five words per op, three per grant) are adapters only;
 * uwueave_encode_request owns FORMAT-v3 counts, block order and bytes. */
static lean_object *box_parent_words(const int64_t *parents, size_t len) {
  lean_object *arr = lean_alloc_array(len, len);
  for (size_t i = 0; i < len; ++i)
    lean_array_set_core(arr, i, lean_box_uint64((uint64_t)parents[i]));
  return arr;
}

static lean_object *box_op_fields(const shim_replay_op *ops, size_t len) {
  if (len > SIZE_MAX / 5)
    abort();
  lean_object *arr = lean_alloc_array(len * 5, len * 5);
  for (size_t i = 0; i < len; ++i) {
    size_t o = i * 5;
    lean_array_set_core(arr, o, lean_box_uint64(ops[i].lamport));
    lean_array_set_core(arr, o + 1, lean_box_uint64(ops[i].replica));
    lean_array_set_core(arr, o + 2, lean_box_uint64(ops[i].child));
    lean_array_set_core(arr, o + 3, lean_box_uint64((uint64_t)ops[i].dest));
    lean_array_set_core(arr, o + 4, lean_box_uint64(ops[i].cite));
  }
  return arr;
}

static lean_object *box_grant_fields(const shim_replay_grant *grants,
                                     size_t len) {
  if (len > SIZE_MAX / 3)
    abort();
  lean_object *arr = lean_alloc_array(len * 3, len * 3);
  for (size_t i = 0; i < len; ++i) {
    size_t o = i * 3;
    lean_array_set_core(arr, o, lean_box_uint64(grants[i].id));
    lean_array_set_core(arr, o + 1, lean_box_uint64(grants[i].parent));
    lean_array_set_core(arr, o + 2, lean_box_uint64(grants[i].scope));
  }
  return arr;
}

/* Copy an owned Lean ByteArray to a non-null malloc allocation. The caller
 * owns the returned pointer and must pair it with shim_uweave_free. */
static uint8_t *copy_lean_bytes(lean_object *out, size_t *out_len) {
  size_t n = lean_sarray_size(out);
  uint8_t *buf = (uint8_t *)malloc(n ? n : 1);
  if (buf == NULL)
    abort();
  if (n > 0)
    memcpy(buf, lean_sarray_cptr(out), n);
  lean_dec_ref(out);
  *out_len = n;
  return buf;
}

/* Copy borrowed Rust bytes into a fresh owned Lean ByteArray. `in` must be
 * readable for `len` bytes when len > 0. */
static lean_object *copy_rust_bytes(const uint8_t *in, size_t len) {
  lean_object *arr = lean_alloc_sarray(1, len, len);
  if (len > 0)
    memcpy(lean_sarray_cptr(arr), in, len);
  return arr;
}

/* SAFETY CONTRACT: all input pointers are readable for their paired element
 * counts when nonempty; out_len is writable. Records have the layouts asserted
 * above. The function retains no Rust pointer and returns a non-null
 * malloc-owned byte buffer. The Lean runtime has already been initialized. */
uint8_t *shim_uweave_encode_request(
    const int64_t *first_parent, size_t first_parent_len,
    const shim_replay_op *ops, size_t ops_len,
    const shim_replay_grant *grants, size_t grants_len,
    const uint64_t *revocations, size_t revocations_len, size_t *out_len) {
  lean_object *fp = box_parent_words(first_parent, first_parent_len);
  lean_object *op_fields = box_op_fields(ops, ops_len);
  lean_object *grant_fields = box_grant_fields(grants, grants_len);
  lean_object *rev_words = box_u64_array(revocations, revocations_len);
  lean_object *out =
      uwueave_encode_request(fp, op_fields, grant_fields, rev_words);
  return copy_lean_bytes(out, out_len);
}

/* Feed `len` bytes to the Lean replay kernel; returns a malloc'd buffer the
 * caller frees with shim_uweave_free, its length in *out_len.
 * SAFETY CONTRACT: `in` is readable for len bytes when nonempty; out_len is
 * writable; the runtime is initialized. No input pointer is retained. */
uint8_t *shim_uweave_replay(const uint8_t *in, size_t len, size_t *out_len) {
  lean_object *arr = copy_rust_bytes(in, len);
  lean_object *out = uwueave_replay_kernel(arr); /* consumes arr */
  return copy_lean_bytes(out, out_len);
}

/* SAFETY CONTRACT: p is a non-null allocation returned by a byte-producing
 * shim function and has not previously been freed. */
void shim_uweave_free(uint8_t *p) { free(p); }

/* Feed `len` bytes to the Lean sequence kernel (Uwueave/SeqKernel.lean, SEQ
 * FORMAT v1); returns a malloc'd buffer the caller frees with
 * shim_uweave_free, its length in *out_len. Bytes-through, exactly like
 * shim_uweave_replay. Same pointer/runtime contract as replay above. */
uint8_t *shim_uweave_seq(const uint8_t *in, size_t len, size_t *out_len) {
  lean_object *arr = copy_rust_bytes(in, len);
  lean_object *out = uwueave_seq_kernel(arr); /* consumes arr */
  return copy_lean_bytes(out, out_len);
}

/* Feed `len` bytes to the Lean ERA arbitration kernel (Uwueave/EraKernel.lean,
 * ERA FORMAT v1); returns a malloc'd buffer the caller frees with
 * shim_uweave_free, its length in *out_len. Bytes-through, exactly like
 * shim_uweave_replay. Same pointer/runtime contract as replay above. */
uint8_t *shim_uweave_era(const uint8_t *in, size_t len, size_t *out_len) {
  lean_object *arr = copy_rust_bytes(in, len);
  lean_object *out = uwueave_era_resolve(arr); /* consumes arr */
  return copy_lean_bytes(out, out_len);
}

/* Ask the Lean kernel whether `len` bytes are the canonical request encoding
 * (decode → re-encode with the proven `encodeRequest` → compare). Returns 1
 * iff canonical. Used by the Rust side as a debug-build self-check of its
 * former marshaller against the proven encoder. Retained as a compatibility
 * audit endpoint; MoveLog now obtains request bytes from Lean directly.
 * SAFETY CONTRACT: `in` is readable for len bytes when nonempty and no input
 * pointer is retained; the runtime is initialized. */
uint8_t shim_uweave_request_canonical(const uint8_t *in, size_t len) {
  lean_object *arr = copy_rust_bytes(in, len);
  lean_object *out = uwueave_request_canonical(arr); /* consumes arr */
  uint8_t v = lean_sarray_size(out) > 0 ? lean_sarray_cptr(out)[0] : 0;
  lean_dec_ref(out);
  return v;
}
