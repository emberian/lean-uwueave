/-
# Uwueave.Exec — the executable kernel the Rust crate calls into.

THIS IS LEAN-AUTHORED SEMANTICS COMPILED TO C. The Rust crate does not
implement the move-log replay; it marshals bytes to `uwueave_replay_kernel`
(the `@[export]` below), which lake compiles to C alongside every other module
here, and `build.rs` links into the cdylib/rlib. Rust's remaining jobs are the
deliberately dumb ones: storage, hashing, indexes, IO.

## The contract — FORMAT v2 (v1 responses no longer exist; this was a flag day)

Input `ByteArray`, little-endian 64-bit words (unchanged from v1):

```
word 0            : n  — node count
word 1            : m  — op count
words 2 .. 2+n    : firstParent[i] as i64   (-1 = root)
then m × 4 words  : lamport, replica, child (u64 index), dest as i64
                    (-1 = move to root; 0 ≤ d < n = move under node d)
```

Output `ByteArray`, exactly `n + m` words (**v2** — v1 emitted only the first
block; a v1 consumer reading a v2 response must refuse, not truncate):

```
words 0 .. n      : override[i] as i64 — -2 = no override, -1 = overridden
                    to root, d ≥ 0 = overridden under node d
words n .. n+m    : status[j] as i64, one per request op, in REQUEST order —
                    0 = applied, 1 = skipped (cycle rule), 2 = skipped
                    (invalid: child or destination index out of range)
```

Both dimensions `n` and `m` are in the request, so the response parses
unambiguously. The status block is what makes `view_not_stable`'s priced
anomaly *observable*: a UI can now see exactly which ops the replay dropped.

Semantics: ops applied in total `(lamport, replica, child, dest)` order (the
request index breaks ties, which only identical duplicate ops can produce —
the sort is stable); an op whose destination's effective-ancestor chain passes
through its child is **skipped** (the Kleppmann cycle rule — `Uwueave/Move.lean`
§2 is the abstract account of exactly this rule, including its proved price,
`view_not_stable`, and §3 is the machine-checked bridge showing the miniature
table and this kernel's sort-and-fold are the same rule on the 2-node
universe).

⚠ **The grounded-base obligation lives at the caller.** Every acyclicity
theorem about this kernel (`absReplay_acyclic` and kin, `ExecRefine`) assumes
`GroundedBase`: some rank strictly descends along the structural first
parents. A caller that encodes a non-grounded base voids those theorems —
the cycle checks walk chains of the base itself, so a garbage base yields
garbage verdicts, silently. The Rust boundary (`rust/src/movelog.rs`)
asserts groundedness at encode time; any new caller must do the same.

## Claim discipline

This kernel is executable Lean, totalized by fuel, compiled by Lean's verified-
nothing C backend and trusted like any compiler output. What is and is not
proved about it, precisely:

**By construction** (no proof debt): `replay` is *literally*
`encodeView ∘ (overrides ++ statuses) ∘ absReplayFull ∘ (decodeBase, decodeOps)`
— a composition, not a re-implementation — so there is no fold-layer/byte-layer
agreement left to prove. The decision layer is the named function
`absReplayFull`; `absReplay` is *definitionally* its override component
(`absReplay = (absReplayFull …).overrides` holds by `rfl`), so every theorem
stated about `absReplay` is a theorem about the shipping kernel's view block.

**Proved, in `Uwueave/ExecRefine.lean`** (axioms ⊆ `{propext, Classical.choice,
Quot.sound}`; no `sorry`/`native_decide`/`#guard`):

  * `absReplay_acyclic` / `absReplay_terminates` / `absReplay_chain_nodup` —
    **the general acyclicity theorem**: if some rank strictly descends along
    the structural first parents (`GroundedBase`, the shape content-addressing
    provides), then after replaying *any* op array — order, duplication and
    content unconstrained — the effective-parent relation has no cycle: every
    override chain terminates at root without revisiting a node. This is
    `Move.miniInterp_acyclic` generalized from the 2-op miniature to this
    kernel, for all inputs.
  * `chainHits_decides` — fuel adequacy: on the (inductively terminating) view
    the kernel maintains, the literal fuel `n + 1` below *decides* chain
    membership; exhaustion never reads as "misses".
  * `getWord_pushWord`, `getWord_pushWord_lt`, `size_encodeView`,
    `getWord_encodeView`, `toI_ofI`, `decode_encode_id` — output-codec round
    trip at the word level: word `i` of `encodeView ov` decodes back to
    `ov[i]` for i64-range values, and pushed words never disturb earlier ones.
  * `size_statuses_absReplayFull` — the status block is exactly one word per
    request op — and `applyOp_skip_of_opStatus_ne_zero` — a nonzero status is
    a real no-op on the view: the trace partitions the replay into ops that
    acted and ops that did not.
  * **SEC for this kernel** (`kernel_derived_view_sec`, with `absReplay_perm`,
    `absReplay_append_mem`, `absReplay_ext_mem`): the replay is a function of
    the op *set* — blind to delivery order and to redelivery — so
    `Move.derived_view_sec`'s three clauses hold for `absReplay` itself, not
    by informal inheritance from the log argument.
  * **Input codec** (`decodeBase_encodeRequest`, `decodeOps_encodeRequest`,
    `replay_encodeRequest`): `encodeRequest` below is the canonical request
    encoder and the decoders invert it exactly, so for canonical requests
    nothing unproved stands between the entry point's bytes and
    `absReplayFull`'s mathematics.

**Proved, in `Uwueave/Move.lean` §3** (the miniature bridge, Wave 5):
`miniReplay_eq_miniInterp` — a replay defined this kernel's way (sort by the
total order, fold apply-if-no-cycle) equals the four-branch `miniInterp` table
on the 2-op universe; and `absReplay_matches_miniInterp` — *this* `absReplay`,
run on the fixed 2-node encoding of each of the four sub-logs, reads back
(through `effParent`) as exactly `miniInterp`'s answer. Same rule, two
presentations, machine-checked. ⚠ Scope: the 2-node universe only — this is
a bridge for the miniature, **not** a general refinement of `absReplay` to an
abstract derived view.

**Still open**, and not claimed — the list is now exactly the TCB, no undone
proof work hiding in its clothes: (a) the Rust marshaller's byte-for-byte
agreement with `encodeRequest` — differentially checked at runtime against
the proven canonical encoder (`requestCanonicalKernel`, asserted in debug
builds on every request the crate sends, hence on every property-suite
case), which is the strongest closure available: test evidence by nature,
since Rust has no formal semantics to prove against; (b) everything
downstream of the C backend, as above. The former open items — the
Prop-level connection of `absReplay` to the derived-view abstraction, and
the input-side codec — are **closed**: `kernel_derived_view_sec` /
`absReplay_ext_mem` and `replay_encodeRequest` in `ExecRefine`, plus the
2-node symbol bridge in `Move.lean` §3.
-/

namespace Uwueave.Exec

/-- Byte at index, 0 out of range (total; malformed input degrades to junk
output, never to unsoundness or a crash). -/
def byteAt (b : ByteArray) (i : Nat) : UInt8 :=
  if h : i < b.size then b.get i h else 0

/-- Little-endian 64-bit word at word-index `i`. -/
def getWord (b : ByteArray) (i : Nat) : UInt64 :=
  let o := i * 8
  (List.range 8).foldl
    (fun acc k => acc ||| (UInt64.ofNat (byteAt b (o + k)).toNat) <<< (UInt64.ofNat (8 * k)))
    0

/-- Two's-complement read of a word as a mathematical integer. -/
def toI (u : UInt64) : Int :=
  if u.toNat ≥ 2 ^ 63 then (u.toNat : Int) - 2 ^ 64 else (u.toNat : Int)

/-- Two's-complement write (defined for the i64 range we produce). -/
def ofI (i : Int) : UInt64 :=
  UInt64.ofNat (((i + 2 ^ 64) % 2 ^ 64).toNat)

/-- Append a word, little-endian. -/
def pushWord (b : ByteArray) (u : UInt64) : ByteArray :=
  (List.range 8).foldl
    (fun ba k => ba.push (UInt8.ofNat ((u >>> (UInt64.ofNat (8 * k))).toNat % 256)))
    b

/-- One decoded move op. -/
structure Op where
  lamport : UInt64
  replica : UInt64
  child   : Nat
  dest    : Int
  deriving Inhabited

/-- The total replay order: (lamport, replica, child, dest), lexicographic.
Total — no two distinct encoded ops compare equal on all four keys and tie,
so the sort's output is unique and replicas agree regardless of sort
stability. -/
def opLt (a b : Op) : Bool :=
  if a.lamport < b.lamport then true
  else if b.lamport < a.lamport then false
  else if a.replica < b.replica then true
  else if b.replica < a.replica then false
  else if a.child < b.child then true
  else if b.child < a.child then false
  else a.dest < b.dest

/-- Non-strict companion of `opLt` (`a ≤ b` iff `¬ b < a`) — the comparator
the stable sort consumes. Total because `opLt` is a strict total order, and
two ops compare equal under it only when they are the same op. -/
def opLe (a b : Op) : Bool := !opLt b a

/-- Effective parent of `n` under the override array: the override if one was
applied, else the weave's structural first parent. `-1` = root. -/
def effParent (firstParent ov : Array Int) (n : Nat) : Int :=
  let o := ov.getD n (-2)
  if o == -2 then firstParent.getD n (-1) else o

/-- Does the effective-ancestor chain from `start` pass through `needle`?
Fuel-totalized; the view being replayed is acyclic by construction of this
very check, so fuel `n+1` suffices and exhaustion (defensive) answers `false`
— the same answer the visited-set guard gives. -/
def chainHits (firstParent ov : Array Int) (start needle : Nat) : Nat → Bool
  | 0 => false
  | fuel + 1 =>
    if start == needle then true
    else
      let p := effParent firstParent ov start
      if p < 0 then false
      else chainHits firstParent ov p.toNat needle fuel

/-- Apply one op to the override array — or skip it, per the cycle rule. -/
def applyOp (firstParent : Array Int) (n : Nat) (ov : Array Int) (op : Op) : Array Int :=
  if op.child ≥ n then ov
  else if op.dest == -1 then ov.set! op.child (-1)
  else if op.dest < 0 then ov
  else
    let d := op.dest.toNat
    if d ≥ n then ov
    else if chainHits firstParent ov d op.child (n + 1) then ov
    else ov.set! op.child op.dest

/-- The kernel's full answer: the override view plus one status word per
request op, in **request** order. -/
structure ReplayFull where
  overrides : Array Int
  statuses  : Array Int

/-- Status of one op against the view it met, mirroring `applyOp`'s branches
one for one: `0` = applied, `1` = skipped by the cycle rule, `2` = skipped as
invalid (child or destination index out of range). `ExecRefine`'s
`applyOp_skip_of_opStatus_ne_zero` checks the mirror is faithful: a nonzero
status really is a no-op on the view. -/
def opStatus (firstParent : Array Int) (n : Nat) (ov : Array Int) (op : Op) : Int :=
  if op.child ≥ n then 2
  else if op.dest == -1 then 0
  else if op.dest < 0 then 2
  else
    let d := op.dest.toNat
    if d ≥ n then 2
    else if chainHits firstParent ov d op.child (n + 1) then 1
    else 0

/-- One traced fold step: update the view by `applyOp`, and record the op's
status in its request slot. The status is judged against the view the op
actually met (`acc.overrides`, before this op applies). -/
def applyOpFull (firstParent : Array Int) (n : Nat) (acc : ReplayFull) (p : Op × Nat) :
    ReplayFull :=
  ⟨applyOp firstParent n acc.overrides p.1,
   acc.statuses.set! p.2 (opStatus firstParent n acc.overrides p.1)⟩

/-- **The pure decision layer, traced**: pair each op with its request index,
sort by the total replay order (`opLe`, stably — the index tiebreak in
`List.zipIdxLE` can only fire between identical duplicate ops), and fold the
traced step over an initially override-free view and an all-`2` status block.
Every request index occurs exactly once among the pairs, so every status slot
is written exactly once; the `2` initial value is fail-closed, never read
back. Everything the kernel *decides* — ordering, the cycle-skip rule —
happens here, with no bytes in sight. -/
def absReplayFull (firstParent : Array Int) (ops : Array Op) : ReplayFull :=
  let n := firstParent.size
  ((ops.toList.zipIdx).mergeSort (List.zipIdxLE opLe)).foldl
    (applyOpFull firstParent n)
    ⟨Array.replicate n (-2), Array.replicate ops.size 2⟩

/-- The decision layer's view component — **definitionally** the override
block of `absReplayFull` (this is a projection, so `absReplay =
(absReplayFull …).overrides` holds by `rfl` and every theorem about
`absReplay` is a theorem about the shipping kernel). `Uwueave/ExecRefine.lean`
proves this view acyclic (`absReplay_acyclic`) whenever the structural base is
grounded. -/
def absReplay (firstParent : Array Int) (ops : Array Op) : Array Int :=
  (absReplayFull firstParent ops).overrides

/-- Decode words `2 .. 2+n` as the structural first-parent array (`n` = word 0). -/
def decodeBase (input : ByteArray) : Array Int :=
  let n := (getWord input 0).toNat
  (Array.range n).map (fun i => toI (getWord input (2 + i)))

/-- Decode the `m` ops (`m` = word 1) following the parent block. -/
def decodeOps (input : ByteArray) : Array Op :=
  let n := (getWord input 0).toNat
  let m := (getWord input 1).toNat
  (Array.range m).map (fun j =>
    let o := 2 + n + j * 4
    { lamport := getWord input o
      replica := getWord input (o + 1)
      child   := (getWord input (o + 2)).toNat
      dest    := toI (getWord input (o + 3)) })

/-- The canonical request, as words: `n`, `m`, the parent block, then each
op's `(lamport, replica, child, dest)` quad — exactly the layout the contract
header documents and `decodeBase`/`decodeOps` read. -/
def requestWords (firstParent : Array Int) (ops : Array Op) : List UInt64 :=
  UInt64.ofNat firstParent.size :: UInt64.ofNat ops.size ::
    (firstParent.toList.map ofI
      ++ ops.toList.flatMap fun op =>
          [op.lamport, op.replica, UInt64.ofNat op.child, ofI op.dest])

/-- **The canonical request encoder** — the input-side codec mirror.
`ExecRefine` proves `decodeBase`/`decodeOps` invert it exactly
(`decodeBase_encodeRequest`, `decodeOps_encodeRequest`, packaged as
`replay_encodeRequest`), which closes the input side of the wire contract at
the Lean level. What remains outside any proof is only that the Rust
marshaller produces these exact bytes — a finite, testable claim the
property suite exercises end-to-end. -/
def encodeRequest (firstParent : Array Int) (ops : Array Op) : ByteArray :=
  (requestWords firstParent ops).foldl pushWord ByteArray.empty

/-- Encode the override view, one little-endian word per entry. -/
def encodeView (ov : Array Int) : ByteArray :=
  ov.foldl (fun b v => pushWord b (ofI v)) ByteArray.empty

/-- The replay: literally decode → `absReplayFull` → encode, the override
block first and the status block after it (format v2). The byte layer's
agreement with the decision layer is **by construction** — this is a
composition, not a re-implementation, so there is no fold/bytes gap to close
by proof. (The output length is right — `n + m` words — because the fold
preserves both blocks' sizes: `size_absReplay` and
`size_statuses_absReplayFull` in `ExecRefine`.) -/
def replay (input : ByteArray) : ByteArray :=
  let out := absReplayFull (decodeBase input) (decodeOps input)
  encodeView (out.overrides ++ out.statuses)

/-- The C entry point. Owned `ByteArray` in, owned `ByteArray` out. -/
@[export uwueave_replay_kernel]
def replayKernel (input : ByteArray) : ByteArray :=
  replay input

/-- Canonicality self-check for request bytes: decode, re-encode with the
canonical `encodeRequest`, compare byte-for-byte. Returns one byte, `1` iff
the input is canonical. Because `ExecRefine` proves decode ∘ `encodeRequest`
is the identity, a `1` here means the caller's bytes are *exactly* the
canonical encoding of what the kernel will decode from them — the Rust
marshaller runs this (via `shim_uweave_request_canonical`) as a debug-build
assert on every request it sends, so its agreement with `encodeRequest` is
differentially checked against the proven encoder rather than merely
exercised. (Still test evidence, not proof: Rust has no formal semantics to
prove against.) -/
@[export uwueave_request_canonical]
def requestCanonicalKernel (input : ByteArray) : ByteArray :=
  let re := encodeRequest (decodeBase input) (decodeOps input)
  ByteArray.empty.push (if re.data == input.data then 1 else 0)

end Uwueave.Exec
