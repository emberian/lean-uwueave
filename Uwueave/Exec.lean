/-
# Uwueave.Exec — the executable kernel the Rust crate calls into.

THIS IS LEAN-AUTHORED SEMANTICS COMPILED TO C. The Rust crate does not
implement the move-log replay; it marshals bytes to `uwueave_replay_kernel`
(the `@[export]` below), which lake compiles to C alongside every other module
here, and `build.rs` links into the cdylib/rlib. Rust's remaining jobs are the
deliberately dumb ones: storage, hashing, indexes, IO.

## The contract

Input `ByteArray`, little-endian 64-bit words:

```
word 0            : n  — node count
word 1            : m  — op count
words 2 .. 2+n    : firstParent[i] as i64   (-1 = root)
then m × 4 words  : lamport, replica, child (u64 index), dest as i64
                    (-1 = move to root; 0 ≤ d < n = move under node d)
```

Output `ByteArray`: `n` words, `override[i]` as i64 — `-2` = no override,
`-1` = overridden to root, `d ≥ 0` = overridden under node `d`.

Semantics: ops applied in total `(lamport, replica, child, dest)` order; an op
whose destination's effective-ancestor chain passes through its child is
**skipped** (the Kleppmann cycle rule — `Uwueave/Move.lean` §2 is the
abstract account of exactly this rule, including its proved price,
`view_not_stable`).

## Claim discipline

This kernel is executable Lean, totalized by fuel, compiled by Lean's verified-
nothing C backend and trusted like any compiler output. The *refinement
theorem* connecting it to `Move.miniInterp`/`derived_view_sec` (that this
replay is the abstract interpreter's derived view, for all inputs) is named
open work, not a thing this comment gets to claim by adjacency. Until it
lands, the honest statement is: the semantics are *authored* in Lean, in one
place, next to their abstract model — no longer twinned across languages.
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

/-- The replay: decode, sort, fold, encode. -/
def replay (input : ByteArray) : ByteArray :=
  let n := (getWord input 0).toNat
  let m := (getWord input 1).toNat
  let firstParent : Array Int :=
    (Array.range n).map (fun i => toI (getWord input (2 + i)))
  let ops : Array Op :=
    (Array.range m).map (fun j =>
      let o := 2 + n + j * 4
      { lamport := getWord input o
        replica := getWord input (o + 1)
        child   := (getWord input (o + 2)).toNat
        dest    := toI (getWord input (o + 3)) })
  let sorted := ops.qsort opLt
  let ov := sorted.foldl (applyOp firstParent n) (Array.replicate n (-2))
  (Array.range n).foldl (fun b i => pushWord b (ofI (ov.getD i (-2)))) ByteArray.empty

/-- The C entry point. Owned `ByteArray` in, owned `ByteArray` out. -/
@[export uwueave_replay_kernel]
def replayKernel (input : ByteArray) : ByteArray :=
  replay input

end Uwueave.Exec
