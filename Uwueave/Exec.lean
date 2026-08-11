/-
# Uwueave.Exec — the executable kernel the Rust crate calls into.

THIS IS LEAN-AUTHORED SEMANTICS COMPILED TO C. The Rust crate does not
implement the move-log replay; it marshals bytes to `uwueave_replay_kernel`
(the `@[export]` below), which lake compiles to C alongside every other module
here, and `build.rs` links into the cdylib/rlib. Rust's remaining jobs are the
deliberately dumb ones: storage, hashing, indexes, IO.

## The contract — FORMAT v3 (v2 requests no longer parse; this was a flag day)

**What v3 added and what it broke.** v2's request was `(base, ops)` and its
response `(overrides, statuses ∈ {0,1,2})`. v3 gives the request an *authority
substrate* — grants and revocations — and the ops a citation, so the gate
`Uwueave/Gated.lean` models at the op layer runs *inside the shipping kernel*:
an op whose cited grant is not active-and-covering never reaches the sort, and
says so in the trace as status `3`. Every v2 request must be re-encoded; every
v2 response reader must learn the fourth code. The break is **loud in both
directions**: the request carries a magic word, and a request without it gets
an EMPTY response (see `replay`), which no length check accepts — ⚠ with one
degenerate exception, stated rather than papered over: a *canonical v3*
request with `n = 0` and `m = 0` also has an `n + m = 0`-word response, so at
that one shape a refusal and an answer are byte-identical. A caller that can
issue empty requests must distinguish them out of band.

Input `ByteArray`, little-endian 64-bit words:

```
word 0            : magic — `magicV3` = 0x5557454156450003 ("UWEAVE" ‖ 3).
                    Anything else ⇒ empty response (refusal, never a guess)
word 1            : n  — node count
word 2            : m  — op count
word 3            : ng — grant count
word 4            : nr — revocation count
words 5 .. 5+n    : firstParent[i] as i64   (-1 = root)
then m × 5 words  : lamport, replica, child (u64 index), dest as i64
                    (-1 = move to root; 0 ≤ d < n = move under node d),
                    cite (u64 grant id the op exercises)
then ng × 3 words : grant id, parent grant id (0 = issued by the root
                    authority), scope
then nr × 1 word  : revoked grant id
```

Output `ByteArray`, exactly `n + m` words:

```
words 0 .. n      : override[i] as i64 — -2 = no override, -1 = overridden
                    to root, d ≥ 0 = overridden under node d
words n .. n+m    : status[j] as i64, one per request op, in REQUEST order —
                    0 = applied, 1 = skipped (cycle rule), 2 = skipped
                    (invalid: child or destination index out of range),
                    3 = skipped (unauthorised: the cited grant is not active,
                    or its scope does not cover the moved node)
```

Both dimensions `n` and `m` are in the request, so the response parses
unambiguously. The status block is what makes `view_not_stable`'s priced
anomaly *observable*: a UI can see exactly which ops the replay dropped — and
now *why*, with `3` naming the moves **authority** removed rather than the
cycle rule.

Semantics, in kernel order:

  1. **Gate** (`permittedOp`, ahead of the sort): op `o` survives iff the
     grant with id `o.cite` is **active** — present, chaining to a
     root-issued grant, with no revoked link on the way (`activeFrom`, the
     executable carrier of `Authority.Active`) — and that grant's scope
     covers the moved node (`o.child < scope`, `Gated.covers`). Refused ops
     are not replayed at all; their status slot is `3`.
  2. **Sort**: the survivors, in total `(lamport, replica, child, dest,
     cite)` order — **five** keys, not four. `cite` became a field of `Op` in
     v3 and is a sort key, not decoration: an order that ignored it would tie
     two *distinct* ops (same move, different grant cited), which is what
     `opLe_antisymm` and therefore SEC ride on (see `opLt`). The request index
     breaks the remaining ties, which only identical duplicate ops can produce
     — the sort is stable.
  3. **Fold**: an op whose destination's effective-ancestor chain passes
     through its child is **skipped** (the Kleppmann cycle rule —
     `Uwueave/Move.lean` §2 is the abstract account of exactly this rule,
     including its proved price, `view_not_stable`, and §3 is the
     machine-checked bridge showing the miniature table and this kernel's
     sort-and-fold are the same rule on the 2-node universe).

The gate is a *filter*, and `gatedReplay_eq_absReplay_admitted` says exactly
that: the gated kernel is the ungated kernel run on the admitted sub-log, so
every theorem about `absReplay` transfers verbatim.

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
`encodeView ∘ (overrides ++ statuses) ∘ gatedReplayFull ∘ (decodeGrants,
decodeRevs, decodeBase, decodeOps)` behind one magic-word guard — a
composition, not a re-implementation — so there is no fold-layer/byte-layer
agreement left to prove. The decision layer is the named function
`gatedReplayFull`; `gatedReplay` is *definitionally* its override component
(`gatedReplay = (gatedReplayFull …).overrides` holds by `rfl`), and the
ungated `absReplay` stands in the same relation to `absReplayFull`, so every
theorem stated about either is a theorem about the shipping kernel's view
block.

**Proved execution refinements, in this file.** Code generation replaces the
proof-facing list codecs with `getWordUnrolled` / `pushWordUnrolled`, and
replaces `gatedReplayFull` with `gatedReplayFullIndex`. The latter builds one
balanced grant-id map per request and reuses it through both gate passes and
every parent-grant walk. `grantLookup_grantIndex` preserves even malformed
duplicate-id first-match behavior; `activeFromIndex_grantIndex` and
`permittedOpIndex_grantIndex` transport that equality through authorization;
`gatedReplayFull_eq_indexed` proves the final overrides and statuses equal.
All three replacements use proved `@[csimp]` equalities, not unproved runtime
overrides.

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
  * **The gate** (§9, format v3): `gatedReplay_eq_absReplay_admitted` — the
    gated kernel *is* `absReplay` on the admitted sub-log, so
    `gatedReplay_acyclic` / `gatedReplay_terminates` are the ungated
    theorems applied, not new arguments; `kernel_gated_antitone` — growing
    the revocation words never enlarges the admitted sub-log (the executable
    twin of `Gated.gated_antitone`), with `gated_unauthorised_is_forever`
    its status-block reading; `gated_status_eq_three_iff` — status `3`
    marks **exactly** the ops the gate removed — with
    `size_statuses_gatedReplayFull` and `gated_status_mem_range` completing
    the trace; and ⚠ `applied_set_not_antitone`, the refutation that keeps
    the antitone claim honest: revoking a grant can *add* an applied op,
    because dropping an op can un-block a cycle-skipped one.
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

**Boundary status** — one former obligation closed, the remaining trust rows
still open and not claimed:
(a) The Rust request marshaller is now **gone**: `encodeRequestKernel` accepts
typed scalar lanes across the FFI and calls the proved canonical
`encodeRequest`, so Rust no longer chooses FORMAT v3's magic, counts, block
order, endianness, or bytes. The typed Rust/C/Lean ABI adapter remains part of
the shim/ABI trust rows; it is not a second wire encoder.
(b) Everything
downstream of the C backend, as above — which is **not one boundary**. This
paragraph used to close "the list is now exactly the TCB, no undone proof
work hiding in its clothes"; that is retracted. `docs/TRUST.md` Ledger 2
decomposes the execution boundary into **ten rows: eight OBLIGATION and two
PAID controls**. The open rows are Lean's C code generator, the C compiler and
linker, the Lean runtime, `shim.c`, the ABI/FFI boundary, Rust `unsafe`, the
storage/index glue, and durability. The paid rows are the Lean-owned canonical
request encoder and Cargo/Lean build freshness. CakeML is the existence proof for the
codegen half; CompCert covers exactly one row, the C compiler, and does not
reach Lean's IR. The former open items — the
Prop-level connection of `absReplay` to the derived-view abstraction, and
the input-side codec — are **closed**: `kernel_derived_view_sec` /
`absReplay_ext_mem` and `replay_encodeRequest` in `ExecRefine`, plus the
2-node symbol bridge in `Move.lean` §3. The gate's own abstract/executable
gap is closed by theorem in `Gated.lean` §5 — and the two halves have
different scopes, which is the half that gets dropped in citation:
`Gated.kernel_admits_only_authorised` is the **hypothesis-free** one (every op
this kernel replays is in the abstract gated feed — the direction that matters
for safety), while `Gated.kernel_gate_agrees_gatedOps` gives the two feeds as
an *iff* only under `Authority.WF ρ` **and** `UniqueGrant`, for ops the request
actually carries. Without those the kernel can only admit FEWER ops than the
abstraction, never more.

⚠ **Total is not resource-safe.** Every decoder sizes its block from a count
word, so a request that carries the magic but a garbage count allocates by
that count. The kernel cannot produce a wrong answer this way (`getWord` is
`0` out of range, so the extra entries decode to junk ops, which the gate
refuses and the cycle rule bounds) but it can be made to allocate. That is a
property of a length-prefixed wire format read by a total decoder, was
equally true of v2, and belongs to whoever admits bytes to the kernel.
-/
import Std.Data.TreeMap

namespace Uwueave.Exec

/-- Byte at index, 0 out of range (total; malformed input degrades to junk
output, never to unsoundness or a crash). -/
def byteAt (b : ByteArray) (i : Nat) : UInt8 :=
  if h : i < b.size then b.get i h else 0

/-- Allocation-free implementation of `getWord`, with its eight byte loads
written out instead of constructing a fresh `List.range 8`. -/
def getWordUnrolled (b : ByteArray) (i : Nat) : UInt64 :=
  let o := i * 8
  let acc := (0 : UInt64) |||
    ((UInt64.ofNat (byteAt b (o + 0)).toNat) <<< (UInt64.ofNat 0))
  let acc := acc |||
    ((UInt64.ofNat (byteAt b (o + 1)).toNat) <<< (UInt64.ofNat 8))
  let acc := acc |||
    ((UInt64.ofNat (byteAt b (o + 2)).toNat) <<< (UInt64.ofNat 16))
  let acc := acc |||
    ((UInt64.ofNat (byteAt b (o + 3)).toNat) <<< (UInt64.ofNat 24))
  let acc := acc |||
    ((UInt64.ofNat (byteAt b (o + 4)).toNat) <<< (UInt64.ofNat 32))
  let acc := acc |||
    ((UInt64.ofNat (byteAt b (o + 5)).toNat) <<< (UInt64.ofNat 40))
  let acc := acc |||
    ((UInt64.ofNat (byteAt b (o + 6)).toNat) <<< (UInt64.ofNat 48))
  acc ||| ((UInt64.ofNat (byteAt b (o + 7)).toNat) <<< (UInt64.ofNat 56))

/-- Little-endian 64-bit word at word-index `i`.

The list fold is the proof-facing specification. The proved compiler
simplification immediately below replaces every executable call with the
allocation-free, eight-load `getWordUnrolled`. -/
def getWord (b : ByteArray) (i : Nat) : UInt64 :=
  let o := i * 8
  (List.range 8).foldl
    (fun acc k => acc ||| (UInt64.ofNat (byteAt b (o + k)).toNat) <<< (UInt64.ofNat (8 * k)))
    0

/-- The compiler-safe replacement proof: executable `getWord` calls use the
unrolled implementation, while theorem unfolding still sees the list spec. -/
@[csimp] theorem getWord_eq_unrolled : getWord = getWordUnrolled := by
  funext b i
  unfold getWord getWordUnrolled
  simp only [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.foldl]

/-- Two's-complement read of a word as a mathematical integer. -/
def toI (u : UInt64) : Int :=
  if u.toNat ≥ 2 ^ 63 then (u.toNat : Int) - 2 ^ 64 else (u.toNat : Int)

/-- Two's-complement write (defined for the i64 range we produce). -/
def ofI (i : Int) : UInt64 :=
  UInt64.ofNat (((i + 2 ^ 64) % 2 ^ 64).toNat)

/-- Allocation-free implementation of `pushWord`, with eight explicit pushes
instead of a temporary eight-cell list. -/
def pushWordUnrolled (b : ByteArray) (u : UInt64) : ByteArray :=
  let b := b.push (UInt8.ofNat ((u >>> (UInt64.ofNat 0)).toNat % 256))
  let b := b.push (UInt8.ofNat ((u >>> (UInt64.ofNat 8)).toNat % 256))
  let b := b.push (UInt8.ofNat ((u >>> (UInt64.ofNat 16)).toNat % 256))
  let b := b.push (UInt8.ofNat ((u >>> (UInt64.ofNat 24)).toNat % 256))
  let b := b.push (UInt8.ofNat ((u >>> (UInt64.ofNat 32)).toNat % 256))
  let b := b.push (UInt8.ofNat ((u >>> (UInt64.ofNat 40)).toNat % 256))
  let b := b.push (UInt8.ofNat ((u >>> (UInt64.ofNat 48)).toNat % 256))
  b.push (UInt8.ofNat ((u >>> (UInt64.ofNat 56)).toNat % 256))

/-- Append a word, little-endian.

The list fold remains as the proof-facing specification; `pushWord_eq_unrolled`
proves the compiler may replace it with the explicit eight-push implementation. -/
def pushWord (b : ByteArray) (u : UInt64) : ByteArray :=
  (List.range 8).foldl
    (fun ba k => ba.push (UInt8.ofNat ((u >>> (UInt64.ofNat (8 * k))).toNat % 256)))
    b

/-- The compiler-safe replacement proof for the allocation-free encoder. -/
@[csimp] theorem pushWord_eq_unrolled : pushWord = pushWordUnrolled := by
  funext b u
  unfold pushWord pushWordUnrolled
  simp only [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.foldl]

/-- One decoded move op. `cite` (format v3) is the id of the grant whose
authority this op exercises — `Gated.GOp.cite`, in the kernel's carrier. The
default `0` is the root *sentinel*, never a grant id on a well-formed
substrate (`Authority.WF` forces `parent < id`, so a present `(0, p, σ)`
would need `p < 0`), which makes an op that forgets its citation refused
rather than privileged: fail-closed by construction of the field's default.
The ungated decision layer (`absReplayFull`, and `Move.lean` §3's miniature)
ignores `cite` entirely; only `permittedOp` reads it. -/
structure Op where
  lamport : UInt64
  replica : UInt64
  child   : Nat
  dest    : Int
  cite    : Nat := 0
  deriving Inhabited

/-- One decoded grant record — `Authority.Grant`'s `(id, parent, scope)`
triple in the kernel's carrier. `parent = 0` means "issued by the root
authority directly"; `scope` is the `Nat` ceiling `Gated.covers` reads (a
grant of scope `σ` may move exactly the nodes with index `< σ`). -/
structure Grant where
  id     : Nat
  parent : Nat
  scope  : Nat
  deriving Inhabited, DecidableEq, Repr

/-- The total replay order: (lamport, replica, child, dest, **cite**),
lexicographic. Total — no two distinct encoded ops compare equal on all five
keys and tie, so the sort's output is unique and replicas agree regardless of
sort stability.

⚠ `cite` is a sort key, not decoration. v3 made it a field of `Op`, and an
order that ignored it would tie two *distinct* ops (same move, different
grant cited) — at which point the sorted presentation of a log is no longer
unique, the stable sort settles the tie by REQUEST index, and two replicas
that received the log in different orders replay it differently.
`opLe_antisymm` is exactly the fact that would fail, and SEC
(`absReplay_perm`, `absReplay_ext_mem`, `kernel_derived_view_sec`) is what
rides on it. -/
def opLt (a b : Op) : Bool :=
  if a.lamport < b.lamport then true
  else if b.lamport < a.lamport then false
  else if a.replica < b.replica then true
  else if b.replica < a.replica then false
  else if a.child < b.child then true
  else if b.child < a.child then false
  else if a.dest < b.dest then true
  else if b.dest < a.dest then false
  else a.cite < b.cite

/-- Non-strict companion of `opLt` (`a ≤ b` iff `¬ b < a`) — the comparator
the stable sort consumes. Total because `opLt` is a strict total order, and
two ops compare equal under it only when they are the same op
(`opLe_antisymm`). -/
def opLe (a b : Op) : Bool := !opLt b a

/-- Effective parent of `n` under the override array: the override if one was
applied, else the weave's structural first parent. `-1` = root. -/
def effParent (firstParent ov : Array Int) (n : Nat) : Int :=
  let o := ov.getD n (-2)
  if o == -2 then firstParent.getD n (-1) else o

/-- Does the effective-ancestor chain from `start` pass through `needle`?
Fuel-totalized; the view being replayed is acyclic by construction of this
very check, so fuel `n+1` suffices and exhaustion (defensive) answers `false`
— the same answer a walk that ran out of graph would give. (⚠ There is no
"visited-set guard" in this kernel, and this docstring used to name one:
`chainHits` is pure fuel, and `chainHits_decides` is what makes exhaustion
unreachable on the view the kernel maintains.) -/
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

/-! ## The gate (format v3): authority, ahead of the sort

`Uwueave/Gated.lean` gates the abstract op feed by `Authority.Active`; these
four definitions are that gate in the shipping kernel's carrier — arrays of
records instead of `GSet`s, `Bool` instead of `Prop`. `Gated.lean` §5 proves
the two agree on encoded states — `kernel_gate_agrees`, an iff under
`Authority.WF ρ` **and** `UniqueGrant`; unconditionally, only the safe-side
half (`kernel_admits_only_authorised`). So this is a port, not a second
design. -/

/-- The grant carrying id `i`, if the substrate holds one. **First match**:
on a substrate violating `Authority.UniqueGrant` two records share an id and
this picks one, where the abstract `Gated.permitted` takes the union over
both — the exact seam `kernel_gate_agrees` carries `UniqueGrant` for, and
which content-addressed grant ids (`id = hash(parent, scope, …)`) discharge
in a deployment. -/
def findGrant (gs : Array Grant) (i : Nat) : Option Grant :=
  gs.find? (fun g => g.id == i)

/-- Balanced grant-id index used by the compiled request-level gate. The
public `findGrant` scan remains the proof-facing first-match specification. -/
abbrev GrantIndex := Std.TreeMap Nat Grant

/-- Build the balanced index tail-first, so an earlier array record overwrites
a later duplicate and `findGrant`'s **first match** behavior is preserved. -/
def grantIndexList : List Grant → GrantIndex
  | [] => ∅
  | g :: gs => (grantIndexList gs).insert g.id g

/-- Build the grant-id index once for a request. -/
def grantIndex (gs : Array Grant) : GrantIndex :=
  grantIndexList gs.toList

/-- Logarithmic grant lookup in a prebuilt request index. -/
def grantLookup (idx : GrantIndex) (i : Nat) : Option Grant :=
  idx[i]?

private theorem grantLookup_grantIndexList (gs : List Grant) (i : Nat) :
    grantLookup (grantIndexList gs) i = gs.find? (fun g => g.id == i) := by
  induction gs with
  | nil => simp [grantLookup, grantIndexList]
  | cons g gs ih =>
      rw [grantLookup, grantIndexList, Std.TreeMap.getElem?_insert]
      by_cases h : g.id = i
      · subst i
        simp
      · have hc : compare g.id i ≠ Ordering.eq := by
          intro heq
          exact h (Nat.compare_eq_eq.mp heq)
        simp only [hc, if_false]
        change grantLookup (grantIndexList gs) i = _
        have hb : (g.id == i) = false := beq_eq_false_iff_ne.mpr h
        rw [List.find?, hb]
        exact ih

/-- The balanced index implements `findGrant` exactly, including first-match
selection on malformed duplicate-id arrays. -/
theorem grantLookup_grantIndex (gs : Array Grant) (i : Nat) :
    grantLookup (grantIndex gs) i = findGrant gs i := by
  rw [grantIndex, grantLookup_grantIndexList]
  exact Array.find?_toList

/-- Is grant id `i` revoked? Revocations are a flat id list — grow-only on
the wire, exactly `Authority.Revoked`. -/
def isRevoked (rs : Array Nat) (i : Nat) : Bool :=
  rs.any (fun x => x == i)

/-- **`Authority.Active`, executable**: grant `i` is active when it is
present, unrevoked, and either root-issued (`parent = 0`) or its parent is
itself active. Total by well-founded recursion on the id — no fuel, because
the recursion only descends when `parent < i`, which is precisely
`Authority.WF`'s creation-order clause; a substrate whose chain fails to
descend is **refused** here rather than walked, which is the fail-closed
reading of an ill-formed grant DAG (and why `activeFrom` needs no
`GroundedBase`-style hypothesis to terminate). -/
def activeFrom (gs : Array Grant) (rs : Array Nat) (i : Nat) : Bool :=
  match findGrant gs i with
  | none => false
  | some g =>
    if isRevoked rs i then false
    else if g.parent == 0 then true
    else if _h : g.parent < i then activeFrom gs rs g.parent
    else false
termination_by i
decreasing_by exact _h

/-- Indexed execution of `activeFrom`. Every recursive parent lookup is
logarithmic in the request's distinct grant count. -/
def activeFromIndex (idx : GrantIndex) (rs : Array Nat) (i : Nat) : Bool :=
  match grantLookup idx i with
  | none => false
  | some g =>
    if isRevoked rs i then false
    else if g.parent == 0 then true
    else if _h : g.parent < i then activeFromIndex idx rs g.parent
    else false
termination_by i
decreasing_by exact _h

/-- Indexed activity is extensionally the original first-match array
semantics for every substrate, including ill-formed duplicate ids. -/
theorem activeFromIndex_grantIndex (gs : Array Grant) (rs : Array Nat)
    (i : Nat) :
    activeFromIndex (grantIndex gs) rs i = activeFrom gs rs i := by
  induction i using Nat.strongRecOn with
  | ind i ih =>
      rw [activeFromIndex, activeFrom, grantLookup_grantIndex]
      cases hf : findGrant gs i with
      | none => rfl
      | some g =>
          by_cases hr : isRevoked rs i = true
          · simp [hr]
          · by_cases hp : g.parent == 0
            · simp [hr, hp]
            · by_cases hlt : g.parent < i
              · simp only [hr, Bool.false_eq_true, ↓reduceIte, hp, hlt]
                exact ih g.parent hlt
              · simp [hr, hp, hlt]

/-- **The gate**: op `o` is permitted when its cited grant is active and that
grant's scope covers the moved node (`o.child < scope` — `Gated.covers`,
which is why `σ = 0` is the fully-attenuated dead token). Only the moved node
is gated; gating the destination too is a policy variant `Gated.lean` names
and does not take. -/
def permittedOp (gs : Array Grant) (rs : Array Nat) (op : Op) : Bool :=
  match findGrant gs op.cite with
  | none => false
  | some g => activeFrom gs rs op.cite && decide (op.child < g.scope)

/-- Indexed execution of `permittedOp`, sharing the same request-level map
with every other authorization decision in the replay. -/
def permittedOpIndex (idx : GrantIndex) (rs : Array Nat) (op : Op) : Bool :=
  match grantLookup idx op.cite with
  | none => false
  | some g =>
    activeFromIndex idx rs op.cite && decide (op.child < g.scope)

/-- Indexed permission is exactly the public gate predicate. -/
theorem permittedOpIndex_grantIndex (gs : Array Grant) (rs : Array Nat)
    (op : Op) :
    permittedOpIndex (grantIndex gs) rs op = permittedOp gs rs op := by
  rw [permittedOpIndex, permittedOp, grantLookup_grantIndex]
  cases findGrant gs op.cite with
  | none => rfl
  | some g => rw [activeFromIndex_grantIndex]

/-- **The feed**: the sub-log the gate admits to the replay — `Gated.gatedOps`
in the kernel's carrier, and the object `kernel_gated_antitone` is about. -/
def admittedOps (gs : Array Grant) (rs : Array Nat) (ops : Array Op) : List Op :=
  ops.toList.filter (permittedOp gs rs)

/-- The status block before the fold runs: `3` (skipped-unauthorised) in the
slot of every op the gate refused — those slots are never written again,
because their ops never reach the fold — and `2` elsewhere, the fail-closed
initial value the fold overwrites for every admitted op. -/
def initStatuses (gs : Array Grant) (rs : Array Nat) (ops : Array Op) : Array Int :=
  ops.map (fun op => if permittedOp gs rs op then 2 else 3)

/-- Status initialization using a prebuilt grant index. -/
def initStatusesIndex (idx : GrantIndex) (rs : Array Nat)
    (ops : Array Op) : Array Int :=
  ops.map (fun op => if permittedOpIndex idx rs op then 2 else 3)

/-- **The gated decision layer**: filter by the gate, *then* sort, then fold —
the same traced fold as `absReplayFull`, over the survivors only, with the
refused ops' request slots pre-set to `3`. Pairing with the request index
survives the filter, so statuses stay attributed to REQUEST slots even though
the fold no longer visits every one. -/
def gatedReplayFull (gs : Array Grant) (rs : Array Nat)
    (firstParent : Array Int) (ops : Array Op) : ReplayFull :=
  let n := firstParent.size
  (((ops.toList.zipIdx).filter (fun p => permittedOp gs rs p.1)).mergeSort
      (List.zipIdxLE opLe)).foldl
    (applyOpFull firstParent n)
    ⟨Array.replicate n (-2), initStatuses gs rs ops⟩

/-- Request-indexed execution of `gatedReplayFull`. The balanced grant map is
built exactly once, then shared by status initialization, admission filtering,
and every recursive parent-grant lookup. -/
def gatedReplayFullIndex (gs : Array Grant) (rs : Array Nat)
    (firstParent : Array Int) (ops : Array Op) : ReplayFull :=
  let n := firstParent.size
  let idx := grantIndex gs
  (((ops.toList.zipIdx).filter
      (fun p => permittedOpIndex idx rs p.1)).mergeSort
      (List.zipIdxLE opLe)).foldl
    (applyOpFull firstParent n)
    ⟨Array.replicate n (-2), initStatusesIndex idx rs ops⟩

/-- Compiler-safe F7 replacement: request-level indexing computes the exact
same overrides and request-order statuses as the scan-based specification. -/
@[csimp] theorem gatedReplayFull_eq_indexed :
    gatedReplayFull = gatedReplayFullIndex := by
  funext gs rs fp ops
  unfold gatedReplayFull gatedReplayFullIndex initStatusesIndex initStatuses
  have hp : permittedOpIndex (grantIndex gs) rs = permittedOp gs rs := by
    funext op
    exact permittedOpIndex_grantIndex gs rs op
  simp only [hp]

/-- The gated view — definitionally the override block of `gatedReplayFull`
(a projection, so `rfl`), exactly as `absReplay` is of `absReplayFull`. -/
def gatedReplay (gs : Array Grant) (rs : Array Nat)
    (firstParent : Array Int) (ops : Array Op) : Array Int :=
  (gatedReplayFull gs rs firstParent ops).overrides

/-! ## The v3 codec -/

/-- The format-v3 magic word: ASCII `UWEAVE` followed by the version, `3`. A
request that does not open with it is refused outright (`replay`), so a v2
encoder cannot be silently reinterpreted under the v3 layout. -/
def magicV3 : UInt64 := 0x5557454156450003

/-- Decode words `5 .. 5+n` as the structural first-parent array (`n` = word 1). -/
def decodeBase (input : ByteArray) : Array Int :=
  let n := (getWord input 1).toNat
  (Array.range n).map (fun i => toI (getWord input (5 + i)))

/-- Decode the `m` ops (`m` = word 2) following the parent block, five words
each — the fifth is the grant citation. -/
def decodeOps (input : ByteArray) : Array Op :=
  let n := (getWord input 1).toNat
  let m := (getWord input 2).toNat
  (Array.range m).map (fun j =>
    let o := 5 + n + j * 5
    { lamport := getWord input o
      replica := getWord input (o + 1)
      child   := (getWord input (o + 2)).toNat
      dest    := toI (getWord input (o + 3))
      cite    := (getWord input (o + 4)).toNat })

/-- Decode the `ng` grants (`ng` = word 3) following the op block, three
words each: `(id, parent, scope)`. -/
def decodeGrants (input : ByteArray) : Array Grant :=
  let n := (getWord input 1).toNat
  let m := (getWord input 2).toNat
  let ng := (getWord input 3).toNat
  (Array.range ng).map (fun k =>
    let o := 5 + n + m * 5 + k * 3
    { id     := (getWord input o).toNat
      parent := (getWord input (o + 1)).toNat
      scope  := (getWord input (o + 2)).toNat })

/-- Decode the `nr` revocations (`nr` = word 4) following the grant block,
one word each: a revoked grant id. -/
def decodeRevs (input : ByteArray) : Array Nat :=
  let n := (getWord input 1).toNat
  let m := (getWord input 2).toNat
  let ng := (getWord input 3).toNat
  let nr := (getWord input 4).toNat
  (Array.range nr).map (fun t =>
    (getWord input (5 + n + m * 5 + ng * 3 + t)).toNat)

/-- The base block of the canonical request: one word per structural parent. -/
def baseWords (firstParent : Array Int) : List UInt64 :=
  firstParent.toList.map ofI

/-- The op block of the canonical request: each op's
`(lamport, replica, child, dest, cite)` quintuple. -/
def opWords (ops : Array Op) : List UInt64 :=
  ops.toList.flatMap fun op =>
    [op.lamport, op.replica, UInt64.ofNat op.child, ofI op.dest,
     UInt64.ofNat op.cite]

/-- The grant block of the canonical request: each grant's
`(id, parent, scope)` triple. -/
def grantWords (gs : Array Grant) : List UInt64 :=
  gs.toList.flatMap fun g =>
    [UInt64.ofNat g.id, UInt64.ofNat g.parent, UInt64.ofNat g.scope]

/-- The revocation block of the canonical request: one word per revoked id. -/
def revWords (rs : Array Nat) : List UInt64 :=
  rs.toList.map UInt64.ofNat

/-- The canonical request, as words: the magic, the four counts, then the
base, op, grant and revocation blocks — exactly the layout the contract
header documents and the four decoders read. -/
def requestWords (firstParent : Array Int) (ops : Array Op)
    (gs : Array Grant) (rs : Array Nat) : List UInt64 :=
  magicV3 :: UInt64.ofNat firstParent.size :: UInt64.ofNat ops.size ::
    UInt64.ofNat gs.size :: UInt64.ofNat rs.size ::
    (baseWords firstParent ++ opWords ops ++ grantWords gs ++ revWords rs)

/-- **The canonical request encoder** — the input-side codec mirror.
`ExecRefine` proves `decodeBase`/`decodeOps` invert it exactly
(`decodeBase_encodeRequest`, `decodeOps_encodeRequest`, packaged as
`replay_encodeRequest`), which closes the input side of the wire contract at
the Lean level. Rust no longer produces a second spelling of these bytes: the
typed FFI adapter below reconstructs the four input lanes and calls this
encoder. The adapter, generated C, runtime and ABI remain separately accounted
execution obligations. -/
def encodeRequest (firstParent : Array Int) (ops : Array Op)
    (gs : Array Grant) (rs : Array Nat) : ByteArray :=
  (requestWords firstParent ops gs rs).foldl pushWord ByteArray.empty

/-! ### Typed FFI entrance to the canonical encoder

The Rust boundary passes values, not a second spelling of FORMAT v3.  The C
shim boxes four lanes of host-ABI `uint64_t`s; this adapter reconstructs the
typed inputs and delegates all request layout and byte-order decisions to
`encodeRequest` above.  The op and grant lanes are exact-width records
(quintuples and triples).  A trailing partial record is ignored here so the
export remains total; the safe Rust wrapper makes such a lane unconstructible.
-/

/-- Reconstruct typed move operations from the FFI's five-word records. -/
def opsOfTypedWords (words : Array UInt64) : Array Op :=
  (Array.range (words.size / 5)).map fun j =>
    let o := j * 5
    { lamport := words.getD o 0
      replica := words.getD (o + 1) 0
      child   := (words.getD (o + 2) 0).toNat
      dest    := toI (words.getD (o + 3) 0)
      cite    := (words.getD (o + 4) 0).toNat }

/-- Reconstruct typed grants from the FFI's three-word records. -/
def grantsOfTypedWords (words : Array UInt64) : Array Grant :=
  (Array.range (words.size / 3)).map fun j =>
    let o := j * 3
    { id     := (words.getD o 0).toNat
      parent := (words.getD (o + 1) 0).toNat
      scope  := (words.getD (o + 2) 0).toNat }

/-- The C entry point for request construction.  Unlike
`requestCanonicalKernel`, this does not check bytes produced elsewhere:
FORMAT v3's canonical bytes are produced here, by `encodeRequest` itself.

All four arguments are owned Lean arrays.  Signed base and destination words
use their two's-complement `UInt64` bit pattern and are interpreted by `toI`.
The C shim guarantees exact-width op/grant lanes. -/
@[export uwueave_encode_request]
def encodeRequestKernel (firstParentWords opFields grantFields revocationWords : Array UInt64) :
    ByteArray :=
  encodeRequest (firstParentWords.map toI) (opsOfTypedWords opFields)
    (grantsOfTypedWords grantFields) (revocationWords.map UInt64.toNat)

/-- The exported typed adapter is definitionally the proved canonical
encoder applied to the values reconstructed at the FFI boundary. -/
theorem encodeRequestKernel_eq (firstParentWords opFields grantFields revocationWords) :
    encodeRequestKernel firstParentWords opFields grantFields revocationWords =
      encodeRequest (firstParentWords.map toI) (opsOfTypedWords opFields)
        (grantsOfTypedWords grantFields) (revocationWords.map UInt64.toNat) := rfl

/-- Encode the override view, one little-endian word per entry. -/
def encodeView (ov : Array Int) : ByteArray :=
  ov.foldl (fun b v => pushWord b (ofI v)) ByteArray.empty

/-- The replay: literally decode → `gatedReplayFull` → encode, the override
block first and the status block after it (format v3). The byte layer's
agreement with the decision layer is **by construction** — this is a
composition, not a re-implementation, so there is no fold/bytes gap to close
by proof. (The output length is right — `n + m` words — because the fold
preserves both blocks' sizes: `size_gatedReplay` and
`size_statuses_gatedReplayFull` in `ExecRefine`.)

The magic guard is the flag day made mechanical: bytes that are not a v3
request get an **empty** response. A v2 caller therefore fails its own length
check instead of reading override words out of a status block, and no reader
can mistake a refusal for an answer at any nonempty shape. ⚠ At `n = 0, m = 0`
it can: such a request passes the magic guard and this function returns
`ByteArray.empty`, byte-identical to the refusal — `rust/src/movelog.rs`
accepts it. That is the one shape where the flag day is silent, and it is a
property of a length-prefixed format whose valid response length can be zero. -/
def replay (input : ByteArray) : ByteArray :=
  if getWord input 0 == magicV3 then
    let out := gatedReplayFull (decodeGrants input) (decodeRevs input)
      (decodeBase input) (decodeOps input)
    encodeView (out.overrides ++ out.statuses)
  else
    ByteArray.empty

/-- The C entry point. Owned `ByteArray` in, owned `ByteArray` out. -/
@[export uwueave_replay_kernel]
def replayKernel (input : ByteArray) : ByteArray :=
  replay input

/-- Canonicality self-check for request bytes: decode, re-encode with the
canonical `encodeRequest`, compare byte-for-byte. Returns one byte, `1` iff
the input is canonical. Because `ExecRefine` proves decode ∘ `encodeRequest`
is the identity, a `1` here means the caller's bytes are *exactly* the
canonical encoding of what the kernel will decode from them. The production
Rust path now calls `encodeRequestKernel` instead; this export remains a
compatibility audit endpoint and test oracle for older callers. -/
@[export uwueave_request_canonical]
def requestCanonicalKernel (input : ByteArray) : ByteArray :=
  if getWord input 0 == magicV3 then
    let re := encodeRequest (decodeBase input) (decodeOps input)
      (decodeGrants input) (decodeRevs input)
    ByteArray.empty.push (if re.data == input.data then 1 else 0)
  else
    -- Not a v3 request: refuse before decoding, so a v2 caller's parent word
    -- is never read as a count.
    ByteArray.empty.push 0

end Uwueave.Exec
