# PERFORMANCE

*First measurement pass, 2026-08-11. Before this file, nothing in this crate had
ever been timed.*

Every decision this crate makes crosses an FFI boundary into Lean-compiled C:
move replay (`Uwueave/Exec.lean`), sequence linearization
(`Uwueave/SeqKernel.lean`), ERA arbitration (`Uwueave/EraKernel.lean`). The open
question was whether that architecture costs microseconds or seconds — whether
this is deployable or a lab piece.

**The answer, in one line: the architecture is fine and four of its algorithms
are not.** One crossing into Lean-compiled C costs **1.44 µs**. Everything
slower than that measured here is ordinary algorithmic debt inside functions that
happen to be written in Lean — quadratics we wrote, in code we can change,
without touching the shape of the design.

---

## How to reproduce

```
cd rust && cargo run --release --example bench_kernels
```

and, for the debug-profile numbers in §7:

```
cd rust && BENCH_MAX=1000 cargo run --example bench_kernels
```

`BENCH_MAX=<n>` caps workload size (default `30000`). The harness is
`rust/examples/bench_kernels.rs`: no dependencies, no `Cargo.toml` change, plain
`std::time::Instant`. Every figure below is a wall-clock mean over an iteration
count the harness prints. Nothing here is extrapolated: where a size was too slow
to measure the harness prints `STOPPED` or drops to a single timed iteration and
says so, and this document does the same.

The harness reports an `exp` column: the local scaling exponent
`log(t₂/t₁) / log(n₂/n₁)` between consecutive rows. `1.0` is linear, `2.0` is
quadratic. It is a two-point slope, not a fit; complexity claims below are made
only where the slope holds across three or more consecutive rows **and** a
reading of the Lean source says why.

### The machine and the build

| | |
|---|---|
| machine | Apple M2 Max, 12 cores, 96 GiB, macOS 26.6 (25G72) |
| target | `aarch64-apple-darwin` |
| rustc | 1.98.0-nightly (91fe22da8 2026-06-21) |
| Lean | 4.30.0 (`d024af099ca4`) |
| repo | `31aac2b` |
| Rust profile | `release` (`opt-level=3`) unless a row says `debug` |
| Lean-emitted C | **`-O2` always** — `rust/build.rs` sets `cc.opt_level(2)` unconditionally, for both cargo profiles |

That last row is load-bearing, and it is confirmed by measurement rather than by
reading: the raw kernel call on identical bytes takes **17.31 ms** in a release
build and **17.56 ms** in a debug build (`n = m = 3000` move replay). *The kernel
does not have a debug profile.* Everything a debug build costs extra is Rust glue
plus one additional crossing (§7).

Startup: **21.2 ms** for `lean_initialize_runtime_module` + the module
initializers + the first kernel call, paid once per process.

---

## 1. The FFI boundary is not the problem

The smallest legal move-replay request — one node, no ops, one grant, 72 bytes —
measured through the raw C shim and through the full Rust wrapper:

| path | per call |
|---|---|
| `shim_uweave_replay` (C shim → Lean kernel → C shim) | **1.44 µs** |
| the same through `MoveLog::replay` (encode, cross, decode) | **1.61 µs** |

So the entire price of "the semantics are a theorem, compiled to C, called over
FFI" is **1.4 µs per decision**, and this crate's Rust wrapper adds 0.2 µs to
it. For comparison, linearizing a 1000-element paragraph (§3) costs 17 ms —
**ten thousand times** the crossing it rides on.

Any future performance conversation that starts with "the FFI boundary" is
starting in the wrong place.

---

## 2. Move replay — `MoveLog::replay` → `Exec.gatedReplayFull`

### 2.1 What scales how

`n` = nodes in the weave, `m` = ops in the log, base = the structural parent DAG.

**Log and weave growing together (chain base):**

| n = m | per call | exp |
|---|---|---|
| 10 | 13.7 µs | – |
| 100 | 146 µs | 1.03 |
| 1000 | 3.14 ms | 1.33 |
| 3000 | 18.7 ms | 1.62 |
| 10000 | 161 ms | 1.79 |

**Weave fixed at 1000 nodes, ops growing:**

| m | chain base | flat base |
|---|---|---|
| 0 | 630 µs | 717 µs |
| 10 | 645 µs | 736 µs |
| 100 | 979 µs | 873 µs |
| 1000 | 3.13 ms | 2.20 ms |
| 10000 | 27.6 ms | 19.7 ms |

exponent at the top of both columns: **0.95 / 0.95 — linear in `m`.**

**Ops fixed at 100, weave growing:**

| n | chain base | flat base |
|---|---|---|
| 100 | 147 µs | 144 µs |
| 1000 | 987 µs | 871 µs |
| 3000 | 2.41 ms | 2.47 ms |
| 10000 | 7.28 ms | 8.27 ms |
| 30000 | 22.7 ms | 24.6 ms |

exponent at the top of both columns: **1.03 / 0.99 — linear in `n`.**

Read those three tables together. Cost is **linear in `n` with `m` fixed** and
**linear in `m` with `n` fixed**, but **super-linear when both grow** (exponent
climbing to 1.79). A separable `f(n) + g(m)` with both parts linear cannot do
that. There is an `n·m` coupling term, and the source says what it is:
`Exec.applyOp` and `Exec.opStatus` each call `Exec.chainHits`, which walks the
*effective*-parent chain from the destination looking for a cycle. That walk is
`O(d)` where `d` is the depth of the tree **as the replay has rebuilt it so far**
— which is why the flat base is only ~25% cheaper than the chain base at
`m = 10000`: moves themselves build chains, so a shallow structural base does not
buy a shallow effective base.

**The model, as far as the measurements support it:**

```
replay(n, m, d, ng) ≈ 1.4 µs                     fixed crossing
                    + c_codec · (n + 5m + 3ng)   wire codec, both directions
                    + c_node  · n                per-node array work
                    + c_op    · m · (log m + d)  sort + two chainHits walks
                    + c_op    · m · ng           the grant scan   (§2.3)
```

The `m·d` term is the only one that is super-linear in document *size*, and `d`
is a property of the document's shape, not its size. An outline that stays
shallow stays linear.

### 2.2 Where the time actually goes

`total` = `MoveLog::replay`; `kernel` = the raw shim call on the *same* bytes;
`encode` = the Rust marshaller; `decode` = the remainder (response walk plus
status-to-log stitch). `canonical` = `Exec.requestCanonicalKernel` on the same
bytes, which is decode-everything + re-encode-everything + `memcmp` with **no
decision layer at all** — a direct reading of the wire codec's throughput, and
also exactly what a debug build adds to every request (§7).

| n | m | total | encode | kernel | decode | canonical | codec rate |
|---|---|---|---|---|---|---|---|
| 100 | 0 | 55.3 µs | 3.3 µs (6%) | 51.4 µs (93%) | 0.5 µs (1%) | 29.0 µs | 134 ns/word |
| 100 | 100 | 148 µs | 6.5 µs (4%) | 138 µs (93%) | 3.6 µs (2%) | 109 µs | 89 ns/word |
| 1000 | 0 | 630 µs | 83 µs (13%) | 499 µs (79%) | 49 µs (8%) | 271 µs | 134 ns/word |
| 1000 | 1000 | 3.15 ms | 161 µs (5%) | 2.87 ms (91%) | 128 µs (4%) | 1.05 ms | 87 ns/word |
| 3000 | 3000 | 18.2 ms | 620 µs (3%) | 17.3 ms (95%) | 284 µs (2%) | 3.13 ms | 87 ns/word |
| 10000 | 1000 | 34.6 ms | 1.31 ms (4%) | 32.5 ms (94%) | 787 µs (2%) | 3.44 ms | 114 ns/word |

Two conclusions, both against expectation:

**(a) Re-encoding the whole log on every `replay` is not the bottleneck.** The
brief flagged it as the prime suspect. Measured, the Rust marshaller is
**3–13%** of a release-profile replay. It is *not* free — 1.31 ms to marshal a
10000-node weave — but killing it entirely would buy at most 13%, and only in
the ops-free case.

**(b) The wire codec is.** `Exec.getWord` and `Exec.pushWord` run at
**87–134 ns per 64-bit word**, i.e. **60–92 MB/s**. On the `n = 1000, m = 0`
row, a codec round trip (271 µs) is **more than half** of the entire kernel call
(499 µs). The reason is three lines of `Uwueave/Exec.lean`:

```lean
def getWord (b : ByteArray) (i : Nat) : UInt64 :=
  let o := i * 8
  (List.range 8).foldl
    (fun acc k => acc ||| (UInt64.ofNat (byteAt b (o + k)).toNat) <<< (UInt64.ofNat (8 * k))) 0
```

`List.range 8` allocates a fresh eight-cell cons list **per word**, in both
directions. That is the ~100 ns. It is not a cost of proving anything; it is a
loop written the way a proof is easiest to read. All three kernels share these
two functions.

### 2.3 The grant substrate — and a control that changes the verdict

100-node flat weave, 1000 ops, grant set growing. The two columns differ only in
**which grant the ops cite**. Grants go on the wire in ascending id order, so
citing grant 1 hits `Exec.findGrant`'s `Array.find?` at index 0, and citing grant
`ng` walks the whole array. The wire bytes are identical in both columns.

| ng | ops cite grant 1 (first) | ops cite grant ng (last) | difference |
|---|---|---|---|
| 1 | 1.07 ms | 1.08 ms | – |
| 10 | 1.09 ms | 1.13 ms | 0.04 ms |
| 100 | 1.10 ms | 1.65 ms | 0.55 ms |
| 1000 | 1.28 ms | 7.21 ms | 5.9 ms |
| 10000 | 3.32 ms | **61.8 ms** | 58.5 ms |

The left column is what a naive sweep measures, and it measures the *wire cost*
of the grant block (3× at ten thousand grants), not the lookup — a reading that
would have retired this as harmless. The right column is the lookup:
**18.6× slower for the same request, same size, same answer**, purely because of
where in the array the cited grant sits. The difference grows linearly in `ng`
(0.55 → 5.9 → 58.5), which is the `O(m · ng)` scan at about **1.46 ns per
(op, grant) visit** — `permittedOp` calls `findGrant` twice and is itself called
twice per op, so it is four passes over the grant array per op.

---

## 3. Sequence linearization — `SeqCrdt::visible` / `text` → `SeqKernel.linearizeK`

**This is the wall.**

| n elements | chain doc `visible()` | flat doc `visible()` | half tombstoned | `text()` |
|---|---|---|---|---|
| 10 | 4.5 µs | 5.1 µs | 4.2 µs | 4.9 µs |
| 100 | 194 µs | 144 µs | 192 µs | 198 µs |
| 500 | 4.33 ms | 2.83 ms | 4.31 ms | 4.35 ms |
| 1000 | 17.1 ms | 11.7 ms | 17.0 ms | 17.1 ms |
| 2000 | 68.6 ms | 44.2 ms | 68.5 ms | 69.0 ms |
| 5000 | 512 ms | 305 ms | 497 ms | 505 ms |
| 10000 | **2.09 s** | – | – | – |

Exponent across the last four rows of every column: **1.92 – 2.19. Quadratic, in
every document shape, tombstoned or not.**

Splitting Rust glue from kernel confirms there is nothing to look for on the
Rust side:

| n | `visible()` | raw kernel on the same bytes | glue |
|---|---|---|---|
| 100 | 194 µs | 190 µs | 3.9 µs |
| 1000 | 17.05 ms | 17.00 ms | 54 µs |
| 5000 | 496 ms | 498 ms | ~0 |

The cause is one line of `Uwueave/SeqKernel.lean`:

```lean
def childrenK (anchor : Array Int) (p : Int) : List Nat :=
  ((List.range anchor.size).reverse).filter (fun i => anchorAt anchor i == p)
```

`emitK` calls `childrenK` once per visited element, and each call builds,
reverses and filters a fresh list of **every index in the document**. `n` visits
× `O(n)` scan = `O(n²)`, carrying `2n` list allocations per visit on top.

**Where the wall is, concretely.** At a 16 ms interactive frame budget the limit
is **about 1000 elements in one node's text** — roughly a paragraph, since
sequential typing makes one element per character. Five thousand elements cost
half a second per read, and `Weave::text` / `Weave::view` recompute it from
scratch every time; nothing is cached, by design ("a cache would be a second
shape of the same fact"). At 10000 elements a single `visible()` is
**2.09 seconds**.

Tombstones are free: the half-tombstoned column is within noise of the live one,
because `linearizeK` filters the *output* of a traversal that never reads the
tombstone array. That is the RGA rule working exactly as `Sequence.lean`
describes, and it costs nothing.

---

## 4. ERA resolve — `EraGroup::resolve` → `Era.resolve`

Three independent super-linearities, only one of which shows up in the easy case.

**(4a) Joins and writes, delivered in eid order, no arbiter cuts** — the best
case, and linear:

| ne | per call | exp |
|---|---|---|
| 100 | 61.8 µs | 0.88 |
| 500 | 303 µs | 0.99 |
| 1000 | 607 µs | 1.00 |
| 2000 | 1.22 ms | 1.01 |
| 5000 | 3.04 ms | 1.00 |

Now the three ways out of that best case.

**(4f) The same event set, delivered backwards.** `Era.resolve_same_sets` is the
theorem that delivery order cannot change the answer — and the harness checks
that it doesn't (`forward and reverse delivery resolve identically = true`). The
*cost* notices enormously:

| ne | forward (4a) | reverse (4f) | ratio |
|---|---|---|---|
| 500 | 303 µs | 11.1 ms | 37× |
| 1000 | 607 µs | 44.4 ms | 73× |
| 2000 | 1.22 ms | 179 ms | **147×** |

The ratio itself doubles when `ne` doubles — the signature of quadratic against
linear. `Era.execOrder` is `log.foldr (insertE cuts) []`: an ordered insertion
sort. Ascending arrival order hits its `O(n)` best case; descending arrival
order hits its `O(n²)` worst case. **In a CRDT no replica controls arrival
order**, so the worst case is not adversarial, it is Tuesday.

**(4e) An all-authorised promote/demote stream.** 4a's writes are cheap partly
because `Era.applyEvent` leaves the role map untouched for a write. Promotes and
demotes do not:

```lean
| 2 => { v with role := fun u => if u = e.target then e.role else v.role u }
```

The role map is a **closure chain**, one frame per authorised role change, and
every subsequent `authorised` check evaluates it:

| ne | per call | exp |
|---|---|---|
| 100 | 259 µs | 1.54 |
| 500 | 5.94 ms | 1.95 |
| 1000 | 26.9 ms | 2.18 |
| 2000 | **108 ms** | 2.01 |

**(4b) Arbiter cuts.** `Era.epochOf` scans the whole cut list to find the least
epoch naming an eid, and it runs twice per order comparison. With events and cuts
growing together:

| ne = nc | per call | exp |
|---|---|---|
| 100 | 262 µs | 1.36 |
| 500 | 4.84 ms | 1.81 |
| 1000 | 18.3 ms | 1.92 |
| 2000 | 78.8 ms | 2.11 |

Holding events at 200 and growing cuts alone (4c) gives 124 µs → 864 µs across
`nc` = 1 → 200: linear in `nc` over a large baseline. So the term is `O(ne·nc)`,
and the quadratic above is that product, not a separate effect.

**(4d) Roster width.** 500 events, users growing 2 → 500: 269 µs → 7.66 ms,
exponent 0.95 — linear in the number of distinct users, because the response's
role block evaluates the closure chain once per user. Harmless alone; it
multiplies with 4e.

**Where the wall is.** Best case, ~5000 membership events is 3 ms and nothing
hurts. Realistically — arbitrary delivery order, real promotions, real arbiter
cuts — the wall is **around 1000 membership events**, at which point a resolve is
tens of milliseconds. And every `Weave` mutation triggers one (§6).

---

## 5. Merge — this part is fine

| n | `CausalWeave::merge` | `SeqCrdt::merge` | `Weave::merge` |
|---|---|---|---|
| 10 | 1.37 µs | 0.50 µs | 1.97 µs |
| 100 | 15.0 µs | 6.8 µs | 18.4 µs |
| 1000 | 283 µs | 158 µs | 323 µs |
| 5000 | – | 1.05 ms | 1.79 ms |
| 10000 | 3.34 ms | – | – |
| 50000 | 20.1 ms | – | – |

Exponents run 0.97–1.36 across all three columns with no upward trend:
**linear, at every level, to the largest size measured.** Each figure *includes*
a full clone of the left-hand side, because both `CausalWeave::merge` and
`Weave::merge` validate on a scratch copy so they can refuse wholesale rather
than half-apply. That refusal discipline costs a memcpy-shaped linear pass and is
worth every nanosecond of it.

Merging calls no kernel. No wall was found: 50000 nodes joined in 20 ms.

---

## 6. The composite — what a real operation costs

**`Weave::view()`** — the whole UI read: ERA resolve, move replay, DFS, plus one
sequence-kernel crossing per node that carries text.

Without text (`n/10` move ops in the log):

| n nodes | per view | exp |
|---|---|---|
| 10 | 10.9 µs | – |
| 100 | 93.8 µs | 0.94 |
| 1000 | 1.16 ms | 1.09 |
| 3000 | 4.04 ms | 1.14 |

With text — 32 nodes, each carrying a chain document of `L` elements:

| L per node | per view |
|---|---|
| 1 | 54.5 µs |
| 10 | 180 µs |
| 50 | 1.83 ms |
| 100 | 6.40 ms |
| 200 | **23.6 ms** |

Exponent 1.88 at the top: §3's quadratic, once per node, every view. Thirty-two
nodes of 200 elements each — a 6.4 KB document — already blows the frame budget.

⚠ One thing the table above does **not** measure, derived from
`rust/src/weave.rs:944–966` rather than from the clock: `view()` calls
`replay_traced` **twice** whenever the ERA gate denies even one move op (once to
enumerate the log, once to replay the surviving feed). The benchmark's actor is
an Admin, so nothing is denied and only the single-call path runs. A document
with any denied move pays roughly twice the move-replay component of the numbers
above. The code says so in its own comment; it has not been timed.

**`Weave::add_node`** — one ordinary user-visible write:

| existing n | per call |
|---|---|
| 10 | 1.86 µs |
| 100 | 4.63 µs |
| 1000 | 34.3 µs |
| 5000 | 178 µs |

and the same call with the weave held at 100 nodes while the **membership log**
grows:

| membership events | `add_node` |
|---|---|
| 1 | 4.62 µs |
| 10 | 9.64 µs |
| 100 | 59.0 µs |
| 500 | 280 µs |
| 1000 | **559 µs** |

Compare that last figure to 4a's 1000-event resolve: **607 µs**. They are the
same number. `Weave::add_node` → `check` → `role` → `resolution()` →
`EraGroup::resolve` → **one full ERA kernel round trip per mutating call**, over
the entire membership history, to answer "is this user a Writer". Adding a node
to a document with a thousand membership events costs a hundred times what
adding the node costs.

---

## 7. What debug mode costs

`rust/src/movelog.rs` runs a `debug_assert!` that asks the Lean kernel whether
its request bytes are the canonical encoding — decode, re-encode with the proven
`Exec.encodeRequest`, compare — **on every single replay**. That is the
marshaller's only differential against a proven encoder and it is worth having.
Here is its price.

Measured directly in a *release* build, so this is the pure extra crossing with
no debug-Rust contamination (§2.2's `canonical` column against `total`):

| n | m | release replay | + canonicality check | overhead |
|---|---|---|---|---|
| 100 | 0 | 55.3 µs | 29.0 µs | +52% |
| 100 | 100 | 148 µs | 109 µs | +74% |
| 1000 | 0 | 630 µs | 271 µs | +43% |
| 1000 | 1000 | 3.15 ms | 1.05 ms | +33% |
| 3000 | 3000 | 18.2 ms | 3.13 ms | +17% |
| 10000 | 1000 | 34.6 ms | 3.44 ms | +10% |

And an actual debug build (`BENCH_MAX=1000`), against release on the same rows:

| workload | release | debug | ratio |
|---|---|---|---|
| `MoveLog::replay`, n = m = 100 | 148 µs | 514 µs | 3.5× |
| `MoveLog::replay`, n = m = 1000 | 3.15 ms | 7.54 ms | 2.4× |
| `MoveLog::replay`, smallest request | 1.61 µs | 6.69 µs | 4.2× |
| **raw crossing, smallest request** | 1.44 µs | 1.47 µs | **1.02×** |
| **raw kernel call, n = m = 3000** | 17.31 ms | 17.56 ms | **1.01×** |
| Rust marshaller, n = m = 3000 | 620 µs | 8.00 ms | 12.9× |
| `SeqCrdt::visible()`, n = 1000 | 17.05 ms | 18.67 ms | 1.10× |
| `EraGroup::resolve()`, ne = 1000 | 607 µs | 1.21 ms | 2.0× |
| `Weave::view()`, n = 1000 | 1.16 ms | 6.07 ms | 5.2× |

The debug tax splits cleanly in two, and both halves are visible above:

* **The kernels do not change.** 1.01× on the raw kernel call, 1.02× on the bare
  crossing. `build.rs` compiles the Lean-emitted C at `-O2` in both profiles, so
  any workload dominated by kernel time (sequence linearization, at 1.10×) barely
  notices the profile at all.
* **The Rust glue and the extra crossing do.** The marshaller is 12.9× slower
  unoptimized, and the canonicality round trip adds a second full codec pass
  (1.06 ms of the 7.54 ms debug replay at n = m = 1000, i.e. 14%). Together they
  make a small replay ~4× slower and a `view()` ~5× slower.

**For a future reader: debug mode is roughly 2–5× on anything that marshals, and
free on anything that computes.** The canonicality differential specifically is
+10% to +74% of a release replay, worst on small requests where the fixed codec
work dominates. It is a good trade and should stay on.

---

## 8. Inherent vs our fault

This is the part worth arguing about, so it is stated flatly.

| cost | inherent to proofs-compiled-to-C? | evidence |
|---|---|---|
| 1.44 µs per crossing | **Yes.** Lean object allocation, `memcpy` in and out, runtime dispatch. Irreducible without inlining Lean into Rust, which is the whole architecture. | §1 |
| 21.2 ms process startup | **Yes.** Lean runtime + module initializers, paid once. | header |
| Re-serializing the whole state per call | **Yes, structurally** — the kernels are pure functions of their input, which is what makes `kernel_derived_view_sec` and `resolve_same_sets` statements about the shipping object rather than about a cache. It costs 3–13% on the Rust side. | §2.2 |
| Wire codec at ~100 ns/word | **No — ours.** `List.range 8` allocated per word in `getWord`/`pushWord`. | §2.2 |
| `O(n²)` sequence linearization | **No — ours.** `childrenK` rescans every index per visited node. | §3 |
| `O(ne²)` on adversarial delivery order | **No — ours.** `execOrder` is an insertion sort where a merge sort would do; `Exec.absReplayFull` in the *same repo* already uses `List.mergeSort`. | §4f |
| `O(ne²)` on role changes | **No — ours.** `GroupView.role` is a closure chain instead of a map. | §4e |
| `O(ne·nc)` on arbiter cuts | **No — ours.** `epochOf` linear-scans the cut list per comparison. | §4b |
| `O(m·ng)` grant lookup | **No — ours.** `findGrant` is a linear scan, four passes per op. 18.6× at ng = 10000. | §2.3 |
| One ERA resolve per `Weave` mutation | **No — ours.** `check` → `role` → `resolution()`, uncached, per call. | §6 |
| `view()` replaying the log twice | **No — ours**, and the code comment already admits it. | §6 |
| Linear-time merges | Neither — they are correct and fast. | §5 |

The honest summary: **one architectural cost (1.4 µs, negligible) and nine
implementation costs, six of them asymptotic.** The proofs are not making this
slow. We are.

None of the nine is a cost of *being* verified. Every one lives inside a function
whose *statement* would not change if it were rewritten — `childrenK` would still
be "the children of an anchor in descending index order", `execOrder` would still
be "the arbitration order of a delivery log". What changes is the proof script,
not the theorem.

---

## 9. The fixes, in the order a next pass should do them

Expected effects are derived from the measured breakdown and are labelled as
such: they are predictions, not results.

**F1 — bucket `SeqKernel.childrenK`. Biggest win available anywhere.**
One pass over the anchor array bucketing each index under its anchor, each bucket
reversed once, then `emitK` indexes the bucket array instead of rescanning.
`O(n²) → O(n)`.
*Expected:* 17.1 ms → tens of µs at n = 1000; 2.09 s → single-digit ms at
n = 10000. It also removes the dominant term from `Weave::view` with text (§6).
*Proof obligation:* every downstream theorem in `SeqKernel.lean` reaches
`childrenK` only through `mem_childrenK` and `childrenK_nodup` — checked: those
two lemmas are the only places the definition is unfolded. Proving
`bucketedChildren anchor p = childrenK anchor p` once transports all of them by
rewriting.

**F2 — `Era.execOrder`: insertion sort → merge sort.**
`List.mergeSort` on the existing decidable `elt`, with `insertE`'s duplicate-skip
becoming a dedup pass. `resolve_same_sets` is a statement about the event *set*,
so sort-then-dedup computes the same function.
*Expected:* removes the 147× delivery-order penalty; ERA resolve becomes
`O(ne log ne)` regardless of arrival order — 179 ms → low single-digit ms at
ne = 2000.
*Note:* `Exec.absReplayFull` already does exactly this, so the pattern and its
proof idioms exist in-tree.

**F3 — `Era.GroupView.role`: closure chain → finite map.**
An assoc list keyed by user, or an array indexed by roster position.
*Expected:* removes 4e's quadratic — 108 ms → linear at ne = 2000 — and 4d's
roster-width multiplier with it.

**F4 — `Exec.getWord` / `Exec.pushWord`: drop `List.range 8`.**
Eight explicit shift-and-or steps, no list.
*Expected:* the codec is 87–134 ns/word today; eight unboxed byte loads should
land in the 5–15 ns/word range, so **5–15× on the codec**. Since the codec is
over half of an ops-free move replay and a smaller share as ops grow, expect
roughly **1.5–2×** on `MoveLog::replay` at low `m`, and a proportional win on
every kernel in the repo — all three share these two functions.

**F5 — `Era.epochOf`: decode cuts into an eid-keyed map once.**
*Expected:* removes the `O(ne·nc)` term; with F2, 78.8 ms → low single-digit ms
at ne = nc = 2000.

**F6 — cache the `EraResolution` inside `Weave`.**
`Weave::check` pays a full ERA round trip per mutation (§6). The resolution is a
pure function of the two substrates, so it can be memoized and invalidated on
`record_membership` / `record_cut` / `merge` — one shape of the fact, still
derived, just not re-derived per call.
*Expected:* `add_node` becomes independent of membership-log length — 559 µs →
~5 µs at 1000 events. This is the one fix that argues against a stated design
position (`resolution()`'s doc comment declines to cache); the position is
defensible, the price is now known, and the price is a hundredfold.

**F7 — index `Exec.findGrant`.**
Four linear passes over the grant array per op (§2.3). A single decode-time pass
into an id-keyed structure removes all four.
*Expected:* 61.8 ms → ~3.3 ms at ng = 10000, m = 1000 — i.e. the citing-last case
collapses onto the citing-first case. Promoted above F8 because the 18.6× only
became visible once the control was run; a sweep that cites the first grant hides
it completely.

**F8 — add `MoveLog::ops()` so `Weave::view` replays once, not twice.**
The comment at `rust/src/weave.rs:947` names this trade and chose against it to
avoid holding a second copy of the log. An iterator accessor is not a second copy.
*Expected:* −50% of the move-replay component of `view()` on any document with a
denied op.

Not on the list, deliberately: **the Rust marshaller.** It measured at 3–13% and
there is nothing there worth the risk. "Re-encodes the whole log every call" is
true, is a design choice, and is *not* the bottleneck — the codec it feeds is.

---

## 10. What this pass did not measure

Named so nobody mistakes silence for a green light.

* **Memory.** Not instrumented at all. The quadratics in §3 and §4 are quadratic
  in *allocations* as well as time (`childrenK` allocates `2n` list cells per
  visited node), so peak RSS under a large linearization is unknown.
* **The doubled `view()` replay path** (§6) — derived from the source, not timed.
* **Concurrency.** Everything is single-threaded. The Lean runtime is initialized
  once behind a `std::sync::Once` and nothing here tests two threads calling a
  kernel at the same time.
* **`Weave::merge` under conflict** — only the clean and all-already-present
  paths were timed. The refusal paths validate-then-abort and should be cheaper,
  but that is an inference.
* **Revocations.** `Exec.isRevoked` is another linear scan (`rs.any`), on a path
  every `activeFrom` step takes. The benchmark never revokes anything, so its
  cost is unmeasured and its shape — `O(m · chain · nr)` — is read off the source
  only.
* **Delegation chains.** `activeFrom` recurses to the root of the grant DAG; all
  grants here are root-issued, so chain depth is 1 throughout.
* **Real-world shapes.** The bases here are a pure chain and a pure star. A
  realistic outline sits between them, and §2.1's `m·d` coupling means the answer
  depends on which.
* **`uwueave-check`**, the 83 KB binary in `rust/src/bin/`. Untimed.
* **Anything above 10⁴–10⁵ elements.** The harness stops rather than
  extrapolating; so does this document.
