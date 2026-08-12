# PERFORMANCE

*First measurement pass, 2026-08-11. Before this file, nothing in this crate had
ever been timed.*

> **Historical-baseline note.** Sections 1–7 preserve the measurements from
> repo `31aac2b`, before the F1–F8 optimization pass. All eight fixes described
> in §9 are now implemented. Section 10 records a post-fix
> `BENCH_MAX=1000` rerun made on 2026-08-11; it is deliberately separate from
> the baseline and does not replace the original full-range sweep. Section 12
> separately records Wave 23 proof-elaboration and build-closure engineering,
> and §§13–17 do the same for Waves 24–28; those figures are not kernel-runtime
> benchmarks. Current
> complexity statements come from proved equivalence where applicable, source
> inspection, successful builds, and generated-C inspection; only the rows in
> §10 are new runtime-kernel timings.

Every decision this crate makes crosses an FFI boundary into Lean-compiled C:
move replay (`Uwueave/Exec.lean`), sequence linearization
(`Uwueave/SeqKernel.lean`), ERA arbitration (`Uwueave/EraKernel.lean`). The open
question was whether that architecture costs microseconds or seconds — whether
this is deployable or a lab piece.

**The baseline answer, in one line: the architecture was fine and four of its
algorithms were not.** One crossing into Lean-compiled C measured **1.44 µs**.
Everything slower in that pass was ordinary algorithmic debt inside functions
that happened to be written in Lean — quadratics that could be changed without
touching the shape of the design.

---

## How the baseline was measured, and how to rerun it

To reproduce the historical numbers exactly, check out repo `31aac2b` first.
The bounded post-fix rerun recorded in §10 used:

```
cd rust && BENCH_MAX=1000 cargo run --release --example bench_kernels
```

The original full-range baseline command was:

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

## 8. Inherent vs our fault — baseline diagnosis and current status

This is the part worth arguing about, so it is stated flatly.

| baseline cost | inherent to proofs-compiled-to-C? | baseline evidence | current source-level status |
|---|---|---|---|
| 1.44 µs per crossing | **Yes.** Lean object allocation, `memcpy` in and out, runtime dispatch. Irreducible without inlining Lean into Rust, which is the whole architecture. | §1 | The bounded rerun measured 1.94 µs; no full-range rerun or attribution of that difference. |
| 21.2 ms process startup | **Yes.** Lean runtime + module initializers, paid once. | header | The bounded rerun measured 43.92 ms; startup is noisy and the difference is not attributed. |
| Re-serializing the whole state per call | **Yes, structurally** — the kernels are pure functions of their input, which is what makes `kernel_derived_view_sec` and `resolve_same_sets` statements about the shipping object rather than about a cache. It cost 3–13% on the Rust side in the baseline. | §2.2 | The wire contract remains pure; F6 caches only the derived ERA result at the `Weave` layer. |
| Wire codec at ~100 ns/word | **No — ours.** `List.range 8` allocated per word in `getWord`/`pushWord`. | §2.2 | **F4 implemented:** eight operations are unrolled; the old timing is historical. |
| `O(n²)` sequence linearization | **No — ours.** `childrenK` rescanned every index per visited node. | §3 | **F1 implemented:** one-pass buckets plus difference-list emission give structural `O(n)`. |
| `O(ne²)` on adversarial delivery order | **No — ours.** `execOrder` was insertion sort. | §4f | **F2 implemented:** proved sort/dedup equivalence and compiled merge sort. |
| `O(ne²)` on role changes | **No — ours.** `GroupView.role` was an update-closure chain. | §4e | **F3 implemented:** one indexed execution/status trace; `usersOf` remains `O(N·r)` and worst-case `O(N²)`. |
| `O(ne·nc)` on arbiter cuts | **No — ours.** `epochOf` linear-scanned the cut list per comparison. | §4b | **F5 implemented:** cuts are preprocessed into a balanced `TreeMap`; comparator lookups are logarithmic. |
| `O(m·ng)` grant lookup | **No — ours.** `findGrant` was a linear scan, four passes per op. | §2.3 | **F7 implemented:** grant lookup uses a `TreeMap`. Revocation checks remain linear; authorisation is still evaluated twice; `activeFrom` remains tail-recursive. |
| One ERA resolve per `Weave` mutation | **No — ours.** `check` → `role` → `resolution()`, uncached, per call. | §6 | **F6 implemented:** a derived `OnceLock` cache is invalidated on membership/cut changes and merge. |
| `view()` replaying the log twice | **No — ours.** | §6 | **F8 implemented:** `view()` consumes one replay. |
| Linear-time merges | Neither — they were correct and fast. | §5 | Unchanged. |

The baseline diagnosis still stands: the proof/FFI architecture was not the
source of the large costs. F1–F8 changed implementations while retaining the
semantic interfaces. That is now established structurally; the magnitude of
the full-range wall-clock improvement is not yet established. The bounded
measurements are in §10.

---

## 9. F1–F8 implementation record

All eight planned fixes are implemented. This section records what changed and
what is established without turning the baseline's predictions into fictional
results. Section 10 supplies a bounded post-fix snapshot; it is not a full
benchmark pass.

**F1 — `SeqKernel.childrenK`: implemented.**
Children are bucketed in one pass and emitted with difference-list accumulation,
eliminating both the per-node full rescan and append-shaped rebuilding. The
structural traversal cost is now `O(n)`, with the executable substitution tied
back to the original ordering semantics.

**F2 — `Era.execOrder`: implemented.**
The proof-facing insertion-sort specification remains, while compiled callers
use `List.mergeSort` followed by consecutive deduplication. Strict sortedness and
membership prove the two orders equal. With comparator cost separated out, sort
and dedup are `O(N log N)` and `O(N)` respectively.

**F3 — `Era.GroupView.role`: implemented, with one explicit residual.**
Execution uses a balanced role `TreeMap`; the ERA kernel walks the order once to
produce both the final indexed view and the status trace. The compiled response
is proved word-for-word equal to the public closure-based specification. For `n`
executed events, `u` indexed role keys, and `r` roster users, this portion is
`O((n+r) log(u+1) + n+r)` instead of worst-case `Θ(n²+n·r)`. However,
`usersOf` still uses sorted insertion: `O(N·r)`, worst-case `O(N²)`. F3 does
not remove that separate roster-construction residual.

**F4 — `Exec.getWord` / `Exec.pushWord`: implemented.**
The eight byte loads/stores are explicit and unrolled; the per-word
`List.range 8` allocation is gone. Existing codec proofs remain the semantic
check, and generated code was inspected. The baseline's 87–134 ns/word is not a
post-fix measurement.

**F5 — `Era.epochOf`: implemented.**
Cuts are preprocessed once into an eid-keyed balanced `TreeMap`, combining
duplicates with `Nat.min`; lookup is proved equal to the old least-epoch scan.
Together F2 and F5 give ordering time
`O(c log(c+1) + N log N log(c+2) + N)` and `O(c+N)` auxiliary space, rather than
scanning all `c` cuts inside every sort comparison. The `c+2` spelling includes
the comparator's constant cost when there are no cuts.

**F6 — derived `EraResolution` cache: implemented.**
`Weave` holds the derived result in a `OnceLock` and invalidates it when
membership events or cuts change and when merge changes the relevant substrate.
The cache is still derived state; it does not replace the replicated facts or
the Lean decision function.

**F7 — `Exec.findGrant`: implemented, with remaining execution costs.**
Grants are indexed once in a `TreeMap`, replacing repeated linear grant lookup
with logarithmic lookup. Revocation checks are still linear, authorisation is
still evaluated twice (status and application), and `activeFrom` remains
tail-recursive through the delegation chain. Those residuals must not be
silently attributed to the now-indexed grant lookup.

**F8 — one move replay in `Weave::view`: implemented.**
The view path now consumes one replay rather than asking the move kernel for the
same decision twice. This removes the duplicate computation without retaining a
second copy of the operation log.

Not on the list, deliberately: **the Rust marshaller.** It measured at 3–13% in
the baseline. "Re-encodes the whole log every call" is true and remains a design
choice, but the measurements did not identify it as the bottleneck. That
priority judgment should be revisited only after a broader post-fix sweep with
the codec breakdown measured again.

---

## 10. Bounded post-fix rerun — 2026-08-11

One release invocation was run on aarch64/macOS with `BENCH_MAX=1000`. These are
the means printed by that invocation, not extrapolations. The run is bounded at
1000 for the main size sweeps and does not re-establish the baseline's machine
fingerprint or its results above that bound, so no cross-run speedup ratios are
claimed here.

### Sequence visibility

| n | chain | flat |
|---|---|---|
| 10 | 3.44 µs | 10.34 µs |
| 100 | 35.63 µs | 76.45 µs |
| 500 | 155.46 µs | 353.64 µs |
| 1000 | 323.36 µs | 588.01 µs |

Both shapes scale approximately linearly across this bounded sweep, consistent
with F1's source-level `O(n)` buckets/difference-list traversal. This is a
bounded observation, not a claim about sizes above 1000.

### ERA resolution

| ne | joins/writes, ordered (4a) | cuts grow with events (4b) | role-change stream (4e) | reverse delivery (4f) |
|---|---|---|---|---|
| 10 | 10.98 µs | 15.65 µs | 9.19 µs | 8.40 µs |
| 100 | 139.06 µs | 188.02 µs | 91.80 µs | 85.19 µs |
| 500 | 532.47 µs | 1.38 ms | 514.07 µs | 603.66 µs |
| 1000 | 909.47 µs | 2.47 ms | 1.04 ms | 879.31 µs |

Within this run, reverse delivery stays in the same band as ordered delivery,
and the role-change stream is approximately linear through 1000. Growing cuts
remain visibly more expensive, as expected from building and consulting the
epoch `TreeMap`; the old full-cut scan is absent structurally, but this bounded
table is not a complexity proof.

### Grant position after F7

`m = 1000` in every row:

| ng | cites first grant | cites last grant |
|---|---|---|
| 1 | 1.93 ms | 1.51 ms |
| 10 | 2.22 ms | 1.39 ms |
| 100 | 2.10 ms | 1.40 ms |
| 1000 | 2.38 ms | 2.81 ms |
| 10000 | 10.38 ms | 8.29 ms |

The former first-versus-last position gap has collapsed: neither position is a
consistently slower lookup path. Total time still rises at large `ng`, because
each replay must decode and construct the grant index; F7 removes position-
sensitive linear lookup, not input/index construction. Linear revocation scans,
double authorisation, and delegation traversal also remain as listed in §9.

### Other bounded points

| workload | post-fix result |
|---|---|
| process startup | 43.92 ms |
| fixed smallest crossing | 1.94 µs |
| move replay, `n = m = 1000` | 4.49 ms |
| `Weave::view()`, `n = 10` | 28.37 µs |
| `Weave::view()`, `n = 100` | 272.15 µs |
| `Weave::view()`, `n = 1000` | 2.69 ms |

The view points are approximately linear over this range. They do not isolate
F8's denied-operation path, so they are evidence about the whole bounded view
workload, not a measurement of the one-replay change by itself.

### F6 cache caveat: 5e is a cold-clone benchmark

The post-fix 5e `add_node` row still rises from **15.85 µs at one membership
event** to **1.23 ms at 1000 membership events**. That does **not** measure F6's
intended warm-cache reuse. The harness clones `Weave` for each timed iteration,
and `Weave`'s custom `Clone` intentionally starts the derived `OnceLock` empty.
Every iteration therefore pays a cold ERA resolution before the mutation.

A needed **warm-cache mutation benchmark** should construct one `Weave`, load a
fixed membership/cut history, call `resolution()` once to populate the cache,
then time a batch of `add_node` operations on that same value without changing
membership or cuts, excluding the initial fill. A companion case should mutate
membership or cuts and measure the intentional invalidation/refill separately.

---

## 11. What the baseline and bounded optimization pass did not measure

Named so nobody mistakes silence for a green light.

* **A full-range post-fix sweep.** The new run stops at `BENCH_MAX=1000`; the
  baseline's larger sizes have not been rerun on the optimized tree.
* **Memory.** Not instrumented in either pass. The baseline quadratics in §3 and
  §4 were allocation-heavy; current bucket, merge-sort, and `TreeMap` peak RSS
  is also unknown.
* **F8's one-replay effect.** The doubled baseline path was derived from source,
  not isolated as its own timing, and the fixed path has not been timed either.
* **F6 warm-cache reuse.** Existing 5e clones start cold. The warm-cache mutation
  benchmark specified in §10 has not yet been run.
* **Concurrency.** Everything is single-threaded. The Lean runtime is initialized
  once behind a `std::sync::Once` and nothing here tests two threads calling a
  kernel at the same time.
* **`Weave::merge` under conflict** — only the clean and all-already-present
  paths were timed. The refusal paths validate-then-abort and should be cheaper,
  but that is an inference.
* **Revocations.** F7 indexes grants, not revocations. `Exec.isRevoked` remains a
  linear scan (`rs.any`) on every `activeFrom` step. The benchmark never revokes
  anything, so its cost is unmeasured and its shape — `O(m · chain · nr)` — is
  read off the source only. Authorisation also still runs once for status and
  once for application, and delegation traversal remains tail-recursive.
* **Delegation chains.** `activeFrom` recurses to the root of the grant DAG; all
  grants here are root-issued, so chain depth is 1 throughout.
* **Real-world shapes.** The bases here are a pure chain and a pure star. A
  realistic outline sits between them, and §2.1's `m·d` coupling means the answer
  depends on which.
* **`uwueave-check`**, the 83 KB binary in `rust/src/bin/`. Untimed.
* **Anything above 10⁴–10⁵ elements.** The harness stops rather than
  extrapolating; so does this document.

---

## 12. Wave 23 proof and build engineering — 2026-08-11

This section measures the cost of checking and shipping the implementation,
not the runtime of a decision kernel. It records several different protocols
because the wave began as an engineering investigation, not a pre-registered
benchmark. The `Demo` row is the only controlled three-run median. Single-shot
and declaration-level rows are still useful directional evidence, but they are
labelled so they cannot be mistaken for statistically sampled wall-clock
results.

### Before/after engineering deltas

| lane | primary before → after | source/artifact evidence | measurement scope |
|---|---|---|---|
| `ExecRefine` proof normalization and shared codecs | wall **6.97 s → 2.50 s** (−64.1%); user CPU **12.17 s → 6.96 s** (−42.8%); cumulative `simp` **7.31 s → 1.58 s** (−78.4%); cumulative tactic execution **5.26 s → 2.73 s** (−48.1%) | `ExecRefine.olean` **4,445,176 B → 4,351,928 B** (−93,248 B); generated C **38,960 B → 38,960 B**; `ExecRefine` +6 lines and `EraKernel` −22 lines, lane net −16 | One before and one after source-only `lake env lean --profile --json`, wrapped in `/usr/bin/time -lp`; imported oleans retained, no deliberate warmup, Lean default parallelism. Directional, not a controlled median. |
| `Preo.Expr` simp normal forms | cumulative emitted `simp` events **950 ms → 55.3 ms** (−94.2%) | source **885 → 929 lines** (+44; +124/−80), **35,592 B → 37,245 B**; current olean **3,495,424 B**, with no retained baseline olean | One serial post-change `lake env lean -j1 --profile --json` run compared with one profiler-lane baseline. Warm imports were present. This is a diagnostic single shot, and the gain spans the `reads_*`, `eval_ext`, `MergeSafe.sound`, and fixture refactors. |
| Six-status specification and consumers | summed source-check wall **6.40 s → 5.72 s** (−10.6%) | owned three-module source **2,999 → 2,994 lines**; consumer-file nets: `RenderSix` −54 and `StatusEffects` −58 lines; owned olean net −6,832 B, five-target olean net +22,392 B | One fresh isolated-clean-clone direct source pass per target, summed across `ResultStatus`, `RenderSix`, `StatusEffects`, `RenderProgress`, and `Preo.ResultProgram`. N=1 per file; a directional aggregate with wall-noise caveat, not `lake build`. |
| Coherent-history proof kernel | three symbolic-subtraction proof hotspots **606 ms combined → one 74 ms shared kernel** (−87.8%) | `Histories` + `HistoryBase` + `HistoryPolicy` **4,665 → 4,666 lines** while adding reusable rank, induction, reachability, and budget APIs | One declaration-profiler diagnostic pass under concurrent swarm load, not repeated end-to-end module wall measurements. The 74 ms theorem replaces repeated proof search; each former theorem fell below the 40 ms reporting threshold, though its thin wrapper still elaborates and typechecks. |
| Pairwise-disjoint `flatMap` and sublist proofs | duplicated target proof blocks **149 → 77 lines** (−48.3%) | three consumer files +60/−129, net −69 lines; new reusable `ListProofs` module 122 lines, so owned source net **+53 lines** including documentation and three generic fixtures | Structural proof-LOC measurement. Current one-shot source checks were 0.77 s (`ListProofs`), 0.96 s (`Sequence`), 1.28 s (`SeqKernel`), and 2.14 s (`Fugue`); there is no comparable before timing, so no speedup is claimed. |
| Preo artifact production split | transitive production closure **36 → 12 modules** (−66.7%); generated C-source closure **4,460,710 B → 1,382,061 B** (−69.0%) | public artifact/export/projection/journal declarations retained behind data, checked, diagnostics, durable-core, and journal-diagnostics boundaries | Static import-closure and generated-source measurement. It measures what production artifact consumers pull in, not elapsed runtime or the final linked archive below. |
| `Preo.Demo` proof cleanup | cumulative tactics **230 ms → 167 ms** (−27.4%); type checking **419 ms → 311 ms** (−25.8%); compilation-category sum **350.3 ms → 302.9 ms** (−13.5%); user CPU **4.06 s → 3.65 s** (−10.1%) | peak RSS **1,412,513,792 B → 1,393,180,672 B** (−1.37%); source +18/−4 lines; olean **1,472,352 B → 1,473,824 B** (+0.10%) for the new named render-result proof | Identical clean dependencies, serialized; one unmeasured warmup plus three native `lean --profile` runs, reporting medians. Wall was noisy and adverse (**3.88 s → 4.37 s**), so this row makes no wall-speedup claim. |

Profiler categories are cumulative and nested: `simp`, tactic execution,
typeclass inference, type checking, and compilation must not be added together
or read as a partition of wall time. Lean can elaborate in parallel, so user
CPU may exceed wall. Source lines include comments, fixtures, and preserved
public wrappers; LOC is a maintenance measure, not a runtime proxy. Olean and
generated-C sizes are toolchain-specific and say nothing by themselves about
semantic equivalence.

### Runtime archive and final gate

Before Wave 23, `build.rs` recursively compiled the root and every emitted
Uwueave C file. The observed archive held **116 members including the shim** and
was **54,425,248 B**. The new closure is derived from Lake's
`RuntimeInit.setup`: 12 transitive kernel imports plus `RuntimeInit` itself,
exactly **13 Lake-owned objects / 655,368 raw bytes**. The verified archive is
exactly **14 members including the shim / 798,968 B**. Against the observed old
archive that is **87.9% fewer members** and **98.53% fewer bytes**. The 12-module
artifact-production closure in the table above and the 13 Lean objects here are
not a disagreement: the latter adds the generated `RuntimeInit` root object.

| validation point | result |
|---|---|
| isolated rebuild after moving aside exactly the 13 generated `c.o` outputs | **1.07 s** |
| immediate Lake no-build object query | **0.14 s** |
| final full Cargo gate after the documentation fix | **147.13 s**, green |
| unchanged `cargo test --quiet` | **0.93 s**, green |
| final Lean/audit coverage | **126 jobs; 117 root modules; 20,446 constants audited** |
| final Rust suite | **132/132 tests passed** |

The 1.07 s closure rebuild is the isolated linker/build-graph datapoint. The
147.13 s validation duration includes the fail-closed full Lake gate, native C,
Rust build, and tests on a shared swarm machine; it is evidence that the whole
path passed, not a reproducible speedup claim. The 0.93 s unchanged run skips
work that Cargo has already proved fresh and therefore must not be compared with
the full run.

### How future proof/build measurements should be run

Use the checked-in serial profiler for source elaboration:

```
scripts/proof-profile.sh Uwueave/ExecRefine.lean Uwueave/Preo/Demo.lean
```

It performs one unmeasured warmup and three measured runs by default and reports
medians as TSV. `UWUEAVE_PROFILE_RUNS` may select another positive odd run
count, and `UWUEAVE_PROFILE_WARMUPS` controls warmups. For a publishable
before/after comparison:

1. Use clean worktrees at named commits, the same Lean toolchain and machine,
   and identical imported oleans. Run the two revisions serially with no other
   Lean or Cargo workers.
2. Report medians for wall, user, system, RSS, and profiler categories; retain
   raw logs. State explicitly whether a result is source-only, `lake build`, a
   Lake object query, or the fail-closed Cargo gate.
3. Record source, olean, generated-C, and archive deltas separately. Do not use
   cached-build wall time as the baseline for a source-only run, or archive
   shrinkage as evidence of kernel throughput.
4. Run the broad Cargo gate only against a frozen tree. Its final no-build check
   deliberately rejects a source or setup change that races the build; a failed
   concurrent run is a useful freshness test, not a benchmark sample.

Runtime kernel comparisons still belong in the harness and protocol of §§10–11.
Proof/build improvements in this section make the verified system cheaper to
develop and ship; they do not change the runtime numbers above unless measured
again by that harness.

---

## 13. Wave 24 elaboration and module-boundary engineering — 2026-08-11

Wave 24 turned three large elaboration/fixture surfaces into small production
facades backed by explicit worker or core modules. These are source-elaboration
and static import-closure results, not measurements of the generated program's
runtime. As in §12, profiler categories are cumulative and nested and must not
be summed into wall time.

### Preoscript elaborator decomposition

| measurement | before | after | change / interpretation |
|---|---:|---:|---|
| direct `Preo.Elab` source-check wall | **39.35 s** | **1.18 s** | **−97.0%** arithmetically; the public facade now registers handlers and delegates to compiled phase workers |
| whole-file cumulative LCNF-base | **about 33.1 s** | **0.813 ms** | the facade now contains no phase implementation |
| `elabPreoDecl` LCNF-base event | **32.2 s** | eliminated | its replacement `Declaration` module reports **43.2 ms** cumulative LCNF-base |
| largest individual worker LCNF-base | included in the 32.2 s monolith | **1.28 s** | no extracted phase recreates the original hotspot |
| aggregate worker LCNF-base | included in the 32.2 s monolith | **about 4.16 s** | useful work moved behind independently cached module boundaries rather than disappearing |

The after facade, workers, `ProtocolSurface`, and `Demo` passed an **81/81**
focused build. Acceptance fixtures check the generated constant names and
types, persisted row ordering, equality-only typed-result future, exact reach,
reports, cache/update laws, native protocol fixtures, and failure behavior.
A required late-phase failure rolls back both generated constants and
`preoExt` rows; immediate reuse of the same declaration name succeeds.

The baseline was one source-only default-threaded
`lake env lean --profile --json Uwueave/Preo/Elab.lean` under
`/usr/bin/time -lp`, with existing imports: wall 39.35 s and user CPU 36.97 s.
The after facade and each of 14 workers were checked sequentially once with
`lean -j1 --profile`, again retaining imported oleans and clearing no cache.
The largest worker wall was **3.25 s** (`TypedDerive`, including 1.12 s import),
and the largest RSS was **1,309,900,800 B** (`Invariant`). The 4.16 s aggregate
is the sum of cumulative LCNF-base buckets, not a predicted wall time; summing
the 15 source-process walls would repay imports 15 times and is not a useful
comparison. Different thread settings and N=1 make the wall reduction strong
structural evidence rather than a controlled statistical estimate.

The thin facade itself fell from **1,718 lines / 92,797 B** to **45 / 1,242 B**;
its olean from **13,645,800 B** to **18,720 B** and generated C from
**5,278,203 B** to **8,269 B**. Those are facade-boundary reductions, not total
artifact reductions. The 14 workers plus facade occupy **2,170 lines /
104,376 B**, **15,919,888 olean bytes**, and **5,881,678 generated-C bytes**.
They now include native protocol grammar/core that previously lived in the
separate `ProtocolSurface`; its old artifact was not retained. Consequently a
correct combined old-Elab-plus-old-ProtocolSurface comparison is unmeasured,
and neither a combined artifact regression nor saving is claimed.

One post-split Demo source profile (`lean -j1`) reported **3.47 s wall**,
**2.84 s user**, **0.54 s system**, **746 ms import**, **897 ms
interpretation**, **330 ms elaboration**, **299 ms type checking**, **340 ms
typeclass inference**, and **1,389,658,112 B peak RSS**. The largest emitted
handler event was `NestedSurface` at **218 ms**. The exact clean-warm Wave 23
RSS reference was 1,412,513,792 B, making the RSS change −1.62%, but wall and
handler comparisons to earlier runs are non-paired because cache, thread, and
run conditions differ. Demo's source change was one explicit examples import.

### Projection production closures

Closure counts below come from each root's Lake `setup.json` transitive project
import keys, with the root counted separately; byte totals are the exact
corresponding olean and generated-C files. The before side uses the retained
Wave 23 setup artifacts.

| production root | project modules | olean bytes | generated-C bytes |
|---|---:|---:|---:|
| Projection V1 before | **47** | **36,384,896** | **5,278,509** |
| Projection V1 after | **3** (−44; −93.6%) | **3,354,088** (−90.8%) | **621,168** (−88.2%) |
| Projection V2 before | **48** | **38,263,712** | **5,796,707** |
| Projection V2 after | **4** (−44; −91.7%) | **4,290,744** (−88.8%) | **665,363** (−88.5%) |

V1 production now consists of `ArtifactData`, `ProjectionV1Core`, and the V1
renderer; V2 adds `ProjectionV2Core` and its renderer while sharing the first
two dependencies. Diagnostics, examples, `Repr` instances, and giant golden
renderer equalities are opt-in modules. This intentionally narrows what a
direct production import provides; aggregate roots retain the broader public
surface for users that need it.

Single uncontended source profiles were **0.63 s / 195 ms elaboration** for
V1Core, **0.36 s / 52.4 ms** for the V1 facade, **0.57 s / 130 ms** for V2Core,
and **0.34 s / 45 ms** for the V2 facade. They are diagnostic points, not
sampled before/after wall benchmarks. The expensive renderer fixtures remain
real work: their last isolated builds were about **12 s** for V1 and **27 s**
for V2, now paid only by fixture consumers. A ten-target no-op build completed
all **57 jobs**, and the combined elaborator/protocol/demo gate completed all
**81 jobs**. Production setup checks found no `Export`, `Scheduling`, or
`Tactics` dependency, and recursion-depth overrides occur only in fixtures.

### Proof cleanup and shipping closure

The minima, path-edge, and semilattice cleanup added 140 lines and removed 185
across `CoordEffect`, `SeamColoring`, `ForkGrade`, `Confluence`, `ClashGraph`,
and `CliqueLive`: **net −45 lines**, including 168 removed nonblank,
non-comment proof lines. In one sequential direct `lean -j1 --profile --json`
source pass per file, the sum of emitted tactic-execution summaries fell from
**1,361.4 ms to 973.7 ms** (**−387.7 ms / −28.48%**). Imports were retained,
with no cache reset, warmup, or repetitions; reruns were visibly noisy. This is
a directional profiler workload aggregate rather than a wall-speedup claim.
The durable result is that public theorem names remain as
thin wrappers over Std `List.min?` / `List.minOn?`, one canonical path
`flatMap`, and shared absorption laws. The focused **41-job** build and full
**126-job** downstream/Audit gate passed; Audit covered **117 root modules and
20,477 constants** within the trust floor.

Wave 24 also added explicit artifact-emission and durability coverage without
widening the shipping FFI graph. The runtime closure remains the Wave 23 value:
**13 Lean objects / 655,368 raw bytes**, and the archive protocol and caveats in
§12 are unchanged. Both real emitted artifacts survive frame creation,
append, close/reopen, exact-byte and BLAKE3 checks; mutation, truncation, and a
wrong version are refused. This is functional durability evidence, not a new
archive-size or runtime-throughput benchmark.

### Preoscript command corpus and hard goldens

The command-level comparison uses **21 cases**, each run with two unmeasured
warmups followed by five serialized `lean -j1 --profile` measurements under
`/usr/bin/time -lp`. A wall or user-time median absolute deviation above 8%
triggers a clean nine-run retry; a persistent value above 8% is labelled
infrastructure-noisy rather than reported as a speedup. The baseline is commit
`ab4c767` in a detached temporary worktree with the same corpus copied in and
normal dependencies built and warmed. No cache clearing or declaration trace
profiler is mixed into the timed samples.

Each table entry below is therefore the median of five runs, or of the fresh
nine-run replacement set when the MAD rule fired. `import_syntax` was the only
current retry and stabilized at 4.08% wall MAD; four baseline cases also
stabilized, with no persistent-noise label. Wall/user/system are seconds from
`time`, RSS is its byte result converted to binary MiB, and Lean profiler
categories are cumulative milliseconds grouped by label. The 213 checks are
21 cases × 10 regression metrics plus three typed-scaling checks.

Performance samples are only half the acceptance contract. Separate hard
goldens pin **94 generated names and canonical types**, persisted `preoExt` row
order, the exact **42-line** report, required diagnostics, rollback, and reuse
of a failed declaration name. The final comparison produced **210 passes, two
warnings, and one scale failure across 213 checks**. Selected medians are:

| corpus case | wall, before → after | user CPU, before → after | peak RSS, before → after | selected profiler category, before → after |
|---|---:|---:|---:|---:|
| import + elaborator syntax | **0.96 → 0.94 s** | **0.39 → 0.40 s** | **1,181.2 → 1,182.9 MiB** | elaboration **0.19 → 0.15 ms** |
| 32 built-in fields | **1.82 → 1.79 s** | **1.18 → 1.21 s** | **1,247.8 → 1,248.6 MiB** | elaboration **73.6 → 71.5 ms**; type checking **32.1 → 31.1 ms**; compilation **90.9 → 88.3 ms** |
| 32 custom fields | **1.92 → 1.86 s** | **1.35 → 1.29 s** | **1,257.2 → 1,258.2 MiB** | elaboration **70.0 → 66.2 ms**; compilation **140.0 → 133.3 ms** |
| 16 typed derives | **1.97 → 1.86 s** | **1.39 → 1.36 s** | **1,269.8 → 1,269.2 MiB** | elaboration **31.7 → 30.8 ms**; type checking **186 → 182 ms**; compilation **100.4 → 97.5 ms** |
| export command | **1.14 → 1.07 s** | **0.56 → 0.55 s** | **1,217.7 → 1,218.9 MiB** | elaboration **6.70 → 6.56 ms**; type checking **37.2 → 32.8 ms** |
| all command families | **1.25 → 1.23 s** | **0.68 → 0.66 s** | **1,233.3 → 1,234.0 MiB** | elaboration **12.5 → 12.2 ms**; compilation **23.0 → 22.1 ms** |
| late rejection/rollback | **1.00 → 0.91 s** | **0.42 → 0.42 s** | **1,196.6 → 1,197.4 MiB** | elaboration **2.26 → 2.06 ms** |

The two warnings were profiler import time: the syntax-import case rose from
**721 to 857 ms** (+18.9%), and the eight-field case from **771 to 849 ms**
(+10.1%). Neither is disguised as an elaboration regression or folded into a
single aggregate score. The remaining scale failure is typed-incremental peak
RSS per item: **6,692,864 B → 4,943,872 B** (**−26.1%**), still **4.71 MiB**
against a hard 4 MiB ceiling. Its user CPU per item passed at
**0.060 → 0.05875 s** (−2.1%), and elaboration per item was essentially flat at
**1.8225 → 1.8231 ms** (+0.03%).

All current hard goldens pass. The historical baseline exposes one semantic
failure that timing cannot: a malformed late typed derive leaked generated
field constants, so an identical declaration name could not be reused. The
current transactional command rolls back both declarations and report rows,
and the same-name reuse golden passes. That correctness fix is the primary
result even where the command medians are nearly flat.

---

## 14. Wave 25 typed-query, world-binding, and V3 engineering — 2026-08-11

Wave 25 extended the typed-query path through explicit application-state
projection, named world futures, certificate-gated reports, proof-indexed V3
rows, canonical V3 bytes, and an end-to-end Quickstart. The measurements in
this section are elaboration, artifact-size, static-closure, and functional
acceptance evidence. They do not update the runtime-kernel timings in
§§10–11, measure filesystem durability, or establish that an authored reach is
the set of states a deployment will visit.

### Typed scaling and exact surface pins

The Wave 25 comparison reused §13's serialized Preoscript benchmark protocol
and, crucially, the same typed-scaling definition: subtract the `Typed0`
control from `Typed4` and `Typed16` peak RSS before dividing by the number of
typed declarations. The resulting N=4→16 RSS slope fell from **4.713 to 3.946
MiB per item** (**−16.3%**), below the hard 4 MiB/item ceiling and therefore a
pass. `Typed16.olean` fell from **854,024 B to 736,048 B** (**−13.8%**).

The exact names/types golden now pins **88 generated constants**. It passed
together with row-order, rollback/reuse, constructor, projection, and report
API checks. Six compiler-generated `ReachReport` metadata constants were
intentionally retired; this is why the pin count itself is not a performance
metric. The RSS slope is a benchmark-runner measurement, while the olean delta
is a file-size observation; neither is evidence about generated query runtime.

### New checked-program surfaces

The following are present-cost diagnostics. Except for the typed slope above,
there is no paired pre-Wave-25 implementation of these modules, so the table
does not claim speedups or compare one module's wall time with another's. Lean
profiler categories are cumulative and nested and must not be summed.

| surface | observed source-profile evidence | artifact / qualification |
|---|---|---|
| `StateProgram` core | import **924 ms**; elaboration **50.2 ms** | explicit `State → Env` projection and authored finite reach; no retained wall/RSS sample |
| `StateProgramSurface` | import **1.05 s**; elaboration **355 ms**; LCNF-base **1.07 s** | command elaborator over the checked core; no retained wall/RSS sample |
| `PlanningSurface` | wall **4.58 s**; user **3.82 s**; import **883 ms**; elaboration **582 ms**; tactics **137 ms**; type checking **144 ms**; LCNF-base **1.94 s**; peak RSS **1,339,424,768 B** | olean **2,642,792 B**; generated C **1,037,142 B** |
| `DerivedProgram` | import **990 ms**; elaboration **79.7 ms**; tactics **65.0 ms**; `simp` **22.2 ms**; type checking **25.6 ms** | direct source diagnostic; duplicated roughly 55-line range-proof bodies are wrappers over foundational `Expr` theorems; no retained wall/RSS sample |
| `BoundResult` | direct warning-free source check **0.88 s** | **232 LOC**; exact future, declaration-answer, certificate, and world-index binding |

These are mixed single-shot/source-profile observations collected during the
Wave 25 swarm, with warm imports and varying contention. They are useful for
locating future elaboration work, not publishable medians. In particular, the
PlanningSurface wall/RSS row must not be compared with a category-only row.

### V3 production closure

Static closure counts come from project-module import closure with exact olean
and generated-C byte totals. Direct profile times are one-shot source
diagnostics, not runtime or clean-build measurements.

| V3 root | project modules | olean bytes | generated-C bytes | direct profile wall |
|---|---:|---:|---:|---:|
| production Rust renderer | **7** | **6,947,616** | **1,100,478** | **0.33 s** |
| structural validator core | **5** | **6,319,784** | **808,390** | **0.63 s** |
| canonical durable V3 codec | — | — | — | **0.49 s** |

The renderer is deliberately one module and about 1.95 MB (1.63 MiB) of olean above the
provisional six-module / 5 MiB target because it reuses the unchanged V2
renderer instead of duplicating its DTO logic. Its generated-C closure remains
below the separate 1.2 MB target. That is a target caveat, not a claimed
regression against a retained V3 baseline. The focused V3 suite passed
**76/76** checks, the generated Rust was **11,364 B** and compiled with
`rustc`, and V2 fixtures remained unchanged and green.

### End-to-end Quickstart bytes

`lake build Uwueave.Preo.Quickstart` completed **98/98** jobs; its last warm
compile was **1.7 s**. One warm `preo-quickstart-canaries.sh` run took **8.4 s**
and covered one positive compilation, five expected compile refusals, and the
runtime path. These are warm validation durations, not cold-build benchmarks.

The runtime fixture wrote the exact stack-safe frame proved equal to
`ArtifactV3Durable.projectionBytes`: **71,011 B** for one frame and **142,022
B** for the concatenated two-frame logical journal. It read the bytes back
exactly and exercised both pure-Lean frame/journal inspection and the external
inspection CLI. Exact byte equality and successful reopen are functional codec
evidence; they do not measure I/O throughput, prove stable-media persistence,
or authenticate a journal.

### History runtime and host journal evidence

`HistoryRuntime.lean` is **568 LOC / 25,266 source bytes** with a **1,883,936 B**
olean; `PersistentHistoryRuntime.lean` is **170 LOC / 7,227 source bytes** with
a **178,416 B** olean. One warm-cache profiled source check under active swarm
contention reported:

| module | wall | import | cumulative elaboration |
|---|---:|---:|---:|
| `HistoryRuntime` | **2.11 s** | **1.39 s** | **301 ms** |
| `PersistentHistoryRuntime` | **1.62 s** | **1.35 s** | **65.1 ms** |

The focused Lean build passed **36/36** jobs. The pure-Rust history journal
implementation is **761 LOC / 26,380 source bytes**; its focused library test
selection passed **6/6** tests. On the recorded run the test bodies reported
**0.00 s**, while command wall was **2.85 s**, including **2.60 s** of
compilation. That split is why this is focused correctness evidence, not a
journal-latency number. Owned-file `rustfmt --check` and diff checks passed;
workspace-wide `cargo fmt --check` still observed unrelated formatting drift
and is not reported as green.

### Final Wave 25 closure

The final aggregate Lean build completed **171 jobs**. The audit traversed
**147 direct root imports excluding `Audit`** and checked **23,138 constants**
against the trust floor. The final Rust accounting passed **140 tests**:
87 library, 13 CLI, one artifact-emission, one inspection, four ergonomics,
15 persistence, 11 property, six closure, and two census tests.

Those counts establish final source/build/test coverage on the frozen Wave 25
tree. As throughout this document, a green aggregate duration would mix cache,
link, compiler, and test work, so no aggregate wall-speedup is inferred from
the job or test totals.

---

## 15. Wave 26 proof reuse, observation, and export hardening — 2026-08-11

Wave 26 consolidated canonical framing and exact-result proofs, added typed
value/source/position attribution, separated authenticated running observation
from authored analysis reach, hardened V3 validation and export, and expanded
the logical/Rust history runtime. As in §14, this section mixes several
explicitly labelled evidence classes: paired profiler comparisons, single-shot
source diagnostics, static closure and file sizes, and functional acceptance
counts. None is a new runtime-kernel benchmark, filesystem refinement, source
authentication protocol, or proof that an authored reach equals deployment
reach.

### Canonical stack-safe framing

One generic stack-safe framing API in `ArtifactDurableCore` replaced three
local encoders. Relative to the Wave 25 source, `ArtifactDurableCore` gained 92
lines while `ArtifactEmit`, `Quickstart`, and the V3 fixture lost 33, 24, and 2
respectively: **113 insertions / 80 deletions, net +33 LOC**. The following
exact byte gates remained unchanged:

| framed value | exact bytes |
|---|---:|
| semantic V2 artifact | **33,331 B** |
| full V2 artifact | **15,887 B** |
| fixture V3 artifact | **41,249 B** |
| Quickstart V3 artifact | **71,011 B** |
| two Quickstart frames as a logical journal | **142,022 B** |

The narrow build completed **103 jobs**. Last warm target observations were
0.14 s for the core, 0.14 s for emission, 1.55 s for the V3 fixture, and 4.82 s
for replay-heavy Quickstart. These are noisy incremental validation durations,
not before/after samples or framing-throughput measurements. Exact bytes,
version/domain/trailing-suffix refusals, reopen, and inspection are functional
codec evidence; they do not prove stable-media durability or authenticity.

### Typed attribution

The typed attribution path now derives full expression positions from exact
`Expr.Hole` analysis and requires an external `SourceAuthenticity` proof before
materialization. Its focused build passed **32 jobs**. Single post-change source
profiler diagnostics reported:

| module | cumulative tactics | cumulative `simp` |
|---|---:|---:|
| `Holes` | **58.8 ms** | **4.94 ms** |
| `Evidence` | **162 ms** | **23.3 ms** |
| `DerivedDocument` | **87.7 ms** | **1.87 ms** |
| `DerivedProgram` | **53.6 ms** | **19.9 ms** |

Profiler categories are nested, these are not summed into wall time, and no
before samples were retained; the table locates current proof work rather than
claiming a speedup. The new exact membership/union laws remain relative to the
authored `World → Source` attribution. They do not authenticate a source or
prove that an externally named position was actually read unless it came
through the checked typed-hole adapter.

### Exact-result proof reuse

`ResultProgram.ExactSnapshot` centralizes the exact singleton-answer,
settledness, evaluation, and total-soundness construction shared by
`Incremental` and `StateProgram`. The source change was **+64/−103 lines, net
−39**, replacing 100 duplicated proof lines with 36 shared/helper-wrapper
lines while preserving public names, types, and definitional reductions.

On the retained declaration-profiler comparison, the consumer theorem sum fell
from **32.704 ms to 6.604 ms** (about −80%). Charging the new shared helper as
well gives **32.704 ms to 21.687 ms** (**−33.7%**) for the whole migrated proof
work. These are declaration-level elaboration measurements, not module wall
times; helper and wrapper accounting is stated separately precisely to avoid
making displaced work disappear. The downstream focused gate passed **99/99**.

### Authenticated observation and transactional V3 surface

`ObservedBoundResult` is a **202 LOC / 9,154 B** proof adapter. Its direct
source check was about **1.0 s** and a fresh dependency build completed **42/42
jobs**. Construction requires all of the following at one exact index: a
caller-supplied `ObservationBoundary.Authentic` witness, running-reach
membership, authored-world-reach membership, and a certificate for the exact
bound declaration answer. No definition performs I/O, discovers running reach,
or constructs authenticity. Consequently the deployment-observation marker is
narrowed but not closed.

The transactional `preo_export_v3` production surface is **527 LOC**. One fresh
focused macOS `/usr/bin/time -l lake env lean` source compile reported **13.55 s
wall, 12.16 s user, 0.74 s system, and 1,421,836,288 B peak RSS**. It is a
single cold/focused observation, not a serialized corpus median or a baseline
comparison. The focused build completed **100 jobs**.

Acceptance comprised **3 green subprocess fixtures**, **14 standalone expected
refusals**, and one additional guarded `maxWork` refusal: **15 expected-red
commands total**. The positive surface audits **48 generated prefix constants**
against the axiom floor. The observation positive pins the exact world, state,
certificate, and report and kernel-checks forged-world and stale-index
refusals. Other red paths cover forged state, absent running reach, bare or
structural-lookalike reports, wrong query/projection/future/binding/world/index/
certificate answer/plan/base, resource bounds, a custom axiom, `sorryAx`, and
`native_decide`. Rollback proves five declarations absent before successful
same-name reuse. The corpus is **19 Lean files including two supports, plus the
runner, totalling 766 LOC**. This is adversarial typechecking evidence, not a
runtime authentication test.

### V3 validation and production closure

V3 hardening passed **108/108** focused checks and added fail-fast resource,
stable-ID, ordering, path, and analysis validation plus proof-gated append
ordering. Its current production renderer closure is **7 project modules,
7,521,384 olean bytes, and 1,230,875 generated-C bytes**. One source-profiler
pass reported **377 ms cumulative elaboration** for the validation core and
**39 ms** for the renderer. These category values are not wall time.

The seven-module renderer continues to reuse V2 infrastructure rather than
duplicate it. The closure is therefore evidence of current shipping cost, not
a paired reduction. Certificate-to-result wire association, stable name
registries, and topology-aware hole-path checking remain explicit boundaries.

### Planning surface

Splitting `PlanningSurface.emitSelected` into two private phases preserved the
public API and emission order. The comparison used serialized direct source
checks, `lake env lean -j1 --profile`, wrapped in `/usr/bin/time -lp`: two
unmeasured warmups followed by five measured runs, reporting medians with no
cache clear or trace profiler. The paired medians were:

| measurement | before | after | change |
|---|---:|---:|---:|
| cumulative LCNF | **2,310 ms** | **639 ms** | **−72.3%** |
| wall | **7.44 s** | **3.71 s** | **−50.1%**, baseline-noisy |
| import | **1,750 ms** | **1,160 ms** | **−33.7%** |
| elaboration | **837 ms** | **718 ms** | **−14.2%** |
| peak RSS | **1,340,653,568 B** | **1,321,091,072 B** | **−19,562,496 B** |
| olean | **2,642,704 B** | **2,459,328 B** | **−183,376 B / −6.94%** |
| generated C | **1,007,938 B** | **1,012,370 B** | **+4,432 B / +0.44%** |

The exact 88-pin golden still passes and typed scaling remains **3.940
MiB/item**, below the 4 MiB guard. The focused V3, StateProgram,
PlanningSurface, and Quickstart build passed **99/99**. LCNF is a cumulative
compiler category, RSS is process peak, and olean bytes are an artifact size;
only like-for-like rows are compared. The baseline cohort was
infrastructure-noisy (LCNF ranged 1,840–5,340 ms and wall 4.53–10.75 s), while
the after cohort was tighter (LCNF 612–808 ms and wall 3.33–4.35 s). The
structural LCNF reduction is useful evidence, but the wall percentage should
not be treated as a controlled speedup.

### History runtime and bounded host queue

Relative to Wave 25, `HistoryRuntime` grew **568→880 LOC** (+312),
25,266→39,571 source bytes, and **1,883,936→3,151,328 olean bytes**.
`PersistentHistoryRuntime` grew **170→296 LOC** (+126), 7,227→12,389 source
bytes, and **178,416→333,560 olean bytes**. The Rust history implementation
grew **761→1,073 LOC** (+312) and is now **38,305 B**.

One warm-cache source profile under active multi-agent contention reported:

| module | wall | import | cumulative elaboration |
|---|---:|---:|---:|
| `HistoryRuntime` | **2.04 s** | **0.940 s** | **508 ms** |
| `PersistentHistoryRuntime` | **1.30 s** | **0.965 s** | **132 ms** |

These are single samples, not medians. The focused Lean build passed **36/36**.
The focused Rust selection passed **8/8** with 81 filtered; the latest command
spent **11.74 s** compiling and reported **0.00 s** in test bodies, so it is not
a queue-latency measurement. Strict Clippy found only five existing unrelated
lint failures; rerunning with exactly those categories allowed passed in 4.27 s.

The semantic caveat is load-bearing: Lean checkpoints authoritative buffered
arrivals, while Rust's bounded pending buffer is volatile and disappears on
reopen. No durable Rust arrival queue or Lean↔Rust refinement theorem is
claimed.

### Final Lean and native closure

The frozen production aggregate completed **173 Lean jobs in 3.72 s**. The
trust audit traversed **149 direct root modules excluding `Audit`** and checked
**23,757 constants**. This was a warm final validation duration, not a cold
build or speedup sample.

The native runtime closure remains **13 Lake-owned objects**, now **659,152 raw
bytes** before archive. The verified archive has **14 members / 803,520 B**:
the 13 uniquely named objects plus the sole shim. All 13 Lake source, staged,
and archived object bytes matched; the audit found zero unresolved same-package
initializers and all **7/7** required initializer/FFI definitions. Relative to
Wave 25 this is +3,784 raw object bytes and +4,552 archive bytes, not a change
in object count or FFI surface. Archive SHA-256 was
`29cea783e844895d44fa72d91b79512535d449181e379b5d2c06f31a2621915a`.

The final `cargo test --all-targets` gate passed **142 tests / 0 failures** in
**11.94 s real**; Cargo's own finished phase was **0.07 s**, so the wall figure
is a validation-path duration, not Rust test-body throughput. The accounting
was 89 library, 13 check-CLI, one artifact-emission, one artifact-inspection,
four ergonomics, 15 persistence/history, 11 property, six runtime-closure, and
two UNDONE-census tests. The fail-closed closure check repeated the exact
**13 objects / 659,152 B** warning line above.

---

## 16. Wave 27 authenticated progress, durable arrival, and an honest V3 no-go — 2026-08-12

Wave 27 added an authenticated frontier-progress envelope, a signed
world-context adapter, a one-way RuntimeAuthV4 sidecar, and a durable bounded
arrival journal. It also centralized V3 effect-shape proofs and subjected the
full V3 export command to a serialized scaling protocol. The evidence classes
remain separate below: proof/module profiles, artifact sizes, subprocess
acceptance, a repeated RSS benchmark, and host-runtime integration tests.
Signatures do not make a progress claim true, persistence does not authenticate
opaque bytes, and none of these rows updates the decision-kernel timings in
§10.

### Authenticated frontier and world context

`AuthenticatedFrontier` is **237 LOC / 10,096 source bytes**, with a **279,384
B** olean and **20,111 B** generated C. Its final focused build completed
**37/37** jobs; the changed target took 0.973 s on that run. It retains the
exact accepted signed event, received-trace membership, issuer-log issuance,
issuer/source and finite-roster binding, timestamp, before/after frontiers,
and issued/old-delivered/new-delivered sets. The semantic
`Frontier.DeliveryAdvance` proof is independent of signature acceptance and
uses those exact signed-event codec projections. The codec is authored model
semantics: an external or running state must separately prove equality to its
projections. No signature primitive, issuance log, network trace, or runtime
state is manufactured here.

`AuthenticatedWorldContext` is **914 LOC / 42,183 source bytes**; approximately
316 lines are theorem/example bodies. Its current artifacts are **2,229,360 B
olean / 69,469 B generated C**. One post-change direct source profile, with no
warmup, cache reset, repetition, or before sample, reported:

| category | one-source diagnostic |
|---|---:|
| import | **1.33 s** |
| elaboration | **250 ms** |
| tactic execution | **89.1 ms** |
| `simp` | **29.0 ms** |
| type checking | **159 ms** |
| typeclass inference | **46.4 ms** |

These nested profiler categories are workload-location evidence, not an
elapsed-time sum or benchmark. The focused downstream build passed **73/73**.
Positive and refusal proofs cover exact typed positions, lawful frontier
progress, forgery, stale base, wrong origin, and one-use token reuse. The
strict one-use grant invariant intentionally rejects same-grant
multi-candidate batches. External EUF-style security, observed deployment
state, and cryptographic construction remain explicit premises.

### RuntimeAuthV4 checked sidecar

The one-way RuntimeAuthV4 path is split into **7 isolated Lean leaves**, now
**1,111 LOC / 44,655 source bytes** in aggregate. Its focused build passed
**61/61**. The canonical fixture is exactly **369 B**, SHA-256
`a9f32051b0e1e328ab08b253a808ba54cc5c4a4e9cb2b5d2550c3811cf03b819`, and
the generated Rust compiled and passed lookup checks. The checked builder,
bounded validator, framing, and adversarial negatives establish one-way
construction and byte-level rejection behavior; they do not reconstruct Lean
proofs from decoded bytes, prove signature hardness, infer a capability holder,
or claim wire compatibility with the existing `UWV4` request format.

### Canonical effect-shape proof reuse

The six finite effect probes and their canonical ordering now live once in
`StatusEffects`; V3 consumes that reification rather than carrying a duplicate
six-shape relation and reconstruction tree. One declaration-profiler proof-path
diagnostic fell from **153.311 ms to 22.584 ms** (**−85.27%**). This is proof
elaboration, not query evaluation or module wall time. All **36 refinement
cases**, canonical order, Quickstart rows, exact bytes, and reopen behavior
passed; the focused/downstream build completed **103/103** jobs.

### Full V3 export scaling: improved, still over budget

The authoritative protocol serialized **16/16 benchmark rows** covering V3
export, authenticated context, frontier, and V4 checked controls at
`N = 0/1/4/16`. Each row used two warmups followed by five measured runs and
reported the median. This cohort recorded zero noise classifications and zero
retries. Per-item slope subtracts the `N=0` process/import control before
dividing by the item count.

| measured slope | retained baseline | current | hard gate |
|---|---:|---:|---:|
| V3 peak RSS | **13,557,760 B/item** | **7,031,808 B/item = 6.7060546875 MiB/item** | **4 MiB/item: FAIL_SCALE** |
| V3 elaboration | **14.1425 ms/item** | **8.254375 ms/item** | diagnostic, no hard gate |

The independent controls pass comfortably: **36,864 B/item** for
authenticated world context, **84,992 B/item** for frontier, and **28,672
B/item** for V4 checked. Thus the remaining slope is localized to full V3
export rather than those imported semantic adapters. Improvement against the
retained baseline is real, but **6.706 MiB/item still fails** the 4 MiB cap and
is not reported as a pass.

The production `ArtifactV3Surface` was therefore restored exactly, with no
experimental patch retained: **527 LOC**, all **8 trust-floor checks**, the
exact **48-prefix audit**, and the **112-declaration golden** remain green.
Current artifacts are **4,331,056 B olean / 1,332,355 B generated C**; the
monolithic core accounts for **1,100,064 B / 82.57%** of C and 341 closed
helpers. `noncomputable`, `abbrev`, a reusable encoding helper, closed
extraction, and floor isolation either failed compatibility or produced no
admissible win. The strongest structural helper exposed only **41 prefix
constants**, removing seven required generated constants; it was rejected and
the exact 48-prefix surface restored. This is an engineering no-go result, not
a disguised optimization claim.

### Durable bounded arrival and runtime end to end

`PersistentHistoryRuntime` is now **338 LOC**, a net +42 from Wave 26, while
the Rust history implementation is **2,023 LOC / 73,599 source bytes**, a net
+950 lines. The new `HistoryArrivalJournal` has a distinct `UWHARR01` marker
and `uwueave.history-arrival-journal.v1` domain, versioned event/checkpoint
records, append-before-memory ordering, bounded pending state, deterministic
drain, no-write retry, and atomic collision/cap refusal. The focused Rust
history selection passed **12/12** tests with 81 filtered; its latest run spent
2.08 s compiling and 0.03 s in test bodies. One warm direct Lean source check
of `PersistentHistoryRuntime` took about 0.94 s. Neither is a throughput
benchmark.

The cross-language runtime integration passed **1/1** focused Cargo test in
**49.95 s**. The 369-byte V4 sidecar survives reopen exactly; retry, collision,
and cap refusals preserve file bytes and the state digest; parent arrival drains
deterministically; and reopened reverse-order and causal journals converge.
The native closure remains **13 objects / 659,152 B**, with no `RuntimeInit`,
build, shim, initializer, or FFI widening. A deliberately mutated sidecar also
survives as opaque payload. That negative is load-bearing evidence that this
layer persists bytes but does **not** authenticate them. Durability remains
relative to the configured sync policy and host filesystem; checkpoints are
integrity assertions, IDs remain unauthenticated, and no Lean↔Rust journal-byte
refinement theorem is claimed.

### Wave 27 aggregate acceptance and Lean closure

The frozen aggregate completed **182 Lean jobs**. An immediate cache replay
took **0.15 s**; that number is cache validation, not clean-build throughput.
The root audit traversed **158 modules**, found **181 Lean files** on disk, and
checked **24,921 constants** against the trust floor.

Wave-owned authentication/V4 acceptance comprised **3 positive fixtures and 18
standalone expected refusals**; the AF/AWC/V4 trust floors covered **17 / 284 /
30 constants** respectively. Delegated transactional V3 acceptance retained
**3 positives, 14 standalone expected refusals, and one guarded rollback
refusal** (**15 red command cases**). Durable-arrival acceptance passed **4/4**.
These counts establish checked coverage of the named positive and adversarial
surfaces; they are not statistical security or runtime-performance samples.

The final `cargo test --manifest-path rust/Cargo.toml --all-targets` gate passed
**147 tests / 0 failures** in **24.08 s real**, including **2.59 s** of
compilation. The accounting was 93 library, 13 `uwueave-check`, one artifact
emission, one artifact inspection, four ergonomics, 15 persistence, 11
properties, one runtime-auth arrival, six runtime-build closure, and two UNDONE
census tests. This is aggregate validation-path duration, not test-body or
journal throughput. Its fail-closed native warning remained exactly **13
objects / 659,152 B**.

---

## 17. Wave 28 authenticated ERA certificate — 2026-08-12

Wave 28 adds one proof-only leaf joining authenticated frontier progress to an
ERA finalisation certificate without collapsing their premises. This section
reports source/compiler size, proof elaboration, trust-floor acceptance, and
aggregate Lean coverage. It is not a runtime benchmark, cryptographic security
argument, byte decoder, or deployment observation.

`AuthenticatedEraCertificate` is **507 LOC / 22,097 source bytes**. Its current
artifacts are **404,648 B olean / 54,480 B generated C**. The focused build
passed **38/38** jobs. An immediate cached `lake build` replay took 0.14 s;
that is dependency-cache validation, not clean-build throughput.

One serialized direct source pass used
`lake env lean -j1 --profile --json Uwueave/AuthenticatedEraCertificate.lean`,
wrapped by macOS `/usr/bin/time -lp`, with existing imported oleans and no
warmup, cache reset, repetition, or retained before sample:

| profile observation | value |
|---|---:|
| wall / user / system | **5.56 s / 0.62 s / 0.96 s** |
| peak RSS | **1,249,247,232 B** |
| import | **5.17 s** |
| elaboration | **111 ms** |
| tactic execution | **20.6 ms** |
| `simp` | **9.72 ms** |
| type checking | **24.7 ms** |
| typeclass inference | **13.6 ms** |
| LCNF base / mono / impure | **8.43 / 6.91 / 3.22 ms** |

The unusually import-dominated wall observation was collected under active
swarm contention. Profiler categories are cumulative and nested; the table is
one-shot workload-location evidence, not a median, speedup, or sum of disjoint
costs.

The authority audit checked the separation rather than merely the final
theorem name. `AuthenticatedProgress` supplies exact accepted-event binding,
received-trace membership, genuine `WasIssued`, issuer/source equality, and
signer roster membership. `CompleteAnnouncement` separately ties the same
codec event to its cut, before/after worlds, issued pool, delivered log,
frontier settlement, and lawful `DeliveryAdvance.complete_after`. Only their
`Verification` conjunction yields `EraCertificate.Settled` and a reusable
certificate.

The reusable artifact deliberately forgets signature provenance and retains
only the exact ERA key plus `settledCert` proof. Its theorem is scoped to
`EraCertificate.Delivery` and exact-key equality. It does not license future
issuance or announcements, prove a cut newly added, authenticate every
candidate event or event ID, identify a designated arbiter, validate an
authored codec against bytes, or supply a deployed EUF-style security premise.
The positive fixture is therefore accompanied by load-bearing refusals for an
accepted-but-unissued record and an authenticated-but-incomplete cut.

The core `CompleteAnnouncement.settled` theorem depends on no axioms. The
delivery-scope, seal, and reusable-soundness projections inherit only the
repository's standard `propext`, `Classical.choice`, and `Quot.sound` floor;
the refusal theorems remain within that standard floor. The source contains no
`sorry`, `admit`, `unsafe`, `native_decide`, scoped recursion-depth override,
or heartbeat override.

Acceptance passed **1 positive fixture and 5 expected refusals**. Its prefix
audits covered **118 production constants and 4 fixture constants**. The final
Lean aggregate completed **183 jobs**, traversed **159 root modules**, and
checked **25,041 constants** against the trust floor. These are coverage
counts, not performance samples. Honest marker reconciliation left **155
markers / 153 blocks / 43 files**: model-level authenticated settlement is
closed, while deployed cryptography, event-ID authenticity, runtime generation,
and announcement-scope certification remain open.

The final all-target Cargo gate remained **147/147 green** in **16.00 s real**,
including **1.61 s** of compilation. No Rust target or test count changed in
this proof-only wave, and the native closure remained exactly **13 objects /
659,152 B**. The wall duration is aggregate validation-path time, not
certificate evaluation or runtime throughput.
