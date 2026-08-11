# PERFORMANCE

*First measurement pass, 2026-08-11. Before this file, nothing in this crate had
ever been timed.*

> **Historical-baseline note.** Sections 1–7 preserve the measurements from
> repo `31aac2b`, before the F1–F8 optimization pass. All eight fixes described
> in §9 are now implemented. Section 10 records a post-fix
> `BENCH_MAX=1000` rerun made on 2026-08-11; it is deliberately separate from
> the baseline and does not replace the original full-range sweep. Current
> complexity statements come from proved equivalence where applicable, source
> inspection, successful builds, and generated-C inspection; only the rows in
> §10 are new timings.

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
