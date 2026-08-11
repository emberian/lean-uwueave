//! **The measurement harness.** Nothing in this crate had ever been timed; every
//! decision crosses an FFI boundary into Lean-compiled C, and nobody knew whether
//! that cost microseconds or seconds. This example answers that with numbers.
//!
//! Run it:
//!
//! ```text
//! cd rust && cargo run --release --example bench_kernels
//! cd rust && cargo run          --example bench_kernels   # debug: the canonicality check is live
//! ```
//!
//! Deliberately dependency-free (`std::time::Instant`, no criterion, no
//! `Cargo.toml` edit) so it can be run from a clean checkout with nothing but a
//! Lean toolchain. Every figure it prints is a wall-clock mean over a stated
//! iteration count; nothing is extrapolated. When a size is too slow to measure
//! the harness says `STOPPED` and moves on rather than guessing.
//!
//! ## What the columns mean
//!
//! * `per-op` — total wall time / iterations, for one whole call.
//! * `×` — this row's `per-op` divided by the previous row's.
//! * `exp` — the implied scaling exponent, `log(t₂/t₁) / log(n₂/n₁)`. `1.0` is
//!   linear, `2.0` is quadratic. This is the evidence for every complexity claim
//!   in `docs/PERFORMANCE.md`; it is a two-point local slope, not a fit.
//!
//! ## The raw-shim section
//!
//! `crate::ffi` is private, so the encode / crossing / kernel / decode split is
//! obtained by declaring the three C shim entry points here directly (they are in
//! the same static archive `build.rs` links) and re-deriving the request bytes
//! with a **reconstruction** of `movelog.rs`'s encoder. The reconstruction is not
//! assumed faithful: it is checked against `Exec.requestCanonicalKernel` — the
//! proven canonical encoder — on every size, and the harness aborts if it ever
//! answers `false`. Since canonical encodings are unique, agreeing with the
//! canonical encoder is agreeing with `movelog.rs`, which asserts the same thing
//! in debug builds.

use std::io::Write;
use std::time::{Duration, Instant};

use uwueave::causal::{CausalWeave, NodeId};
use uwueave::era::{EraEvent, EraGroup};
use uwueave::movelog::{Grant, MoveLog, MoveOp};
use uwueave::seq::SeqCrdt;
use uwueave::weave::Weave;

// The C shim, borrowed directly for the cost split. Same symbols `src/ffi.rs`
// binds; the Lean runtime is initialized by the first library call we make in
// `main`, before any of these run.
extern "C" {
    fn shim_uweave_replay(input: *const u8, len: usize, out_len: *mut usize) -> *mut u8;
    fn shim_uweave_free(p: *mut u8);
    fn shim_uweave_request_canonical(input: *const u8, len: usize) -> u8;
    fn shim_uweave_seq(input: *const u8, len: usize, out_len: *mut usize) -> *mut u8;
}

const MAGIC_V3: u64 = 0x5557_4541_5645_0003;

// ---------------------------------------------------------------------------
// Timing
// ---------------------------------------------------------------------------

/// Stop growing a series once one iteration costs more than this. Prevents a
/// quadratic kernel from turning a benchmark run into an afternoon.
const WALL: Duration = Duration::from_secs(10);
/// Target wall time per data point; iterations stop as soon as it is reached.
const BUDGET: Duration = Duration::from_millis(120);
const MAX_ITERS: u64 = 2_000_000;

struct Sample {
    secs: f64,
    iters: u64,
}

fn bench(mut f: impl FnMut()) -> Sample {
    // One warm-up iteration, untimed: the first call to any kernel path can pay
    // for lazily-initialized Lean closures.
    f();
    let start = Instant::now();
    let mut iters = 0u64;
    loop {
        f();
        iters += 1;
        let elapsed = start.elapsed();
        if elapsed >= BUDGET || iters >= MAX_ITERS {
            return Sample { secs: elapsed.as_secs_f64() / iters as f64, iters };
        }
    }
}

fn fmt_time(s: f64) -> String {
    if s < 1e-6 {
        format!("{:>9.1} ns", s * 1e9)
    } else if s < 1e-3 {
        format!("{:>9.2} us", s * 1e6)
    } else if s < 1.0 {
        format!("{:>9.2} ms", s * 1e3)
    } else {
        format!("{:>9.3} s ", s)
    }
}

/// A table that accumulates (size, time) pairs so it can print the ratio and
/// the implied exponent between consecutive rows.
struct Table {
    prev: Option<(f64, f64)>,
}

impl Table {
    fn new(title: &str, size_label: &str) -> Self {
        println!("\n  {title}");
        println!(
            "    {:>10}  {:>12}  {:>10}  {:>6}  {:>5}",
            size_label, "per-op", "iters", "x", "exp"
        );
        Table { prev: None }
    }

    fn row(&mut self, size: f64, s: &Sample) {
        let (ratio, exp) = match self.prev {
            None => ("     -".to_string(), "    -".to_string()),
            Some((psize, psecs)) => {
                let r = s.secs / psecs;
                let e = if size > psize && psize > 0.0 && psecs > 0.0 {
                    (s.secs / psecs).ln() / (size / psize).ln()
                } else {
                    f64::NAN
                };
                (format!("{r:>6.2}"), if e.is_finite() { format!("{e:>5.2}") } else { "    -".into() })
            }
        };
        println!(
            "    {:>10}  {}  {:>10}  {}  {}",
            fmt_size(size),
            fmt_time(s.secs),
            s.iters,
            ratio,
            exp
        );
        std::io::stdout().flush().ok();
        self.prev = Some((size, s.secs));
    }

    fn stopped(&self, size: f64, why: &str) {
        println!(
            "    {:>10}  {:>12}  {:>10}  {:>6}  {:>5}   ({why})",
            fmt_size(size),
            "STOPPED",
            "-",
            "-",
            "-"
        );
        std::io::stdout().flush().ok();
    }
}

fn fmt_size(n: f64) -> String {
    if n.fract() == 0.0 {
        format!("{}", n as u64)
    } else {
        format!("{n}")
    }
}

// ---------------------------------------------------------------------------
// Workload construction
// ---------------------------------------------------------------------------

/// A structural chain: node *i* has node *i-1* as its only parent. The deepest
/// possible base, so `Exec.chainHits` walks the longest possible ancestor chain.
fn chain_weave(n: usize) -> (CausalWeave<Vec<u8>>, Vec<NodeId>) {
    let mut w = CausalWeave::new();
    let mut ids = Vec::with_capacity(n);
    let mut parent: Vec<NodeId> = vec![];
    for i in 0..n {
        let id = w.insert(parent.clone(), (i as u64).to_le_bytes().to_vec()).unwrap();
        ids.push(id);
        parent = vec![id];
    }
    (w, ids)
}

/// A flat weave: `n` roots, no structure at all. Shallowest possible base.
fn flat_weave(n: usize) -> (CausalWeave<Vec<u8>>, Vec<NodeId>) {
    let mut w = CausalWeave::new();
    let mut ids = Vec::with_capacity(n);
    for i in 0..n {
        ids.push(w.insert(vec![], (i as u64).to_le_bytes().to_vec()).unwrap());
    }
    (w, ids)
}

/// `m` deterministic move ops over `ids`, all citing grant 1. Distinct lamports,
/// so replay order is lamport order and no two ops collide in the log's `BTreeSet`.
fn move_ops(ids: &[NodeId], m: usize) -> Vec<MoveOp> {
    move_ops_citing(ids, m, 1)
}

fn move_ops_citing(ids: &[NodeId], m: usize, cite: u64) -> Vec<MoveOp> {
    let n = ids.len();
    (0..m)
        .map(|i| MoveOp {
            lamport: i as u64 + 1,
            replica: 0,
            child: ids[(i * 7 + 3) % n],
            dest: Some(ids[(i * 13 + 1) % n]),
            cite,
        })
        .collect()
}

fn log_of(ops: &[MoveOp], grants: usize) -> MoveLog {
    let mut log = MoveLog::new();
    for g in 1..=grants.max(1) {
        log.issue(Grant::universal(g as u64));
    }
    for op in ops {
        log.record(*op);
    }
    log
}

/// A reconstruction of `movelog.rs`'s request encoder, used only to price the
/// encode step. Checked against the proven canonical encoder before use.
fn encode_request(
    weave: &CausalWeave<Vec<u8>>,
    ops: &[MoveOp],
    grants: &[Grant],
    revs: &[u64],
) -> Vec<u8> {
    use std::collections::BTreeMap;
    let ids: Vec<NodeId> = weave.nodes().map(|n| n.id()).collect();
    let index: BTreeMap<NodeId, u64> =
        ids.iter().enumerate().map(|(i, id)| (*id, i as u64)).collect();
    let n = ids.len();

    let mut sorted: Vec<MoveOp> = ops.to_vec();
    sorted.sort();
    sorted.dedup();

    let mut words: Vec<u64> =
        Vec::with_capacity(5 + n + sorted.len() * 5 + grants.len() * 3 + revs.len());
    words.push(MAGIC_V3);
    words.push(n as u64);
    let mut encoded: Vec<[u64; 5]> = Vec::with_capacity(sorted.len());
    for op in &sorted {
        let child = match index.get(&op.child) {
            Some(c) => *c,
            None => continue,
        };
        let dest = match op.dest {
            None => -1i64,
            Some(d) => match index.get(&d) {
                Some(i) => *i as i64,
                None => continue,
            },
        };
        encoded.push([op.lamport, op.replica, child, dest as u64, op.cite]);
    }
    words.push(encoded.len() as u64);
    words.push(grants.len() as u64);
    words.push(revs.len() as u64);
    for id in &ids {
        let node = weave.get(id).unwrap();
        let fp: i64 = match node.parents().first() {
            None => -1,
            Some(p) => *index.get(p).unwrap() as i64,
        };
        words.push(fp as u64);
    }
    for op in &encoded {
        words.extend_from_slice(op);
    }
    for g in grants {
        words.extend_from_slice(&[g.id, g.parent, g.scope]);
    }
    for r in revs {
        words.push(*r);
    }
    words.iter().flat_map(|w| w.to_le_bytes()).collect()
}

fn raw_replay(bytes: &[u8]) -> usize {
    let mut out_len = 0usize;
    unsafe {
        let p = shim_uweave_replay(bytes.as_ptr(), bytes.len(), &mut out_len);
        shim_uweave_free(p);
    }
    out_len
}

fn raw_canonical(bytes: &[u8]) -> bool {
    unsafe { shim_uweave_request_canonical(bytes.as_ptr(), bytes.len()) == 1 }
}

fn raw_seq(bytes: &[u8]) -> usize {
    let mut out_len = 0usize;
    unsafe {
        let p = shim_uweave_seq(bytes.as_ptr(), bytes.len(), &mut out_len);
        shim_uweave_free(p);
    }
    out_len
}

/// A sequence CRDT of `n` elements, each anchored to the previous one — what
/// sequential typing produces.
fn seq_chain(n: usize) -> SeqCrdt {
    let mut s = SeqCrdt::new();
    let mut anchor = None;
    for i in 0..n {
        let id = s.insert(anchor, &(i as u64).to_le_bytes()).unwrap();
        anchor = Some(id);
    }
    s
}

/// A sequence CRDT of `n` elements all anchored at the document head — what
/// repeated head-insertion produces, and the widest possible sibling run.
fn seq_flat(n: usize) -> SeqCrdt {
    let mut s = SeqCrdt::new();
    for i in 0..n {
        s.insert(None, &(i as u64).to_le_bytes()).unwrap();
    }
    s
}

fn seq_ids(s: &SeqCrdt) -> Vec<NodeId> {
    s.visible()
}

/// `ne` ERA events: `users` joins, then writes cycling through them. All
/// authorised, so the arbitration does real work rather than short-circuiting.
fn era_group(ne: usize, users: u64, nc: usize) -> EraGroup {
    let mut g = EraGroup::new();
    let users = users.max(1);
    for u in 0..users {
        if (u as usize) < ne {
            g.record(EraEvent::join(u + 1, u + 1)).unwrap();
        }
    }
    for i in (users as usize)..ne {
        let u = (i as u64) % users + 1;
        // Promote/demote alternating keeps every event authorised-or-refused by
        // the real rule rather than by a trivially-unauthorised actor.
        g.record(EraEvent::write(i as u64 + 1, u)).unwrap();
    }
    for i in 0..nc.min(ne) {
        g.record_cut(1, i as u64 + 1);
    }
    g
}

/// `era_group`'s event set, recorded backwards. `Era.resolve_same_sets` makes
/// this the *same* resolution; the benchmark checks that the compiled merge
/// sort has also removed arrival-order sensitivity from the cost.
fn era_group_reversed(ne: usize, users: u64) -> EraGroup {
    let forward = era_group(ne, users, 0);
    let mut evs: Vec<EraEvent> = Vec::with_capacity(ne);
    let users = users.max(1);
    for u in 0..users {
        if (u as usize) < ne {
            evs.push(EraEvent::join(u + 1, u + 1));
        }
    }
    for i in (users as usize)..ne {
        evs.push(EraEvent::write(i as u64 + 1, (i as u64) % users + 1));
    }
    let mut g = EraGroup::new();
    for ev in evs.iter().rev() {
        g.record(*ev).unwrap();
    }
    assert_eq!(g.events_len(), forward.events_len());
    g
}

/// One admin churning one target's role forever: every event is authorised and
/// every authorised promote/demote adds a layer to `Era.GroupView.role`.
fn era_churn(ne: usize) -> EraGroup {
    use uwueave::era::EraRole;
    let mut g = EraGroup::new();
    g.record(EraEvent::join(1, 1)).unwrap();
    for i in 2..=ne.max(1) {
        let eid = i as u64;
        let ev = if i % 2 == 0 {
            EraEvent::promote(eid, 1, 2, EraRole::Writer)
        } else {
            EraEvent::demote(eid, 1, 2, EraRole::Reader)
        };
        g.record(ev).unwrap();
    }
    g
}

// ---------------------------------------------------------------------------
// Sections
// ---------------------------------------------------------------------------

fn section(name: &str) {
    println!("\n{}", "=".repeat(74));
    println!("{name}");
    println!("{}", "=".repeat(74));
    std::io::stdout().flush().ok();
}

fn bench_replay(max: usize) {
    section("1. MOVE REPLAY  (MoveLog::replay -> Exec.gatedReplayFull)");

    {
        let mut t = Table::new(
            "1a. log and weave grow together (chain base, n nodes / n ops / 1 grant)",
            "n = m",
        );
        for &n in &[10usize, 100, 1000, 3000, 10000] {
            if n > max {
                t.stopped(n as f64, "over BENCH_MAX");
                break;
            }
            let (w, ids) = chain_weave(n);
            let log = log_of(&move_ops(&ids, n), 1);
            let one = Instant::now();
            let _ = log.replay(&w);
            if one.elapsed() > WALL {
                t.row(n as f64, &Sample { secs: one.elapsed().as_secs_f64(), iters: 1 });
                println!("      (single iteration only: over the {WALL:?} wall)");
                break;
            }
            let s = bench(|| {
                let _ = log.replay(&w);
            });
            t.row(n as f64, &s);
        }
    }

    {
        let mut t = Table::new("1b. weave fixed at 1000 nodes (chain), ops grow", "m ops");
        let (w, ids) = chain_weave(1000);
        for &m in &[0usize, 10, 100, 1000, 10000] {
            let log = log_of(&move_ops(&ids, m), 1);
            let one = Instant::now();
            let _ = log.replay(&w);
            if one.elapsed() > WALL {
                t.stopped(m as f64, "over the wall");
                break;
            }
            let s = bench(|| {
                let _ = log.replay(&w);
            });
            t.row(m.max(1) as f64, &s);
        }
    }

    {
        // The control for 1b. `Exec.chainHits` walks the effective-parent chain
        // from the destination; on a chain base that walk is O(depth), on a flat
        // base it terminates at once. Same n, same m, same everything else — so
        // the difference between this table and 1b IS the ancestor walk.
        let mut t = Table::new("1b'. weave fixed at 1000 nodes (FLAT base), ops grow", "m ops");
        let (w, ids) = flat_weave(1000);
        for &m in &[0usize, 10, 100, 1000, 10000] {
            let log = log_of(&move_ops(&ids, m), 1);
            let one = Instant::now();
            let _ = log.replay(&w);
            if one.elapsed() > WALL {
                t.stopped(m as f64, "over the wall");
                break;
            }
            let s = bench(|| {
                let _ = log.replay(&w);
            });
            t.row(m.max(1) as f64, &s);
        }
    }

    {
        let mut t = Table::new("1c. ops fixed at 100, weave grows (chain base)", "n nodes");
        for &n in &[100usize, 1000, 3000, 10000, 30000] {
            if n > max {
                t.stopped(n as f64, "over BENCH_MAX");
                break;
            }
            let (w, ids) = chain_weave(n);
            let log = log_of(&move_ops(&ids, 100), 1);
            let one = Instant::now();
            let _ = log.replay(&w);
            if one.elapsed() > WALL {
                t.row(n as f64, &Sample { secs: one.elapsed().as_secs_f64(), iters: 1 });
                println!("      (single iteration only: over the {WALL:?} wall)");
                break;
            }
            let s = bench(|| {
                let _ = log.replay(&w);
            });
            t.row(n as f64, &s);
        }
    }

    {
        let mut t = Table::new("1d. ops fixed at 100, weave grows (FLAT base, depth 1)", "n nodes");
        for &n in &[100usize, 1000, 3000, 10000, 30000] {
            if n > max {
                t.stopped(n as f64, "over BENCH_MAX");
                break;
            }
            let (w, ids) = flat_weave(n);
            let log = log_of(&move_ops(&ids, 100), 1);
            let s = bench(|| {
                let _ = log.replay(&w);
            });
            t.row(n as f64, &s);
        }
    }

    {
        // ⚠ Every op here cites grant 1, and grants go on the wire in ascending
        // id order, so `Exec.findGrant`'s `Array.find?` hits at index 0 and its
        // O(ng) scan is never paid. What this table measures is the grant
        // block's WIRE COST. 1e' below is the one that measures the scan.
        let mut t = Table::new(
            "1e. grant substrate grows (100-node flat weave, 1000 ops, citing grant 1 = FIRST)",
            "ng grants",
        );
        let (w, ids) = flat_weave(100);
        let ops = move_ops(&ids, 1000);
        for &ng in &[1usize, 10, 100, 1000, 10000] {
            let log = log_of(&ops, ng);
            let one = Instant::now();
            let _ = log.replay(&w);
            if one.elapsed() > WALL {
                t.row(ng as f64, &Sample { secs: one.elapsed().as_secs_f64(), iters: 1 });
                println!("      (single iteration only: over the {WALL:?} wall)");
                break;
            }
            let s = bench(|| {
                let _ = log.replay(&w);
            });
            t.row(ng as f64, &s);
        }
    }

    {
        // Same workload and wire size, ops citing the LAST grant. F7's balanced
        // index should erase position sensitivity; the pair of tables checks
        // that claim while retaining index-construction cost in both.
        let mut t = Table::new(
            "1e'. the same, ops citing grant ng = LAST (indexed position check)",
            "ng grants",
        );
        let (w, ids) = flat_weave(100);
        for &ng in &[1usize, 10, 100, 1000, 10000] {
            let ops = move_ops_citing(&ids, 1000, ng as u64);
            let log = log_of(&ops, ng);
            let one = Instant::now();
            let _ = log.replay(&w);
            if one.elapsed() > WALL {
                t.row(ng as f64, &Sample { secs: one.elapsed().as_secs_f64(), iters: 1 });
                println!("      (single iteration only: over the {WALL:?} wall)");
                break;
            }
            let s = bench(|| {
                let _ = log.replay(&w);
            });
            t.row(ng as f64, &s);
        }
    }
}

fn bench_split() {
    section("2. WHERE THE REPLAY TIME GOES  (encode / crossing+kernel / decode)");
    println!(
        "\n  Rows: total = MoveLog::replay; kernel = the raw shim call on the SAME bytes;\n  \
         encode = a checked reconstruction of movelog.rs's marshaller; decode = the\n  \
         remainder (total - encode - kernel), which is the response walk plus the\n  \
         status/log stitch. canonical = Exec.requestCanonicalKernel on the same bytes,\n  \
         i.e. exactly what a DEBUG build adds to every single replay."
    );
    println!(
        "\n    {:>7} {:>7}  {:>12} {:>12} {:>12} {:>12} {:>12}",
        "n", "m", "total", "encode", "kernel", "decode", "canonical"
    );
    for &(n, m) in &[(100usize, 0usize), (100, 100), (1000, 0), (1000, 1000), (3000, 3000), (10000, 1000)]
    {
        let (w, ids) = chain_weave(n);
        let ops = move_ops(&ids, m);
        let log = log_of(&ops, 1);
        let grants = [Grant::universal(1)];
        let bytes = encode_request(&w, &ops, &grants, &[]);
        assert!(
            raw_canonical(&bytes),
            "the encoder reconstruction is NOT the canonical encoding at n={n} m={m}; \
             the split below would be measuring the wrong bytes"
        );
        let out_words = raw_replay(&bytes) / 8;
        assert_eq!(out_words, n + m, "raw kernel response is not n + m words");

        let total = bench(|| {
            let _ = log.replay(&w);
        });
        let enc = bench(|| {
            let b = encode_request(&w, &ops, &grants, &[]);
            std::hint::black_box(&b);
        });
        let ker = bench(|| {
            let l = raw_replay(&bytes);
            std::hint::black_box(l);
        });
        let can = bench(|| {
            let b = raw_canonical(&bytes);
            std::hint::black_box(b);
        });
        let dec = (total.secs - enc.secs - ker.secs).max(0.0);
        println!(
            "    {n:>7} {m:>7}  {} {} {} {} {}",
            fmt_time(total.secs),
            fmt_time(enc.secs),
            fmt_time(ker.secs),
            fmt_time(dec),
            fmt_time(can.secs)
        );
        // `requestCanonicalKernel` is decode-everything + encode-everything +
        // memcmp, with NO decision layer at all: it is a direct reading of the
        // Lean-side wire codec's throughput, in nanoseconds per 64-bit word.
        let req_words = (bytes.len() / 8) as f64;
        println!(
            "    {:>7} {:>7}  {:>12} {:>11.0}% {:>11.0}% {:>11.0}% {:>11.0}%   codec: {:.0} ns/word ({:.1} MB/s)",
            "",
            "",
            "share",
            100.0 * enc.secs / total.secs,
            100.0 * ker.secs / total.secs,
            100.0 * dec / total.secs,
            100.0 * can.secs / total.secs,
            1e9 * can.secs / (2.0 * req_words),
            (2.0 * req_words * 8.0) / can.secs / 1e6,
        );
        std::io::stdout().flush().ok();
    }

    println!("\n  The fixed cost of one crossing, measured on the smallest legal request:");
    let (w, ids) = chain_weave(1);
    let ops: Vec<MoveOp> = Vec::new();
    let _ = &ids;
    let grants = [Grant::universal(1)];
    let bytes = encode_request(&w, &ops, &grants, &[]);
    assert!(raw_canonical(&bytes));
    let s = bench(|| {
        let l = raw_replay(&bytes);
        std::hint::black_box(l);
    });
    println!(
        "    n=1, m=0, 1 grant ({} request bytes): {}  ({} iters)",
        bytes.len(),
        fmt_time(s.secs),
        s.iters
    );
    let log = log_of(&ops, 1);
    let s2 = bench(|| {
        let _ = log.replay(&w);
    });
    println!("    the same through MoveLog::replay:      {}  ({} iters)", fmt_time(s2.secs), s2.iters);
}

fn bench_seq(max: usize) {
    section("3. SEQUENCE LINEARIZATION  (SeqCrdt::visible / text -> SeqKernel.linearizeK)");

    {
        let mut t = Table::new(
            "3a. visible() on a CHAIN document (sequential typing: each element anchored to the last)",
            "n elems",
        );
        for &n in &[10usize, 100, 500, 1000, 2000, 5000, 10000] {
            if n > max {
                t.stopped(n as f64, "over BENCH_MAX");
                break;
            }
            let s = seq_chain(n);
            let one = Instant::now();
            let _ = s.visible();
            let single = one.elapsed();
            if single > WALL {
                t.row(n as f64, &Sample { secs: single.as_secs_f64(), iters: 1 });
                println!("      (single iteration only: over the {WALL:?} wall)");
                break;
            }
            let sm = bench(|| {
                let _ = s.visible();
            });
            t.row(n as f64, &sm);
        }
    }

    {
        let mut t = Table::new("3b. text() on the same CHAIN document (visible + contents splice)", "n elems");
        for &n in &[10usize, 100, 500, 1000, 2000, 5000] {
            if n > max {
                t.stopped(n as f64, "over BENCH_MAX");
                break;
            }
            let s = seq_chain(n);
            let one = Instant::now();
            let _ = s.text();
            if one.elapsed() > WALL {
                t.row(n as f64, &Sample { secs: one.elapsed().as_secs_f64(), iters: 1 });
                break;
            }
            let sm = bench(|| {
                let _ = s.text();
            });
            t.row(n as f64, &sm);
        }
    }

    {
        let mut t = Table::new(
            "3c. visible() with HALF the document tombstoned (deleted elements stay anchorable)",
            "n elems",
        );
        for &n in &[10usize, 100, 500, 1000, 2000, 5000] {
            if n > max {
                t.stopped(n as f64, "over BENCH_MAX");
                break;
            }
            let mut s = seq_chain(n);
            let ids = seq_ids(&s);
            for (i, id) in ids.iter().enumerate() {
                if i % 2 == 0 {
                    s.delete(id).unwrap();
                }
            }
            let one = Instant::now();
            let _ = s.visible();
            if one.elapsed() > WALL {
                t.row(n as f64, &Sample { secs: one.elapsed().as_secs_f64(), iters: 1 });
                break;
            }
            let sm = bench(|| {
                let _ = s.visible();
            });
            t.row(n as f64, &sm);
        }
    }

    {
        let mut t = Table::new(
            "3d. visible() on a FLAT document (every element anchored at the head: one wide run)",
            "n elems",
        );
        for &n in &[10usize, 100, 500, 1000, 2000, 5000] {
            if n > max {
                t.stopped(n as f64, "over BENCH_MAX");
                break;
            }
            let s = seq_flat(n);
            let one = Instant::now();
            let _ = s.visible();
            if one.elapsed() > WALL {
                t.row(n as f64, &Sample { secs: one.elapsed().as_secs_f64(), iters: 1 });
                break;
            }
            let sm = bench(|| {
                let _ = s.visible();
            });
            t.row(n as f64, &sm);
        }
    }

    {
        println!("\n  3e. the split, on a chain document: kernel vs the Rust glue around it");
        println!(
            "    {:>8}  {:>12} {:>12} {:>12}",
            "n", "visible()", "raw kernel", "glue"
        );
        for &n in &[100usize, 1000, 5000] {
            if n > max {
                continue;
            }
            let s = seq_chain(n);
            // Reconstruct the exact request `seq.rs` sends: one count word, n
            // anchor-index words, n tombstone words, indices in id (= BTreeMap
            // key) order. `seq_chain` anchors element k to element k-1, so the
            // anchor indices can be recovered by sorting the elements on their
            // contents and reading off adjacent pairs. The reconstruction is
            // checked below: the kernel must linearize all n elements from it.
            let ids: Vec<NodeId> = {
                let mut v: Vec<NodeId> = s.visible();
                v.sort();
                v
            };
            let mut words: Vec<u64> = Vec::with_capacity(1 + 2 * n);
            words.push(ids.len() as u64);
            let mut by_contents: Vec<(u64, NodeId)> = ids
                .iter()
                .map(|id| {
                    let c = s.contents(id).unwrap();
                    (u64::from_le_bytes(c.try_into().unwrap()), *id)
                })
                .collect();
            by_contents.sort();
            let pos_of: std::collections::BTreeMap<NodeId, usize> =
                ids.iter().enumerate().map(|(i, id)| (*id, i)).collect();
            let mut anchor_idx = vec![-1i64; ids.len()];
            for w in by_contents.windows(2) {
                let (_, prev) = w[0];
                let (_, cur) = w[1];
                anchor_idx[pos_of[&cur]] = pos_of[&prev] as i64;
            }
            for a in &anchor_idx {
                words.push(*a as u64);
            }
            for _ in 0..ids.len() {
                words.push(0);
            }
            let bytes: Vec<u8> = words.iter().flat_map(|w| w.to_le_bytes()).collect();
            let out = raw_seq(&bytes);
            assert_eq!(out / 8, 1 + n, "reconstructed seq request did not linearize all {n}");
            let tot = bench(|| {
                let _ = s.visible();
            });
            let ker = bench(|| {
                let l = raw_seq(&bytes);
                std::hint::black_box(l);
            });
            println!(
                "    {n:>8}  {} {} {}",
                fmt_time(tot.secs),
                fmt_time(ker.secs),
                fmt_time((tot.secs - ker.secs).max(0.0))
            );
            std::io::stdout().flush().ok();
        }
    }
}

fn bench_era(max: usize) {
    section("4. ERA RESOLVE  (EraGroup::resolve -> Era.resolve)");

    {
        let mut t = Table::new("4a. events grow, no arbiter cuts (everything pending)", "ne events");
        for &ne in &[10usize, 100, 500, 1000, 2000, 5000] {
            if ne > max {
                t.stopped(ne as f64, "over BENCH_MAX");
                break;
            }
            let g = era_group(ne, 8, 0);
            let one = Instant::now();
            let _ = g.resolve();
            if one.elapsed() > WALL {
                t.row(ne as f64, &Sample { secs: one.elapsed().as_secs_f64(), iters: 1 });
                println!("      (single iteration only: over the {WALL:?} wall)");
                break;
            }
            let s = bench(|| {
                let _ = g.resolve();
            });
            t.row(ne as f64, &s);
        }
    }

    {
        let mut t = Table::new("4b. events and cuts grow together (every event finalized)", "ne = nc");
        for &ne in &[10usize, 100, 500, 1000, 2000] {
            if ne > max {
                t.stopped(ne as f64, "over BENCH_MAX");
                break;
            }
            let g = era_group(ne, 8, ne);
            let one = Instant::now();
            let _ = g.resolve();
            if one.elapsed() > WALL {
                t.row(ne as f64, &Sample { secs: one.elapsed().as_secs_f64(), iters: 1 });
                println!("      (single iteration only: over the {WALL:?} wall)");
                break;
            }
            let s = bench(|| {
                let _ = g.resolve();
            });
            t.row(ne as f64, &s);
        }
    }

    {
        let mut t = Table::new("4c. events fixed at 200, cuts grow", "nc cuts");
        for &nc in &[0usize, 10, 50, 100, 200] {
            let g = era_group(200, 8, nc);
            let s = bench(|| {
                let _ = g.resolve();
            });
            t.row(nc.max(1) as f64, &s);
        }
    }

    {
        let mut t = Table::new("4d. events fixed at 500, distinct users grow (roster width)", "users");
        for &u in &[2u64, 8, 32, 128, 500] {
            let g = era_group(500, u, 0);
            let s = bench(|| {
                let _ = g.resolve();
            });
            t.row(u as f64, &s);
        }
    }

    {
        // 4a's events are joins and writes. Promotes and demotes stress role
        // updates; F3's compiled path carries them in a balanced index rather
        // than deepening the proof-facing closure chain.
        let mut t = Table::new(
            "4e. an all-authorised PROMOTE/DEMOTE stream (indexed role churn)",
            "ne events",
        );
        for &ne in &[10usize, 100, 500, 1000, 2000] {
            if ne > max {
                t.stopped(ne as f64, "over BENCH_MAX");
                break;
            }
            let g = era_churn(ne);
            let one = Instant::now();
            let _ = g.resolve();
            if one.elapsed() > WALL {
                t.row(ne as f64, &Sample { secs: one.elapsed().as_secs_f64(), iters: 1 });
                println!("      (single iteration only: over the {WALL:?} wall)");
                break;
            }
            let s = bench(|| {
                let _ = g.resolve();
            });
            t.row(ne as f64, &s);
        }
    }

    {
        // Same event SET as 4a, delivered backwards. `Era.resolve_same_sets`
        // says the answer cannot notice; F2's merge-sort path should keep the
        // cost in the same band too.
        let mut t = Table::new(
            "4f. 4a's event SET delivered in REVERSE arrival order (same answer and cost check)",
            "ne events",
        );
        for &ne in &[10usize, 100, 500, 1000, 2000] {
            if ne > max {
                t.stopped(ne as f64, "over BENCH_MAX");
                break;
            }
            let g = era_group_reversed(ne, 8);
            let one = Instant::now();
            let _ = g.resolve();
            if one.elapsed() > WALL {
                t.row(ne as f64, &Sample { secs: one.elapsed().as_secs_f64(), iters: 1 });
                println!("      (single iteration only: over the {WALL:?} wall)");
                break;
            }
            let s = bench(|| {
                let _ = g.resolve();
            });
            t.row(ne as f64, &s);
        }
        // The answers really are the same object, which is the point of the pair.
        let fwd = era_group(200, 8, 0).resolve();
        let rev = era_group_reversed(200, 8).resolve();
        println!(
            "      (checked: forward and reverse delivery resolve identically = {})",
            fwd == rev
        );
    }
}

fn bench_merge(max: usize) {
    section("5. MERGE  (CausalWeave::merge, Weave::merge) and 6. THE COMPOSITE VIEW");

    {
        let mut t = Table::new("5a. CausalWeave::merge, two disjoint flat weaves of n each", "n nodes");
        for &n in &[10usize, 100, 1000, 10000, 50000] {
            if n > max * 5 {
                t.stopped(n as f64, "over BENCH_MAX");
                break;
            }
            let (a, _) = flat_weave(n);
            let mut b = CausalWeave::new();
            for i in 0..n {
                b.insert(vec![], (i as u64 + 1_000_000).to_le_bytes().to_vec()).unwrap();
            }
            let s = bench(|| {
                let mut left = a.clone();
                left.merge(&b).unwrap();
            });
            t.row(n as f64, &s);
        }
        println!("      (each iteration includes one CausalWeave::clone of the left side)");
    }

    {
        let mut t = Table::new("5b. SeqCrdt::merge, two chain documents of n each", "n elems");
        for &n in &[10usize, 100, 1000, 5000] {
            if n > max {
                t.stopped(n as f64, "over BENCH_MAX");
                break;
            }
            let a = seq_chain(n);
            let b = a.clone();
            let s = bench(|| {
                let mut left = a.clone();
                left.merge(&b).unwrap();
            });
            t.row(n as f64, &s);
        }
        println!("      (identical documents: the all-already-present path, plus one clone)");
    }

    {
        let mut t = Table::new(
            "5c. Weave::merge, composite documents of n nodes each (no kernel calls inside)",
            "n nodes",
        );
        for &n in &[10usize, 100, 1000, 5000] {
            if n > max {
                t.stopped(n as f64, "over BENCH_MAX");
                break;
            }
            let a = build_weave(n, 0, 1);
            let mut b = build_weave(0, 0, 1);
            for i in 0..n {
                b.add_node(1, vec![], (i as u64 + 5_000_000).to_le_bytes().to_vec()).unwrap();
            }
            let one = Instant::now();
            {
                let mut left = a.clone();
                left.merge(&b).unwrap();
            }
            if one.elapsed() > WALL {
                t.row(n as f64, &Sample { secs: one.elapsed().as_secs_f64(), iters: 1 });
                break;
            }
            let s = bench(|| {
                let mut left = a.clone();
                left.merge(&b).unwrap();
            });
            t.row(n as f64, &s);
        }
        println!("      (Weave::merge clones itself first, to refuse wholesale rather than half-apply)");
    }

    {
        let mut t = Table::new(
            "5d. Weave::add_node — ONE user-visible write; note what it costs per call",
            "existing n",
        );
        for &n in &[10usize, 100, 1000, 5000] {
            if n > max {
                t.stopped(n as f64, "over BENCH_MAX");
                break;
            }
            let w = build_weave(n, 0, 1);
            let mut k = 0u64;
            let s = bench(|| {
                let mut ww = w.clone();
                k += 1;
                ww.add_node(1, vec![], (k + 9_000_000).to_le_bytes().to_vec()).unwrap();
            });
            t.row(n as f64, &s);
        }
        println!("      (includes the Weave::clone the harness does to keep each call a fresh insert)");
    }

    {
        let mut t = Table::new(
            "5e. Weave::add_node with the MEMBERSHIP LOG grown (weave fixed at 100 nodes)",
            "ne events",
        );
        for &ne in &[1usize, 10, 100, 500, 1000] {
            let w = build_weave(100, 0, ne);
            let mut k = 0u64;
            let one = Instant::now();
            {
                let mut ww = w.clone();
                ww.add_node(1, vec![], 42u64.to_le_bytes().to_vec()).unwrap();
            }
            if one.elapsed() > WALL {
                t.stopped(ne as f64, "over the wall");
                break;
            }
            let s = bench(|| {
                let mut ww = w.clone();
                k += 1;
                ww.add_node(1, vec![], (k + 7_000_000).to_le_bytes().to_vec()).unwrap();
            });
            t.row(ne as f64, &s);
        }
    }

    {
        let mut t = Table::new(
            "6a. Weave::view() — the whole UI read: ERA resolve + move replay + DFS",
            "n nodes",
        );
        for &n in &[10usize, 100, 1000, 3000] {
            if n > max {
                t.stopped(n as f64, "over BENCH_MAX");
                break;
            }
            let w = build_weave(n, n / 10, 1);
            let one = Instant::now();
            let _ = w.view();
            if one.elapsed() > WALL {
                t.row(n as f64, &Sample { secs: one.elapsed().as_secs_f64(), iters: 1 });
                println!("      (single iteration only: over the {WALL:?} wall)");
                break;
            }
            let s = bench(|| {
                let _ = w.view();
            });
            t.row(n as f64, &s);
        }
        println!("      (n/10 move ops in the log; no node carries text)");
    }

    {
        let mut t = Table::new(
            "6b. Weave::view() with TEXT — 32 nodes, each carrying a chain document of L elements",
            "L per node",
        );
        for &l in &[1usize, 10, 50, 100, 200] {
            let mut w = build_weave(32, 0, 1);
            let node_ids: Vec<NodeId> = w.nodes().nodes().map(|n| n.id()).collect();
            for id in &node_ids {
                let mut anchor = None;
                for i in 0..l {
                    anchor = Some(w.insert_text(1, *id, anchor, &(i as u64).to_le_bytes()).unwrap());
                }
            }
            let one = Instant::now();
            let _ = w.view();
            if one.elapsed() > WALL {
                t.row(l as f64, &Sample { secs: one.elapsed().as_secs_f64(), iters: 1 });
                println!("      (single iteration only: over the {WALL:?} wall)");
                break;
            }
            let s = bench(|| {
                let _ = w.view();
            });
            t.row(l as f64, &s);
        }
        println!("      (one SeqKernel crossing per node with text, every view)");
    }
}

/// A `Weave` with `n` flat nodes, `m` move ops, and `ne` membership events.
fn build_weave(n: usize, m: usize, ne: usize) -> Weave<Vec<u8>> {
    let mut w = Weave::new([(1u64, 1u64 << 40)]);
    w.record_membership(EraEvent::join(1, 1)).unwrap();
    for i in 1..ne {
        w.record_membership(EraEvent::write(i as u64 + 1, 1)).unwrap();
    }
    let mut ids = Vec::with_capacity(n);
    for i in 0..n {
        ids.push(w.add_node(1, vec![], (i as u64).to_le_bytes().to_vec()).unwrap());
    }
    for i in 0..m {
        let child = ids[(i * 7 + 3) % n.max(1)];
        let dest = ids[(i * 13 + 1) % n.max(1)];
        if child != dest {
            w.move_node(1, i as u64 + 1, child, Some(dest)).unwrap();
        }
    }
    w
}

// ---------------------------------------------------------------------------

fn main() {
    let max: usize = std::env::var("BENCH_MAX").ok().and_then(|s| s.parse().ok()).unwrap_or(30000);

    // First library call: initializes the Lean runtime, so the raw shim calls
    // below never race the `Once`.
    let init = Instant::now();
    let (w0, _) = chain_weave(1);
    let l0 = log_of(&[], 1);
    let _ = l0.replay(&w0);
    let init = init.elapsed();

    println!("{}", "#".repeat(74));
    println!("# uwueave kernel benchmarks");
    println!("#");
    println!("#   profile          : {}", if cfg!(debug_assertions) { "DEBUG (debug_assertions ON: the canonicality differential runs on every replay)" } else { "RELEASE (debug_assertions off: no canonicality differential)" });
    println!("#   target           : {} / {}", std::env::consts::ARCH, std::env::consts::OS);
    println!("#   BENCH_MAX        : {max}");
    println!("#   per-point budget : {BUDGET:?}, wall per iteration: {WALL:?}");
    println!("#   Lean runtime init + first kernel call: {}", fmt_time(init.as_secs_f64()));
    println!("#");
    println!("#   Reproduce: cd rust && cargo run --release --example bench_kernels");
    println!("{}", "#".repeat(74));
    std::io::stdout().flush().ok();

    bench_replay(max);
    bench_split();
    bench_seq(max);
    bench_era(max);
    bench_merge(max);

    println!("\ndone.");
}
