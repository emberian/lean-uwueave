//! End-to-end scaling, crash-recovery, and adversarial tests for checkpointed
//! admission preflight, through the real runtime and on-disk journal.
//!
//! Wall-clock assertions live in one ignored benchmark:
//!
//! ```text
//! cargo test --release --test incremental_preflight -- --ignored --nocapture admission_latency
//! ```

#[path = "support/incremental_preflight.rs"]
mod harness;

use std::env;
use std::fs;
use std::path::PathBuf;
use std::time::Instant;

use harness::{
    admit_against_full_replay, adversarial_rows, authority_log, bounded_clock_rows, in_order_rows,
    move_op, new_runtime, node_ids, recover_runtime, signed_requests, weave, Row, TempJournal,
    MAX_BYTES,
};
use uwueave::auth_runtime::{AdmissionDisposition, AdmissionOutcome};
use uwueave::persistence::{RecoveryExpectation, TornTailPolicy};
use uwueave::MoveLog;

const MARKS: [usize; 3] = [100, 500, 2_000];
/// Include a full historical snapshot interval in each time window.
const WINDOW: usize = 64;

fn admit_all(runtime: &mut harness::Runtime, requests: &[Vec<u8>]) {
    for request in requests {
        match runtime.admit(MAX_BYTES, request) {
            AdmissionOutcome::Accepted(receipt) => {
                assert_eq!(receipt.disposition, AdmissionDisposition::Appended)
            }
            other => panic!("in-order admission failed: {other:?}"),
        }
    }
}

/// Check physical file growth and bound each replay exchange on both clock
/// schedules. Counts include the raw journal headers and packed certificates.
#[test]
fn persisted_bytes_and_replay_evidence_scale_linearly() {
    for rows in [bounded_clock_rows(MARKS[2]), in_order_rows(MARKS[2])] {
        let requests = signed_requests(&rows);
        let journal = TempJournal::new("linear-bytes");
        let mut runtime = new_runtime(&journal.0);
        let mut start = 0;
        let mut sizes = Vec::new();
        for mark in MARKS {
            admit_all(&mut runtime, &requests[start..mark]);
            sizes.push(fs::metadata(&journal.0).unwrap().len());
            start = mark;
        }
        for record in runtime.journal().records() {
            let trace = record.admission().trace();
            assert_eq!(&trace.format_v3_request()[16..24], &1u64.to_le_bytes());
        }
        println!("journal bytes at {MARKS:?}: {sizes:?}");
        assert!(sizes[1] <= 6 * sizes[0] && sizes[2] <= 22 * sizes[0]);
    }
}

fn bench_rounds() -> usize {
    env::var("UWUEAVE_BENCH_ROUNDS")
        .ok()
        .and_then(|rounds| rounds.parse().ok())
        .unwrap_or(5)
        .max(1)
}

/// Measure contiguous windows, including checkpoint creation, receipt drops
/// and buffered journal writes. Summarize complete window means across runs.
fn window_latencies(rows: &[Row]) -> ([f64; 3], [u64; 3]) {
    let requests = signed_requests(rows);
    let mut means: [Vec<f64>; 3] = Default::default();
    let mut bytes = [0; 3];
    for _ in 0..bench_rounds() {
        let journal = TempJournal::new("latency");
        let mut runtime = new_runtime(&journal.0);
        let mut start = 0;
        for (slot, mark) in MARKS.into_iter().enumerate() {
            admit_all(&mut runtime, &requests[start..mark - WINDOW]);
            let started = Instant::now();
            admit_all(&mut runtime, &requests[mark - WINDOW..mark]);
            means[slot].push(started.elapsed().as_secs_f64() * 1e6 / WINDOW as f64);
            bytes[slot] = fs::metadata(&journal.0).unwrap().len();
            start = mark;
        }
    }
    (
        means.map(|mut samples| {
            samples.sort_by(f64::total_cmp);
            samples[samples.len() / 2]
        }),
        bytes,
    )
}

#[test]
#[ignore = "wall-clock benchmark; run in release with --ignored --nocapture"]
fn admission_latency_scaling() {
    for (name, rows) in [
        ("slow clock", bounded_clock_rows(MARKS[2])),
        ("single writer", in_order_rows(MARKS[2])),
    ] {
        let (means, bytes) = window_latencies(&rows);
        let ratio = means[2] / means[0];
        println!(
            "{name} at {MARKS:?}: {means:.1?} µs/commit ({ratio:.2}x), {bytes:?} journal bytes"
        );
        assert!(bytes[2] <= 22 * bytes[0]);
        assert!(
            ratio < 2.0,
            "{name} admission grew {ratio:.2}x (target < 2x)"
        );
    }
}

/// Run `rows` through a runtime, crashing and recovering before each index in
/// `crashes`, and return the exact journal bytes and final log.
fn run_with_crashes(
    rows: &[Row],
    requests: &[Vec<u8>],
    crashes: &[usize],
    torn: bool,
) -> (Vec<u8>, MoveLog) {
    let weave = weave();
    let nodes = node_ids(&weave);
    let journal = TempJournal::new("crash");
    let mut runtime = new_runtime(&journal.0);
    let mut shadow = authority_log();
    for (position, (row, request)) in rows.iter().zip(requests).enumerate() {
        if crashes.contains(&position) {
            let pin = runtime.journal().recovery_expectation();
            drop(runtime);
            let policy = if torn {
                // A crash in the middle of the next append leaves a torn tail.
                use std::io::Write;
                let mut file = fs::OpenOptions::new()
                    .append(true)
                    .open(&journal.0)
                    .unwrap();
                file.write_all(b"UWAM").unwrap();
                TornTailPolicy::Truncate
            } else {
                TornTailPolicy::Refuse
            };
            runtime = recover_runtime(&journal.0, pin, policy);
            assert_eq!(
                runtime.execution().log(),
                &shadow,
                "recovered log differs before row {position}"
            );
        }
        admit_against_full_replay(
            &mut runtime,
            &mut shadow,
            &weave,
            move_op(&nodes, *row),
            request,
            &format!("row {position}"),
        );
    }
    assert_eq!(runtime.execution().log(), &shadow);
    assert_eq!(
        runtime.execution().log().replay(&weave),
        shadow.replay(&weave),
        "final view differs from full genesis replay"
    );
    let bytes = fs::read(&journal.0).unwrap();
    (bytes, shadow)
}

/// Every verdict on a hostile schedule equals full genesis replay, and a crash
/// at any point, including through a torn final append, reproduces the
/// uninterrupted journal bit for bit.
#[test]
fn crash_recovery_matches_full_genesis_replay_bit_for_bit() {
    let rows = adversarial_rows(300, 7);
    let requests = signed_requests(&rows);
    let (uninterrupted, final_log) = run_with_crashes(&rows, &requests, &[], false);
    assert!(
        final_log.len() > 128,
        "schedule must cross several checkpoints"
    );

    for crashes in [
        vec![1],
        vec![63, 64, 65],
        vec![128],
        vec![40, 97, 151, 233, 299],
    ] {
        let (bytes, log) = run_with_crashes(&rows, &requests, &crashes, false);
        assert_eq!(log, final_log, "crashes at {crashes:?}");
        assert!(
            bytes == uninterrupted,
            "journal bytes differ for crashes at {crashes:?}"
        );
    }
    let (bytes, _) = run_with_crashes(&rows, &requests, &[70, 190], true);
    assert!(
        bytes == uninterrupted,
        "journal bytes differ after torn appends"
    );
}

/// A retried request after recovery is the same durable admission, not a new
/// one, even when it landed before the newest checkpoint.
#[test]
fn verified_retry_across_recovery_appends_nothing() {
    let rows = in_order_rows(150);
    let requests = signed_requests(&rows);
    let journal = TempJournal::new("retry");
    let mut runtime = new_runtime(&journal.0);
    admit_all(&mut runtime, &requests);
    let pin = runtime.journal().recovery_expectation();
    drop(runtime);
    let before = fs::read(&journal.0).unwrap();

    let mut recovered = recover_runtime(&journal.0, pin, TornTailPolicy::Refuse);
    for sequence in [0usize, 63, 64, 149] {
        match recovered.admit(MAX_BYTES, &requests[sequence]) {
            AdmissionOutcome::Accepted(receipt) => {
                assert_eq!(receipt.disposition, AdmissionDisposition::Retry);
                assert_eq!(receipt.sequence, sequence as u64);
            }
            other => panic!("retry of {sequence} failed: {other:?}"),
        }
    }
    assert_eq!(recovered.journal().records().len(), 150);
    assert!(
        fs::read(&journal.0).unwrap() == before,
        "a retry changed the journal"
    );
}

fn cross_version_dir() -> PathBuf {
    PathBuf::from(env::var_os("UWUEAVE_CROSS_VERSION_DIR").expect("set UWUEAVE_CROSS_VERSION_DIR"))
}

/// Write a journal for [`cross_version_recover`] to read with a later build.
#[test]
#[ignore = "cross-version compatibility: run on the older build"]
fn cross_version_write() {
    let directory = cross_version_dir();
    let path = directory.join("journal.bin");
    fs::File::create_new(&path).expect("cross-version output needs a fresh journal path");
    let rows = in_order_rows(160);
    let requests = signed_requests(&rows);
    let mut runtime = new_runtime(&path);
    admit_all(&mut runtime, &requests);
    let pin = runtime.journal().recovery_expectation();
    let mut encoded = pin.last_sequence.expect("nonempty").to_le_bytes().to_vec();
    encoded.extend_from_slice(&pin.head_commitment.expect("nonempty"));
    fs::write(directory.join("pin.bin"), encoded).unwrap();
}

/// Recover a journal written by an older build and keep admitting on it.
#[test]
#[ignore = "cross-version compatibility: run on the newer build"]
fn cross_version_recover() {
    let directory = cross_version_dir();
    let path = directory.join("journal.bin");
    let encoded = fs::read(directory.join("pin.bin")).unwrap();
    let pin = RecoveryExpectation {
        last_sequence: Some(u64::from_le_bytes(encoded[..8].try_into().unwrap())),
        head_commitment: Some(encoded[8..40].try_into().unwrap()),
    };
    let rows = in_order_rows(240);
    let requests = signed_requests(&rows);
    let weave = weave();
    let nodes = node_ids(&weave);

    let mut runtime = recover_runtime(&path, pin, TornTailPolicy::Refuse);
    let legacy = fs::read(&path).unwrap();
    for sequence in [0, 63, 149] {
        let AdmissionOutcome::Accepted(retry) = runtime.admit(MAX_BYTES, &requests[sequence])
        else {
            panic!("legacy retry failed at {sequence}");
        };
        assert_eq!(retry.disposition, AdmissionDisposition::Retry);
        assert_eq!(retry.sequence, sequence as u64);
    }
    assert_eq!(fs::read(&path).unwrap(), legacy);
    let mut shadow = authority_log();
    rows[..160]
        .iter()
        .for_each(|row| shadow.record(move_op(&nodes, *row)));
    assert_eq!(runtime.execution().log(), &shadow);
    for (position, row) in rows.iter().enumerate().skip(160) {
        admit_against_full_replay(
            &mut runtime,
            &mut shadow,
            &weave,
            move_op(&nodes, *row),
            &requests[position],
            &format!("row {position}"),
        );
    }
    let pin = runtime.journal().recovery_expectation();
    drop(runtime);
    let recovered = recover_runtime(&path, pin, TornTailPolicy::Refuse);
    assert_eq!(recovered.journal().records().len(), 240);
    assert_eq!(
        recovered.execution().log().replay(&weave),
        shadow.replay(&weave)
    );
    println!("recovered 160 older records and appended 80 newer ones");
}
