//! Cross-boundary evidence for Lean-owned runtime-auth sidecar bytes in the
//! durable Rust arrival queue.
//!
//! The queue treats the sidecar as opaque payload. Preserving these bytes is
//! not signature verification, authorization, membership, or permission to
//! execute; the final assertion deliberately shows that storage also accepts
//! a mutated sidecar when the caller gives it a distinct event id.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use uwueave::persistence::{
    HistoryArrivalJournal, HistoryArrivalJournalError, HistoryDeliveryStatus, HistoryEvent,
    HistoryJournalError, JournalOptions, SyncPolicy, TornTailPolicy,
};

const FIXTURE_BYTES: usize = 369;
const FIXTURE_PREFIX: [u8; 4] = [213, 74, 4, 162];
const FIXTURE_BLAKE3: &str = "ca8928d7f1fabbe744a1417926a9cc400b2895369773012964fd5a351890b202";

static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

struct TempPath(PathBuf);

impl TempPath {
    fn new(label: &str) -> Self {
        let nonce = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "uwueave-{label}-{}-{nonce}.journal",
            std::process::id()
        ));
        let _ = fs::remove_file(&path);
        Self(path)
    }
}

impl Drop for TempPath {
    fn drop(&mut self) {
        let _ = fs::remove_file(&self.0);
    }
}

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("rust crate is directly below repository root")
        .to_path_buf()
}

fn emit_fixture() -> Vec<u8> {
    let output = Command::new("lake")
        .args([
            "env",
            "lean",
            "--run",
            "rust/tests/support/RuntimeAuthV4Fixture.lean",
        ])
        .current_dir(repo())
        .output()
        .expect("launch test-only Lean runtime-auth sidecar emitter");
    assert!(
        output.status.success(),
        "fixture emitter stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stderr.is_empty(),
        "fixture emitter must be byte-only"
    );
    output.stdout
}

fn event(id: u8, parents: &[u8], payload: Vec<u8>) -> HistoryEvent {
    HistoryEvent::new(
        [id; 32],
        parents.iter().map(|parent| [*parent; 32]).collect(),
        payload,
    )
    .expect("test event has a canonical parent set")
}

fn options() -> JournalOptions {
    JournalOptions {
        torn_tail: TornTailPolicy::Refuse,
        sync: SyncPolicy::SyncData,
        ..JournalOptions::default()
    }
}

#[test]
fn lean_v4_sidecar_survives_durable_pending_reopen_and_drain_as_opaque_bytes() {
    let fixture = emit_fixture();
    assert_eq!(fixture.len(), FIXTURE_BYTES);
    assert_eq!(fixture[..FIXTURE_PREFIX.len()], FIXTURE_PREFIX);
    assert_eq!(blake3::hash(&fixture).to_hex().as_str(), FIXTURE_BLAKE3);

    let root = event(1, &[], b"causal-root".to_vec());
    let child = event(2, &[1], fixture.clone());
    let path = TempPath::new("runtime-auth-arrival");
    let pending_digest;
    let pending_file;

    {
        let mut journal = HistoryArrivalJournal::open(&path.0, options(), 1).unwrap();
        let receipt = journal.receive(child.clone()).unwrap();
        assert_eq!(receipt.status, HistoryDeliveryStatus::Buffered);
        assert_eq!(receipt.arrival_sequence, 0);
        assert_eq!(
            journal.pending_event(&child.id()).unwrap().payload(),
            fixture
        );
        journal.append_checkpoint().unwrap();
        journal.sync(SyncPolicy::SyncData).unwrap();
        pending_digest = journal.state_digest();
        pending_file = fs::read(&path.0).unwrap();
    }

    {
        let mut reopened = HistoryArrivalJournal::open(&path.0, options(), 1).unwrap();
        let reopened_payload = reopened.pending_event(&child.id()).unwrap().payload();
        assert_eq!(reopened_payload, fixture);
        assert_eq!(
            blake3::hash(reopened_payload).to_hex().as_str(),
            FIXTURE_BLAKE3
        );
        assert_eq!(reopened.state_digest(), pending_digest);
        assert_eq!(fs::read(&path.0).unwrap(), pending_file);

        assert_eq!(
            reopened.receive(child.clone()).unwrap().status,
            HistoryDeliveryStatus::Retry
        );
        assert!(matches!(
            reopened.receive(event(2, &[1], b"same-id-forgery".to_vec())),
            Err(HistoryArrivalJournalError::Journal(
                HistoryJournalError::IdCollision { .. }
            ))
        ));
        assert!(matches!(
            reopened.receive(event(3, &[1], b"over-capacity".to_vec())),
            Err(HistoryArrivalJournalError::Journal(
                HistoryJournalError::BufferFull { capacity: 1 }
            ))
        ));
        assert_eq!(reopened.state_digest(), pending_digest);
        assert_eq!(fs::read(&path.0).unwrap(), pending_file);

        let receipt = reopened.receive(root.clone()).unwrap();
        assert_eq!(receipt.status, HistoryDeliveryStatus::Appended);
        assert_eq!(receipt.drained, 1);
        assert!(reopened.is_settled());
        assert_eq!(
            reopened.materialized_event(&child.id()).unwrap().payload(),
            fixture
        );
        reopened.sync(SyncPolicy::SyncData).unwrap();
    }

    let reopened = HistoryArrivalJournal::open(&path.0, options(), 1).unwrap();
    assert!(reopened.is_settled());
    assert_eq!(
        reopened.materialized_event(&child.id()).unwrap().payload(),
        fixture
    );

    let causal_path = TempPath::new("runtime-auth-causal");
    let mut causal = HistoryArrivalJournal::open(&causal_path.0, options(), 1).unwrap();
    causal.receive(root).unwrap();
    causal.receive(child).unwrap();
    assert!(causal.settled_same_event_set(&reopened));

    // The storage layer is intentionally not an authenticator or validator.
    let opaque_path = TempPath::new("runtime-auth-opaque-mutation");
    let mut opaque = HistoryArrivalJournal::open(&opaque_path.0, options(), 0).unwrap();
    let mut mutated = fixture;
    mutated[2] = 99;
    assert_eq!(
        opaque
            .receive(event(9, &[], mutated.clone()))
            .unwrap()
            .status,
        HistoryDeliveryStatus::Appended
    );
    assert_eq!(
        opaque.materialized_event(&[9; 32]).unwrap().payload(),
        mutated
    );
}
