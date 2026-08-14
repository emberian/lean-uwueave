//! End-to-end evidence that explicit Lean emission, Rust canonical admission,
//! and durable journal recovery preserve one real generated artifact byte for
//! byte. The test invokes the user-facing command; it does not reconstruct the
//! Preoscript payload in Rust.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use uwueave::persistence::{
    ArtifactFrame, ArtifactFrameError, ArtifactJournal, JournalOptions, SyncPolicy, TornTailPolicy,
};

const SEMANTIC_NAME: &str = "SemanticExport.ArtifactDurableBytes";
const SEMANTIC_BYTES: usize = 33_331;
const SEMANTIC_BLAKE3: &str = "c43397db99dc66b4264caa7a79b9c081d9ae42c73e2e70de7daf8a65b1804bbf";
const FULL_NAME: &str = "ProjectionV2.Examples.fullExport";
const FULL_BYTES: usize = 15_887;
const FULL_BLAKE3: &str = "14f7acf40b69cfecdd9ce64be22c05c82fc887f70125c2df89815560d43d81df";

static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

struct TempPath(PathBuf);

impl TempPath {
    fn new(label: &str, extension: &str) -> Self {
        let nonce = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "uwueave-{label}-{}-{nonce}.{extension}",
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

fn emitter() -> PathBuf {
    repo().join("tools/uwueave-preo-artifact")
}

fn emit_to_path(path: &Path) -> Vec<u8> {
    let output = Command::new(emitter())
        .args([SEMANTIC_NAME, "--output"])
        .arg(path)
        .current_dir(repo())
        .output()
        .expect("launch explicit Lean artifact emitter");
    assert!(
        output.status.success(),
        "artifact emitter failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stdout.is_empty(),
        "path mode must not mix an artifact with stdout diagnostics"
    );
    fs::read(path).expect("read explicitly emitted artifact path")
}

fn emit_to_stdout(name: &str) -> Vec<u8> {
    let output = Command::new(emitter())
        .args([name, "--stdout"])
        .current_dir(repo())
        .output()
        .expect("launch explicit Lean artifact emitter");
    assert!(
        output.status.success(),
        "artifact emitter failed:\nstderr:\n{}",
        String::from_utf8_lossy(&output.stderr)
    );
    output.stdout
}

#[test]
fn emitter_refusal_status_propagates_without_binary_stdout() {
    let output = Command::new(emitter())
        .args(["not-a-real-artifact", "--stdout"])
        .current_dir(repo())
        .output()
        .expect("launch explicit Lean artifact emitter");
    assert!(!output.status.success());
    assert!(
        output.stdout.is_empty(),
        "a refused artifact must not emit a binary-looking stdout prefix"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("unknown artifact"),
        "the exact Main refusal should propagate through the import-only runner"
    );
}

#[test]
fn real_export_bytes_survive_syncdata_reopen_and_refuse_damage() {
    let emitted_path = TempPath::new("semantic-export", "preo");
    let path_bytes = emit_to_path(&emitted_path.0);
    let stdout_bytes = emit_to_stdout(SEMANTIC_NAME);
    assert_eq!(
        stdout_bytes, path_bytes,
        "stdout and path modes must be exact"
    );
    assert!(
        !path_bytes.is_empty(),
        "the real export is not a marker fixture"
    );
    assert_eq!(path_bytes.len(), SEMANTIC_BYTES);
    assert_eq!(
        blake3::hash(&path_bytes).to_hex().as_str(),
        SEMANTIC_BLAKE3,
        "generated ArtifactDurableBytes changed; inspect the checked export and update intentionally"
    );
    let full_bytes = emit_to_stdout(FULL_NAME);
    assert_eq!(full_bytes.len(), FULL_BYTES);
    assert_eq!(
        blake3::hash(&full_bytes).to_hex().as_str(),
        FULL_BLAKE3,
        "fullExport bytes changed; inspect the checked export and update intentionally"
    );

    let frame = ArtifactFrame::new(path_bytes.clone())
        .expect("Lean's canonical validator admits Lean's actual emitted bytes");
    assert_eq!(frame.as_bytes(), path_bytes);
    let full_frame = ArtifactFrame::new(full_bytes.clone())
        .expect("Lean's canonical validator admits Lean's full example export");
    assert_eq!(full_frame.as_bytes(), full_bytes);

    let journal_path = TempPath::new("semantic-export", "journal");
    let syncdata = JournalOptions {
        torn_tail: TornTailPolicy::Refuse,
        sync: SyncPolicy::SyncData,
        ..JournalOptions::default()
    };
    {
        let mut journal = ArtifactJournal::open(&journal_path.0, syncdata).unwrap();
        let receipt = journal.append(frame.clone()).unwrap();
        assert_eq!(receipt.sequence, 0);
        let receipt = journal.append(full_frame.clone()).unwrap();
        assert_eq!(receipt.sequence, 1);
        journal.sync(SyncPolicy::SyncData).unwrap();
    }
    let reopened = ArtifactJournal::open(
        &journal_path.0,
        JournalOptions {
            torn_tail: TornTailPolicy::Refuse,
            sync: SyncPolicy::Buffered,
            ..JournalOptions::default()
        },
    )
    .unwrap();
    assert_eq!(reopened.frames(), &[frame, full_frame]);
    assert_eq!(reopened.frames()[0].as_bytes(), path_bytes);
    assert_eq!(reopened.frames()[1].as_bytes(), full_bytes);
    assert_eq!(
        blake3::hash(reopened.frames()[0].as_bytes())
            .to_hex()
            .as_str(),
        SEMANTIC_BLAKE3
    );
    assert_eq!(
        blake3::hash(reopened.frames()[1].as_bytes())
            .to_hex()
            .as_str(),
        FULL_BLAKE3
    );

    let mut semantic_mutation = path_bytes.clone();
    assert_eq!(semantic_mutation[4], 0, "first payload byte has a data tag");
    assert_eq!(semantic_mutation[5], 1, "declaration id starts canonically");
    semantic_mutation[5] = 2;
    assert_eq!(
        ArtifactFrame::new(semantic_mutation),
        Err(ArtifactFrameError::NonCanonicalPayload),
        "outer-valid mutation is refused by Lean's payload decoder"
    );

    assert_eq!(
        ArtifactFrame::new(path_bytes[..path_bytes.len() - 1].to_vec()),
        Err(ArtifactFrameError::Torn)
    );

    let mut wrong_version = path_bytes;
    wrong_version[2] = 1;
    assert_eq!(
        ArtifactFrame::new(wrong_version),
        Err(ArtifactFrameError::WrongVersion { actual: 1 })
    );
}
