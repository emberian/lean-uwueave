//! Differential evidence for the boundary between Lean's canonical logical
//! artifact journal and Rust's checksummed `UWARJ001` outer records.
//!
//! The test constructs explicit complete and truncated byte images. It does
//! not claim that a filesystem or power loss can produce only those images.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use uwueave::persistence::{
    decode_artifact_frame_stream, encode_artifact_frame_stream, ArtifactJournal,
    ArtifactJournalError, JournalOptions, SyncPolicy, TornTailPolicy,
};

static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

struct TempFile(PathBuf);

impl TempFile {
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

impl Drop for TempFile {
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

fn options(torn_tail: TornTailPolicy) -> JournalOptions {
    JournalOptions {
        torn_tail,
        sync: SyncPolicy::Buffered,
        ..JournalOptions::default()
    }
}

fn lean_generated_corpus() -> Vec<u8> {
    let output = Command::new("lake")
        .args([
            "env",
            "lean",
            "--run",
            "tests/ArtifactJournalRefinementCorpus.lean",
        ])
        .current_dir(repo())
        .output()
        .expect("launch Lean-owned artifact journal corpus");
    assert!(
        output.status.success(),
        "Lean corpus failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stderr.is_empty(),
        "the binary corpus runner must be diagnostic-free: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    output.stdout
}

fn recovered_logical_bytes(journal: &ArtifactJournal) -> Vec<u8> {
    encode_artifact_frame_stream(journal.frames())
}

#[test]
fn lean_generated_outer_prefix_refines_durable_complete_journal() {
    let logical_corpus = lean_generated_corpus();
    let frames = decode_artifact_frame_stream(&logical_corpus)
        .expect("existing Lean validator admits every Lean-generated frame");
    assert_eq!(frames.len(), 3, "the refinement trace has three records");
    assert_eq!(
        encode_artifact_frame_stream(&frames),
        logical_corpus,
        "logical parsing retains every Lean-owned byte"
    );

    let first_two_logical_len = frames[0].as_bytes().len() + frames[1].as_bytes().len();
    let first_two_logical = &logical_corpus[..first_two_logical_len];
    let expected_first_two = frames[..2].to_vec();
    let temp = TempFile::new("artifact-refinement");

    let first_physical_len;
    let first_two_physical_len;
    {
        let mut journal = ArtifactJournal::open(&temp.0, options(TornTailPolicy::Refuse))
            .expect("create production artifact journal");
        journal.append(frames[0].clone()).unwrap();
        first_physical_len = fs::metadata(&temp.0).unwrap().len() as usize;
        journal.append(frames[1].clone()).unwrap();
        first_two_physical_len = fs::metadata(&temp.0).unwrap().len() as usize;
        journal.append(frames[2].clone()).unwrap();
    }

    let complete_image = fs::read(&temp.0).unwrap();
    let final_physical_len = complete_image.len() - first_two_physical_len;
    assert!(first_physical_len < first_two_physical_len);
    assert!(final_physical_len > 0);

    let complete = ArtifactJournal::open(&temp.0, options(TornTailPolicy::Refuse)).unwrap();
    assert_eq!(complete.frames(), frames);
    assert_eq!(recovered_logical_bytes(&complete), logical_corpus);
    drop(complete);

    // The empty prefix and every nonempty strict prefix of the final complete
    // outer record withhold its inner body. No partial logical frame reaches
    // the Lean validator or the recovered frame list.
    for cut in 0..final_physical_len {
        fs::write(&temp.0, &complete_image[..first_two_physical_len + cut]).unwrap();

        if cut > 0 {
            assert!(matches!(
                ArtifactJournal::open(&temp.0, options(TornTailPolicy::Refuse)),
                Err(ArtifactJournalError::TornTail { bytes, .. }) if bytes == cut as u64
            ));
        }

        let recovered = ArtifactJournal::open(&temp.0, options(TornTailPolicy::Truncate)).unwrap();
        assert_eq!(recovered.frames(), expected_first_two);
        assert_eq!(recovered.open_report().truncated_bytes, cut as u64);
        let logical_prefix = recovered_logical_bytes(&recovered);
        assert_eq!(logical_prefix, first_two_logical);
        assert_eq!(
            decode_artifact_frame_stream(&logical_prefix).unwrap(),
            expected_first_two,
            "every returned outer body remains accepted by the real Lean validator"
        );
        drop(recovered);
        assert_eq!(
            fs::metadata(&temp.0).unwrap().len() as usize,
            first_two_physical_len
        );
    }

    // A corrupt complete middle record is never treated as a disposable final
    // prefix and the valid third record after it is never skipped into view.
    let mut corrupt_middle = complete_image;
    let second_body_offset = first_physical_len + 56;
    assert_eq!(
        &corrupt_middle[second_body_offset..second_body_offset + frames[1].as_bytes().len()],
        frames[1].as_bytes()
    );
    corrupt_middle[second_body_offset + 5] ^= 0x40;
    fs::write(&temp.0, corrupt_middle).unwrap();
    assert!(matches!(
        ArtifactJournal::open(&temp.0, options(TornTailPolicy::Truncate)),
        Err(ArtifactJournalError::CorruptPhysical { sequence: 1, .. })
    ));
}
