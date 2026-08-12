use std::fs;
use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};

use uwueave::persistence::{
    decode_artifact_frame_stream, encode_artifact_frame_stream, AppendStatus, ArtifactFrame,
    ArtifactFrameError, ArtifactJournal, ArtifactJournalError, DocumentJournal,
    DocumentJournalError, DocumentReplay, JournalOptions, SyncPolicy, TornTailPolicy,
    MAX_ARTIFACT_FRAME_BYTES,
};
use uwueave::{Grant, MoveLog, MoveOp};

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

fn options(torn_tail: TornTailPolicy, sync: SyncPolicy) -> JournalOptions {
    JournalOptions {
        torn_tail,
        sync,
        ..JournalOptions::default()
    }
}

/// Canonical empty artifacts emitted by Lean's v2 codec, varying only the
/// unary-encoded declaration id. This fixture was generated from
/// `ArtifactDurable.projectionBytes`; the production API validates it by
/// calling the Lean decoder rather than reproducing that decoder in Rust.
fn artifact_frame(declaration_id: u8) -> ArtifactFrame {
    assert!(declaration_id <= 2, "fixture only pins ids 0, 1, and 2");
    let mut bytes = vec![213, 74, 2, 161];
    let mut payload = vec![1; declaration_id as usize];
    payload.push(0); // declaration id terminator
    payload.extend_from_slice(&[0; 8]); // two declaration Nats + six empty lists
    for byte in payload {
        bytes.extend_from_slice(&[0, byte]);
    }
    bytes.push(1);
    ArtifactFrame::new(bytes).expect("well-framed v2 fixture")
}

#[test]
fn logical_artifact_stream_is_exact_and_refuses_wrong_tags_and_trailing_torn_frame() {
    let first = artifact_frame(0);
    let second = artifact_frame(1);
    let stream = encode_artifact_frame_stream([&first, &second]);
    assert_eq!(
        decode_artifact_frame_stream(&stream).unwrap(),
        vec![first.clone(), second.clone()]
    );
    assert_eq!(
        ArtifactFrame::new(vec![213, 74, 2, 161, 1]),
        Err(ArtifactFrameError::NonCanonicalPayload),
        "well-framed but noncanonical payload is refused by Lean"
    );
    assert_eq!(
        encode_artifact_frame_stream(decode_artifact_frame_stream(&stream).unwrap().iter()),
        stream
    );

    let mut wrong_version = first.as_bytes().to_vec();
    wrong_version[2] = 1;
    assert_eq!(
        ArtifactFrame::new(wrong_version),
        Err(ArtifactFrameError::WrongVersion { actual: 1 })
    );
    let mut wrong_domain = first.as_bytes().to_vec();
    wrong_domain[3] = 162;
    assert_eq!(
        ArtifactFrame::new(wrong_domain),
        Err(ArtifactFrameError::WrongDomain { actual: 162 })
    );
    let mut corrupt_tag = first.as_bytes().to_vec();
    corrupt_tag[4] = 7;
    assert_eq!(
        ArtifactFrame::new(corrupt_tag),
        Err(ArtifactFrameError::UnknownBodyTag {
            offset: 4,
            actual: 7
        })
    );

    let mut torn = stream;
    torn.extend_from_slice(&second.as_bytes()[..3]);
    let error = decode_artifact_frame_stream(&torn).unwrap_err();
    assert_eq!(
        error.offset,
        first.as_bytes().len() + second.as_bytes().len()
    );
    assert_eq!(error.source, ArtifactFrameError::Torn);
}

#[test]
fn oversized_artifact_refuses_before_lean_validation() {
    let bytes = vec![0; MAX_ARTIFACT_FRAME_BYTES + 1];
    assert_eq!(
        ArtifactFrame::new(bytes),
        Err(ArtifactFrameError::TooLarge {
            actual: MAX_ARTIFACT_FRAME_BYTES + 1,
            maximum: MAX_ARTIFACT_FRAME_BYTES,
        })
    );
}

#[test]
fn artifact_physical_journal_reopens_with_exact_frames_and_all_sync_policies() {
    for sync in [
        SyncPolicy::Buffered,
        SyncPolicy::Flush,
        SyncPolicy::SyncData,
        SyncPolicy::SyncAll,
    ] {
        let temp = TempFile::new("artifact-reopen");
        let first = artifact_frame(0);
        let second = artifact_frame(1);
        {
            let mut journal =
                ArtifactJournal::open(&temp.0, options(TornTailPolicy::Refuse, sync)).unwrap();
            assert!(journal.open_report().created);
            assert_eq!(journal.append(first.clone()).unwrap().sequence, 0);
            assert_eq!(journal.append(second.clone()).unwrap().sequence, 1);
        }
        let reopened = ArtifactJournal::open(
            &temp.0,
            options(TornTailPolicy::Refuse, SyncPolicy::Buffered),
        )
        .unwrap();
        assert_eq!(reopened.frames(), &[first, second]);
        assert_eq!(reopened.next_sequence(), 2);
        assert!(!reopened.open_report().created);
    }
}

#[test]
fn every_physical_final_record_truncation_recovers_only_the_complete_prefix() {
    let temp = TempFile::new("artifact-all-tears");
    let first = artifact_frame(0);
    let second = artifact_frame(1);
    let third = artifact_frame(2);
    let prefix_len;
    {
        let mut journal = ArtifactJournal::open(
            &temp.0,
            options(TornTailPolicy::Refuse, SyncPolicy::Buffered),
        )
        .unwrap();
        journal.append(first.clone()).unwrap();
        journal.append(second.clone()).unwrap();
        prefix_len = fs::metadata(&temp.0).unwrap().len() as usize;
        journal.append(third).unwrap();
    }
    let complete = fs::read(&temp.0).unwrap();
    let third_record_len = complete.len() - prefix_len;

    for cut in 0..third_record_len {
        fs::write(&temp.0, &complete[..prefix_len + cut]).unwrap();
        if cut == 0 {
            let journal = ArtifactJournal::open(
                &temp.0,
                options(TornTailPolicy::Truncate, SyncPolicy::Buffered),
            )
            .unwrap();
            assert_eq!(journal.frames(), &[first.clone(), second.clone()]);
            assert_eq!(journal.open_report().truncated_bytes, 0);
            drop(journal);
        } else {
            let refused = ArtifactJournal::open(
                &temp.0,
                options(TornTailPolicy::Refuse, SyncPolicy::Buffered),
            )
            .unwrap_err();
            assert!(matches!(
                refused,
                ArtifactJournalError::TornTail { bytes, .. } if bytes == cut as u64
            ));
            let journal = ArtifactJournal::open(
                &temp.0,
                options(TornTailPolicy::Truncate, SyncPolicy::Buffered),
            )
            .unwrap();
            assert_eq!(journal.frames(), &[first.clone(), second.clone()]);
            assert_eq!(journal.open_report().truncated_bytes, cut as u64);
            drop(journal);
            assert_eq!(fs::metadata(&temp.0).unwrap().len() as usize, prefix_len);
        }
    }
}

#[test]
fn physical_checksum_refuses_payload_corruption_and_never_skips_a_corrupt_middle() {
    let temp = TempFile::new("artifact-corrupt-middle");
    let first = artifact_frame(0);
    let second = artifact_frame(1);
    {
        let mut journal = ArtifactJournal::open(
            &temp.0,
            options(TornTailPolicy::Refuse, SyncPolicy::Buffered),
        )
        .unwrap();
        journal.append(first.clone()).unwrap();
        journal.append(second).unwrap();
    }
    let mut bytes = fs::read(&temp.0).unwrap();
    let body_offset = bytes
        .windows(first.as_bytes().len())
        .position(|window| window == first.as_bytes())
        .expect("physical record contains unchanged exact frame");
    bytes[body_offset + 5] ^= 0x40;
    fs::write(&temp.0, bytes).unwrap();

    let error = ArtifactJournal::open(
        &temp.0,
        options(TornTailPolicy::Truncate, SyncPolicy::Buffered),
    )
    .unwrap_err();
    assert!(matches!(
        error,
        ArtifactJournalError::CorruptPhysical { sequence: 0, .. }
    ));
}

#[test]
fn truncated_checksum_prefixes_are_torn_only_when_every_present_byte_matches() {
    let temp = TempFile::new("artifact-checksum-prefix");
    let frame = artifact_frame(0);
    let complete = physical_artifact_record(0, frame.as_bytes());
    let header_checksum_start = 24;
    let body_checksum_start = 56 + frame.as_bytes().len();

    for checksum_start in [header_checksum_start, body_checksum_start] {
        for prefix_len in 1..=32 {
            let end = checksum_start + prefix_len;
            let mut corrupt_prefix = complete[..end].to_vec();
            corrupt_prefix[end - 1] ^= 0x80;
            fs::write(&temp.0, corrupt_prefix).unwrap();
            assert!(matches!(
                ArtifactJournal::open(
                    &temp.0,
                    options(TornTailPolicy::Truncate, SyncPolicy::Buffered)
                ),
                Err(ArtifactJournalError::CorruptPhysical { sequence: 0, .. })
            ));
        }
    }
}

#[test]
fn artifact_sequence_retries_are_idempotent_and_gaps_or_conflicts_refuse() {
    let temp = TempFile::new("artifact-sequence");
    let first = artifact_frame(0);
    let other = artifact_frame(1);
    let mut journal = ArtifactJournal::open(
        &temp.0,
        options(TornTailPolicy::Refuse, SyncPolicy::Buffered),
    )
    .unwrap();
    assert_eq!(
        journal.append_at(0, first.clone()).unwrap().status,
        AppendStatus::Appended
    );
    assert_eq!(
        journal.append_at(0, first).unwrap().status,
        AppendStatus::AlreadyPresent
    );
    assert!(matches!(
        journal.append_at(0, other.clone()),
        Err(ArtifactJournalError::SequenceConflict { sequence: 0 })
    ));
    assert!(matches!(
        journal.append_at(2, other),
        Err(ArtifactJournalError::SequenceGap {
            expected: 1,
            requested: 2
        })
    ));
}

#[test]
fn journal_lock_and_record_allocation_bound_are_enforced() {
    let temp = TempFile::new("artifact-lock-bound");
    let journal = ArtifactJournal::open(
        &temp.0,
        options(TornTailPolicy::Refuse, SyncPolicy::Buffered),
    )
    .unwrap();
    assert!(matches!(
        ArtifactJournal::open(
            &temp.0,
            options(TornTailPolicy::Refuse, SyncPolicy::Buffered)
        ),
        Err(ArtifactJournalError::Locked)
    ));
    drop(journal);

    let mut bounded = ArtifactJournal::open(
        &temp.0,
        JournalOptions {
            max_record_bytes: 22,
            ..options(TornTailPolicy::Refuse, SyncPolicy::Buffered)
        },
    )
    .unwrap();
    assert!(matches!(
        bounded.append(artifact_frame(0)),
        Err(ArtifactJournalError::RecordTooLarge {
            actual: 23,
            maximum: 22
        })
    ));
}

fn move_op(lamport: u64, child: u8, dest: Option<u8>, cite: u64) -> MoveOp {
    MoveOp {
        lamport,
        replica: 7,
        child: [child; 32],
        dest: dest.map(|byte| [byte; 32]),
        cite,
    }
}

#[test]
fn document_journal_reconstructs_typed_movelog_and_checkpoint_prefix() {
    let temp = TempFile::new("document-replay");
    let grant = Grant::universal(1);
    let op = move_op(10, 1, Some(2), 1);
    {
        let mut journal = DocumentJournal::open(
            &temp.0,
            options(TornTailPolicy::Refuse, SyncPolicy::SyncData),
        )
        .unwrap();
        journal.append_grant(grant).unwrap();
        journal.append_move(op).unwrap();
        journal.append_checkpoint().unwrap();
        journal.append_revocation(1).unwrap();
        assert_eq!(journal.next_sequence(), 4);
    }

    let reopened = DocumentJournal::open(
        &temp.0,
        options(TornTailPolicy::Refuse, SyncPolicy::Buffered),
    )
    .unwrap();
    let mut expected = MoveLog::new();
    expected.issue(grant);
    expected.record(op);
    expected.revoke(1);
    assert_eq!(reopened.recovered_move_log(), &expected);
    assert_eq!(reopened.entries().len(), 4);

    #[derive(Default)]
    struct Consumer(MoveLog);
    impl DocumentReplay for Consumer {
        type Error = ();

        fn restore_move_log(&mut self, checkpoint: &MoveLog) -> Result<(), Self::Error> {
            self.0 = checkpoint.clone();
            Ok(())
        }
        fn record_move(&mut self, op: MoveOp) -> Result<(), Self::Error> {
            self.0.record(op);
            Ok(())
        }
        fn issue_grant(&mut self, grant: Grant) -> Result<(), Self::Error> {
            self.0.issue(grant);
            Ok(())
        }
        fn revoke_grant(&mut self, grant_id: u64) -> Result<(), Self::Error> {
            self.0.revoke(grant_id);
            Ok(())
        }
    }
    let mut consumer = Consumer::default();
    reopened.replay_into(&mut consumer).unwrap();
    assert_eq!(consumer.0, expected);
}

#[test]
fn document_sequences_make_uncertain_retries_safe() {
    let temp = TempFile::new("document-sequence");
    let grant = Grant::root(4, 8);
    let mut journal = DocumentJournal::open(
        &temp.0,
        options(TornTailPolicy::Refuse, SyncPolicy::Buffered),
    )
    .unwrap();
    assert_eq!(
        journal.append_grant_at(0, grant).unwrap().status,
        AppendStatus::Appended
    );
    assert_eq!(
        journal.append_grant_at(0, grant).unwrap().status,
        AppendStatus::AlreadyPresent
    );
    assert!(matches!(
        journal.append_grant_at(0, Grant::root(4, 9)),
        Err(DocumentJournalError::SequenceConflict { sequence: 0 })
    ));
    assert!(matches!(
        journal.append_revocation_at(3, 4),
        Err(DocumentJournalError::SequenceGap {
            expected: 1,
            requested: 3
        })
    ));
}

#[test]
fn document_journal_does_not_mistake_physical_sequence_for_unique_grant_or_authentication() {
    let temp = TempFile::new("document-legacy-duplicate-grant");
    let mut journal = DocumentJournal::open(
        &temp.0,
        options(TornTailPolicy::Refuse, SyncPolicy::Buffered),
    )
    .unwrap();
    journal.append_grant(Grant::root(4, 8)).unwrap();
    journal.append_grant(Grant::root(4, 9)).unwrap();

    assert_eq!(journal.recovered_move_log().grants().count(), 2);
    assert_eq!(journal.next_sequence(), 2);
    // This is observable legacy behavior, not approval: physical sequences
    // do not establish Authority.UniqueGrant, issuer identity, or a v4 nonce.
}

#[test]
fn document_physical_corruption_refuses_and_a_torn_final_record_is_policy_controlled() {
    let temp = TempFile::new("document-corrupt-torn");
    let first_len;
    {
        let mut journal = DocumentJournal::open(
            &temp.0,
            options(TornTailPolicy::Refuse, SyncPolicy::Buffered),
        )
        .unwrap();
        journal.append_grant(Grant::universal(1)).unwrap();
        first_len = fs::metadata(&temp.0).unwrap().len() as usize;
        journal.append_move(move_op(1, 2, None, 1)).unwrap();
    }
    let complete = fs::read(&temp.0).unwrap();
    fs::write(&temp.0, &complete[..first_len + 10]).unwrap();
    assert!(matches!(
        DocumentJournal::open(
            &temp.0,
            options(TornTailPolicy::Refuse, SyncPolicy::Buffered)
        ),
        Err(DocumentJournalError::TornTail { bytes: 10, .. })
    ));
    let recovered = DocumentJournal::open(
        &temp.0,
        options(TornTailPolicy::Truncate, SyncPolicy::Buffered),
    )
    .unwrap();
    assert_eq!(recovered.entries().len(), 1);
    drop(recovered);

    // A complete, checksummed record with one corrupted body byte is not a
    // torn tail and is refused even under the truncating policy.
    fs::write(&temp.0, complete).unwrap();
    let mut corrupt = fs::read(&temp.0).unwrap();
    corrupt[56 + 1] ^= 0x80; // first physical body, after its typed tag
    fs::write(&temp.0, corrupt).unwrap();
    assert!(matches!(
        DocumentJournal::open(
            &temp.0,
            options(TornTailPolicy::Truncate, SyncPolicy::Buffered)
        ),
        Err(DocumentJournalError::CorruptPhysical { sequence: 0, .. })
    ));
}

fn physical_document_record(sequence: u64, body: &[u8]) -> Vec<u8> {
    physical_record(b"UWDJRN01", b"uwueave.document-journal.v1", sequence, body)
}

fn physical_artifact_record(sequence: u64, body: &[u8]) -> Vec<u8> {
    physical_record(b"UWARJ001", b"uwueave.artifact-journal.v1", sequence, body)
}

fn physical_record(marker: &[u8; 8], domain: &[u8], sequence: u64, body: &[u8]) -> Vec<u8> {
    let length = body.len() as u64;
    let mut header_hasher = blake3::Hasher::new();
    header_hasher.update(domain);
    header_hasher.update(b".header\0");
    header_hasher.update(marker);
    header_hasher.update(&sequence.to_le_bytes());
    header_hasher.update(&length.to_le_bytes());

    let mut body_hasher = blake3::Hasher::new();
    body_hasher.update(domain);
    body_hasher.update(b".body\0");
    body_hasher.update(marker);
    body_hasher.update(&sequence.to_le_bytes());
    body_hasher.update(&length.to_le_bytes());
    body_hasher.update(body);

    let mut record = Vec::new();
    record.extend_from_slice(marker);
    record.extend_from_slice(&sequence.to_le_bytes());
    record.extend_from_slice(&length.to_le_bytes());
    record.extend_from_slice(header_hasher.finalize().as_bytes());
    record.extend_from_slice(body);
    record.extend_from_slice(body_hasher.finalize().as_bytes());
    record
}

#[test]
fn reopened_artifact_physical_records_refuse_wrong_tags_and_noncanonical_payloads() {
    let temp = TempFile::new("artifact-invalid-inner");
    for (body, expected) in [
        (
            vec![213, 74, 1, 161, 1],
            ArtifactFrameError::WrongVersion { actual: 1 },
        ),
        (
            vec![213, 74, 2, 162, 1],
            ArtifactFrameError::WrongDomain { actual: 162 },
        ),
        (
            vec![213, 74, 2, 161, 1],
            ArtifactFrameError::NonCanonicalPayload,
        ),
    ] {
        fs::write(&temp.0, physical_artifact_record(0, &body)).unwrap();
        assert!(matches!(
            ArtifactJournal::open(
                &temp.0,
                options(TornTailPolicy::Truncate, SyncPolicy::Buffered)
            ),
            Err(ArtifactJournalError::CorruptFrame { sequence: 0, source })
                if source == expected
        ));
    }
}

#[test]
fn checksummed_but_invalid_typed_entry_is_not_mistaken_for_physical_corruption() {
    let temp = TempFile::new("document-invalid-entry");
    fs::write(&temp.0, physical_document_record(0, &[99])).unwrap();
    assert!(matches!(
        DocumentJournal::open(
            &temp.0,
            options(TornTailPolicy::Truncate, SyncPolicy::Buffered)
        ),
        Err(DocumentJournalError::CorruptEntry { sequence: 0, .. })
    ));
}

#[test]
fn checksummed_canonical_checkpoint_must_equal_the_preceding_mutation_prefix() {
    let temp = TempFile::new("document-invalid-checkpoint");

    // Canonical Grant(root 1, universal scope).
    let mut grant = vec![1];
    grant.extend_from_slice(&1u64.to_le_bytes());
    grant.extend_from_slice(&0u64.to_le_bytes());
    grant.extend_from_slice(&u64::MAX.to_le_bytes());

    // Canonical empty checkpoint claiming to cover the empty prefix. It is a
    // valid typed body in isolation, but false after the grant at sequence 0.
    let mut empty_checkpoint = vec![3, 0];
    empty_checkpoint.extend_from_slice(&0u64.to_le_bytes()); // op count
    empty_checkpoint.extend_from_slice(&0u64.to_le_bytes()); // grant count
    empty_checkpoint.extend_from_slice(&0u64.to_le_bytes()); // revocation count

    let mut bytes = physical_document_record(0, &grant);
    bytes.extend_from_slice(&physical_document_record(1, &empty_checkpoint));
    fs::write(&temp.0, bytes).unwrap();
    assert!(matches!(
        DocumentJournal::open(
            &temp.0,
            options(TornTailPolicy::Truncate, SyncPolicy::Buffered)
        ),
        Err(DocumentJournalError::InvalidCheckpoint { sequence: 1 })
    ));
}
