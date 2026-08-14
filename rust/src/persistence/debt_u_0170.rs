//! Immutable private-unit evidence for U-0170's deterministic I/O paths.
//!
//! These deliberately constructed Unix descriptors exercise the production
//! `RawJournal` state machine. They do not model a crash, power loss, stable
//! storage, or the filesystem-prefix premise retained as U-0168.

use super::*;
use std::os::fd::OwnedFd;
use std::os::unix::net::UnixStream;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_TEMP: AtomicU64 = AtomicU64::new(0);

fn test_spec() -> RecordSpec {
    RecordSpec {
        marker: *b"UWTEST01",
        hash_domain: b"uwueave.test.debt-u-0170.v1",
    }
}

fn options(sync: SyncPolicy) -> JournalOptions {
    JournalOptions {
        torn_tail: TornTailPolicy::Refuse,
        sync,
        max_record_bytes: 1024,
    }
}

#[test]
fn debt_closure_u_0170_fault_paths() {
    let nonce = NEXT_TEMP.fetch_add(1, Ordering::Relaxed);

    // Open failure cannot create a target through a non-directory sentinel.
    let root = std::env::temp_dir().join(format!(
        "uwueave-debt-u-0170-open-{}-{nonce}",
        std::process::id()
    ));
    let _ = std::fs::remove_dir_all(&root);
    std::fs::create_dir(&root).unwrap();
    let non_directory = root.join("not-a-directory");
    std::fs::write(&non_directory, b"unchanged sentinel").unwrap();
    assert!(matches!(
        RawJournal::open(
            non_directory.join("journal"),
            test_spec(),
            options(SyncPolicy::Buffered)
        ),
        Err(RawJournalError::Io(_))
    ));
    assert_eq!(
        std::fs::read(&non_directory).unwrap(),
        b"unchanged sentinel"
    );
    assert_eq!(std::fs::read_dir(&root).unwrap().count(), 1);
    std::fs::remove_file(non_directory).unwrap();
    std::fs::remove_dir(root).unwrap();

    // A deterministic write refusal poisons without committing memory/state.
    let write_path = std::env::temp_dir().join(format!(
        "uwueave-debt-u-0170-write-{}-{nonce}.journal",
        std::process::id()
    ));
    let _ = std::fs::remove_file(&write_path);
    let mut write_journal =
        RawJournal::open(&write_path, test_spec(), options(SyncPolicy::Buffered)).unwrap();
    write_journal.file = File::open("/dev/null").unwrap();
    assert!(matches!(
        write_journal.append_at(0, b"must not commit"),
        Err(RawJournalError::Io(_))
    ));
    assert!(write_journal.poisoned);
    assert!(write_journal.records().is_empty());
    assert_eq!(write_journal.next_sequence(), 0);
    assert!(matches!(
        write_journal.append_at(0, b"must not commit"),
        Err(RawJournalError::Poisoned)
    ));
    assert_eq!(std::fs::metadata(&write_path).unwrap().len(), 0);
    drop(write_journal);
    std::fs::remove_file(write_path).unwrap();

    // A retry sync refusal preserves the exact prior record and requires a
    // fresh production reopen before sequence progress resumes.
    let sync_path = std::env::temp_dir().join(format!(
        "uwueave-debt-u-0170-sync-{}-{nonce}.journal",
        std::process::id()
    ));
    let _ = std::fs::remove_file(&sync_path);
    let mut sync_journal =
        RawJournal::open(&sync_path, test_spec(), options(SyncPolicy::Buffered)).unwrap();
    sync_journal.append_at(0, b"accepted").unwrap();
    let (socket, _peer) = UnixStream::pair().unwrap();
    let socket_fd: OwnedFd = socket.into();
    sync_journal.file = File::from(socket_fd);
    sync_journal.options.sync = SyncPolicy::SyncData;
    assert!(matches!(
        sync_journal.append_at(0, b"accepted"),
        Err(RawJournalError::Io(_))
    ));
    assert!(sync_journal.poisoned);
    assert_eq!(sync_journal.records(), &[b"accepted".to_vec()]);
    assert_eq!(sync_journal.next_sequence(), 1);
    assert!(matches!(
        sync_journal.append_at(0, b"accepted"),
        Err(RawJournalError::Poisoned)
    ));
    drop(sync_journal);

    let mut reopened =
        RawJournal::open(&sync_path, test_spec(), options(SyncPolicy::Buffered)).unwrap();
    assert!(!reopened.poisoned);
    assert_eq!(reopened.records(), &[b"accepted".to_vec()]);
    assert_eq!(reopened.next_sequence(), 1);
    reopened.append_at(1, b"after reopen").unwrap();
    assert_eq!(
        reopened.records(),
        &[b"accepted".to_vec(), b"after reopen".to_vec()]
    );
    drop(reopened);
    std::fs::remove_file(sync_path).unwrap();
}
