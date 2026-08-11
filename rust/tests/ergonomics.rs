//! Public-surface checks for refusal rendering and receipt inspection.

use std::error::Error;

use uwueave::status::{HonestWidgetViolation, PendingSoundViolation, WidgetSoundViolation};
use uwueave::weave::{SeamError, WeaveMergeError, WeaveOpError};
use uwueave::{
    EraMergeError, EraRecordError, InsertError, MergeError, MoveLog, MoveOp, NodeIdDisplay,
    SeqDeleteError, SeqInsertError, SeqMergeError,
};

fn assert_public_error<E: Error + 'static>() {}

#[test]
fn every_public_refusal_type_is_a_standard_error() {
    assert_public_error::<InsertError>();
    assert_public_error::<MergeError>();
    assert_public_error::<SeqInsertError>();
    assert_public_error::<SeqDeleteError>();
    assert_public_error::<SeqMergeError>();
    assert_public_error::<EraRecordError>();
    assert_public_error::<EraMergeError>();
    assert_public_error::<SeamError>();
    assert_public_error::<WeaveOpError>();
    assert_public_error::<WeaveMergeError>();
    assert_public_error::<HonestWidgetViolation>();
    assert_public_error::<WidgetSoundViolation>();
    assert_public_error::<PendingSoundViolation>();
}

#[test]
fn node_ids_have_full_and_short_allocation_free_display() {
    let id = [0xabu8; 32];
    assert_eq!(NodeIdDisplay::new(&id).to_string(), "ab".repeat(32));
    assert_eq!(NodeIdDisplay::short(&id).to_string(), "ababab");
    assert_eq!(format!("{:?}", NodeIdDisplay::prefix(&id, 4)), "abababab");
}

#[test]
fn composite_refusals_render_context_and_preserve_sources() {
    let id = [0xabu8; 32];
    let error = WeaveOpError::Insert(InsertError::MissingParent(id));
    let rendered = error.to_string();
    assert!(rendered.starts_with("node insertion refused:"));
    assert!(rendered.contains(&"ab".repeat(32)));
    assert_eq!(
        error
            .source()
            .expect("wrapped refusal retains its source")
            .to_string(),
        format!("missing parent node {}", "ab".repeat(32))
    );

    let merge = WeaveMergeError::Text {
        node: id,
        source: SeqMergeError::NotAnchorClosed {
            element: [0xcdu8; 32],
            missing_anchor: [0xefu8; 32],
        },
    };
    assert!(merge.to_string().contains("text merge for node"));
    assert!(merge.source().is_some());
}

#[test]
fn move_log_ops_is_a_receipt_accessor_not_a_replay() {
    let first = MoveOp {
        lamport: 1,
        replica: 7,
        child: [1u8; 32],
        dest: None,
        cite: 0,
    };
    let second = MoveOp {
        lamport: 2,
        replica: 7,
        child: [2u8; 32],
        dest: Some([1u8; 32]),
        cite: 0,
    };
    let mut log = MoveLog::new();
    log.record(second);
    log.record(first);
    log.record(first);

    assert_eq!(log.ops().copied().collect::<Vec<_>>(), vec![first, second]);
    assert_eq!(log.len(), 2);
}
