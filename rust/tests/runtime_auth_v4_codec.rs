//! End-to-end canaries for the narrow Lean-owned UWV4 syntax checkpoint.

use std::path::{Path, PathBuf};
use std::process::Command;

use uwueave::auth::{
    decode_runtime_auth_v4_canonical, RuntimeAuthV4DecodeOutcome, RuntimeAuthV4DecodeRefusal,
};

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("rust crate is directly below repository root")
        .to_path_buf()
}

fn fixture() -> Vec<u8> {
    let output = Command::new("lake")
        .args([
            "env",
            "lean",
            "--run",
            "rust/tests/support/RuntimeAuthV4RequestFixture.lean",
        ])
        .current_dir(repo())
        .output()
        .expect("launch canonical UWV4 fixture emitter");
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

fn refused(input: &[u8], maximum: usize) -> RuntimeAuthV4DecodeRefusal {
    match decode_runtime_auth_v4_canonical(maximum, input) {
        RuntimeAuthV4DecodeOutcome::Refused(reason) => reason,
        RuntimeAuthV4DecodeOutcome::Accepted { .. } => panic!("request unexpectedly accepted"),
    }
}

#[test]
fn canonical_request_roundtrips_and_every_decode_refusal_is_distinct() {
    let bytes = fixture();
    assert_eq!(&bytes[..6], b"UWV4\x04\x01");

    assert_eq!(
        decode_runtime_auth_v4_canonical(bytes.len(), &bytes),
        RuntimeAuthV4DecodeOutcome::Accepted {
            canonical_request: bytes.clone(),
        }
    );
    assert_eq!(
        refused(&bytes, bytes.len() - 1),
        RuntimeAuthV4DecodeRefusal::TooLarge
    );

    let mut bad_magic = bytes.clone();
    bad_magic[0] ^= 1;
    assert_eq!(
        refused(&bad_magic, bad_magic.len()),
        RuntimeAuthV4DecodeRefusal::BadMagic
    );

    let mut old_version = bytes.clone();
    old_version[4] = 3;
    assert_eq!(
        refused(&old_version, old_version.len()),
        RuntimeAuthV4DecodeRefusal::UnsupportedVersion
    );

    let mut wrong_kind = bytes.clone();
    wrong_kind[5] = 2;
    assert_eq!(
        refused(&wrong_kind, wrong_kind.len()),
        RuntimeAuthV4DecodeRefusal::WrongKind
    );

    let truncated = &bytes[..bytes.len() - 1];
    assert_eq!(
        refused(truncated, truncated.len()),
        RuntimeAuthV4DecodeRefusal::Malformed
    );

    let mut trailing = bytes;
    trailing.push(0);
    assert_eq!(
        refused(&trailing, trailing.len()),
        RuntimeAuthV4DecodeRefusal::Malformed
    );
}
