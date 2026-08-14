//! Test-only launcher for Lean-owned context-bound UWV4 corpus bytes.
//!
//! This helper deliberately has no request encoder. A keyed test first asks
//! Lean for the exact signing bytes, computes a verifier-specific signature,
//! then asks Lean to place those opaque signature bytes in the canonical
//! request.

#![allow(dead_code)]

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_SIGNATURE_FILE: AtomicU64 = AtomicU64::new(0);

struct SignatureFile(PathBuf);

impl SignatureFile {
    fn write(bytes: &[u8]) -> Self {
        let nonce = NEXT_SIGNATURE_FILE.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "uwueave-auth-v4-signature-{}-{nonce}.bin",
            std::process::id()
        ));
        let _ = fs::remove_file(&path);
        fs::write(&path, bytes).expect("write test-only signature input");
        Self(path)
    }
}

impl Drop for SignatureFile {
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

fn emit(arguments: &[&str]) -> Vec<u8> {
    let output = Command::new("lake")
        .args([
            "env",
            "lean",
            "--run",
            "rust/tests/support/RuntimeAuthV4AdmissionCorpus.lean",
        ])
        .args(arguments)
        .current_dir(repo())
        .output()
        .expect("launch test-only Lean UWV4 admission corpus emitter");
    assert!(
        output.status.success(),
        "admission corpus emitter {:?} stderr: {}",
        arguments,
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(
        output.stderr.is_empty(),
        "admission corpus emitter must be byte-only"
    );
    output.stdout
}

/// Lean's exact kind-3 signing bytes for `case`.
pub fn signing_bytes(case: &str) -> Vec<u8> {
    emit(&["signing", case])
}

/// Lean's exact kind-3 request containing the supplied opaque signature.
pub fn request(case: &str, signature: &[u8]) -> Vec<u8> {
    let signature_file = SignatureFile::write(signature);
    let signature_path = signature_file
        .0
        .to_str()
        .expect("temporary signature path is UTF-8");
    emit(&["request", case, signature_path])
}

/// Lean's exact kind-3 request with an empty signature field.
pub fn empty_signature_request(case: &str) -> Vec<u8> {
    emit(&["empty_signature", case])
}

/// Lean's canonical legacy kind-1 request, never context-bound admission.
pub fn legacy_request() -> Vec<u8> {
    emit(&["legacy"])
}

/// Both exact byte identities needed by an end-to-end admission case.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SignedFixture {
    pub signing_bytes: Vec<u8>,
    pub canonical_request: Vec<u8>,
}

pub fn signed_fixture(case: &str, sign: impl FnOnce(&[u8]) -> Vec<u8>) -> SignedFixture {
    let signing_bytes = signing_bytes(case);
    let signature = sign(&signing_bytes);
    let canonical_request = request(case, &signature);
    SignedFixture {
        signing_bytes,
        canonical_request,
    }
}
