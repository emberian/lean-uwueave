//! Immutable implementation evidence for debt U-0160.
//!
//! This case executes the repository's fail-closed Ledger-2 integrity gate.
//! It closes only the registry-integrity umbrella: U-0161 through U-0169 and
//! the independent U-0170 receipt retain their own classifications and state.

use std::path::{Path, PathBuf};
use std::process::Command;

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("rust crate is directly below repository root")
        .to_path_buf()
}

#[test]
fn debt_closure_u_0160() {
    let output = Command::new("python3")
        .args(["-B", "scripts/ledger2-gate.py", "check"])
        .env("PYTHONDONTWRITEBYTECODE", "1")
        .current_dir(repo())
        .output()
        .expect("launch the machine-readable Ledger-2 integrity gate");
    assert!(
        output.status.success(),
        "Ledger-2 gate failed:\nstdout:\n{}\nstderr:\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    assert_eq!(output.stdout, b"ledger2-gate: OK\n");
    assert!(
        output.stderr.is_empty(),
        "Ledger-2 gate emitted diagnostics: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}
