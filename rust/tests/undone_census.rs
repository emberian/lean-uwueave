//! Keeps the generated ⟨UNDONE⟩ ledger wired into the ordinary Cargo gate.

use std::path::Path;
use std::process::Command;

#[test]
fn undone_census_is_current() {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let repo = manifest
        .parent()
        .expect("the rust crate lives inside the repository");
    let script = repo.join("scripts/undone-census.sh");
    let output = Command::new(&script)
        .arg("--check")
        .current_dir(repo)
        .output()
        .expect("run scripts/undone-census.sh --check");

    assert!(
        output.status.success(),
        "{} --check failed with {}\nstdout:\n{}\nstderr:\n{}",
        script.display(),
        output.status,
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr),
    );
}
