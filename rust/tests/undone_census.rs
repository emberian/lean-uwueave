//! Keeps the generated ⟨UNDONE⟩ ledger wired into the ordinary Cargo gate.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{SystemTime, UNIX_EPOCH};

struct TempRepo(PathBuf);

impl TempRepo {
    fn new() -> Self {
        let nonce = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("the system clock is after the Unix epoch")
            .as_nanos();
        let path = std::env::temp_dir().join(format!(
            "uwueave-undone-census-{}-{nonce}",
            std::process::id()
        ));
        fs::create_dir_all(path.join("Uwueave")).expect("create fixture source directory");
        fs::create_dir_all(path.join("docs")).expect("create fixture docs directory");
        Self(path)
    }
}

impl Drop for TempRepo {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn census_script() -> PathBuf {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    manifest
        .parent()
        .expect("the rust crate lives inside the repository")
        .join("scripts/undone-census.sh")
}

#[test]
fn undone_census_is_current() {
    let manifest = Path::new(env!("CARGO_MANIFEST_DIR"));
    let repo = manifest
        .parent()
        .expect("the rust crate lives inside the repository");
    let script = census_script();
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

#[test]
fn decorated_marker_grammar_counts_only_markers() {
    let fixture = TempRepo::new();
    fs::write(
        fixture.0.join("Uwueave/FormsA.lean"),
        concat!(
            "/- ⟨UNDONE⟩ EXACT_FORM -/\n\n",
            "/- ⟨UNDONE, comma qualifier⟩ COMMA_FORM; ",
            "⟨UNDONE—dash qualifier⟩ DASH_FORM -/\n\n",
            "/- ⟨UNDONEFUL⟩ FALSE_IDENTIFIER -/\n",
            "/- ⟨UNDONE/false⟩ FALSE_PUNCTUATION -/\n",
        ),
    )
    .expect("write first census fixture");
    fs::write(
        fixture.0.join("Uwueave/FormsB.lean"),
        concat!(
            "/- ⟨UNDONE qualified over\n",
            "two source lines⟩ QUALIFIER_FORM -/\n\n",
            "/- plain UNDONE text FALSE_PLAIN -/\n",
        ),
    )
    .expect("write second census fixture");

    let script = census_script();
    let generated = Command::new(&script)
        .env("UWUEAVE_UNDONE_CENSUS_ROOT", &fixture.0)
        .output()
        .expect("generate fixture census");
    assert!(
        generated.status.success(),
        "fixture generation failed with {}\nstdout:\n{}\nstderr:\n{}",
        generated.status,
        String::from_utf8_lossy(&generated.stdout),
        String::from_utf8_lossy(&generated.stderr),
    );

    let ledger = fs::read_to_string(fixture.0.join("docs/UNDONE.md"))
        .expect("read generated fixture census");
    assert!(ledger.contains("**Marker occurrences:** 4"));
    assert!(ledger.contains("**Extracted blocks (marker-bearing source lines):** 3"));
    assert!(ledger.contains("**Lean files containing markers:** 2"));
    for included in ["EXACT_FORM", "COMMA_FORM", "DASH_FORM", "QUALIFIER_FORM"] {
        assert!(ledger.contains(included), "missing marker form {included}");
    }
    for excluded in ["FALSE_IDENTIFIER", "FALSE_PUNCTUATION", "FALSE_PLAIN"] {
        assert!(
            !ledger.contains(excluded),
            "counted false substring {excluded}"
        );
    }

    let checked = Command::new(&script)
        .arg("--check")
        .env("UWUEAVE_UNDONE_CENSUS_ROOT", &fixture.0)
        .output()
        .expect("check fixture census");
    assert!(
        checked.status.success(),
        "fixture --check failed with {}\nstdout:\n{}\nstderr:\n{}",
        checked.status,
        String::from_utf8_lossy(&checked.stdout),
        String::from_utf8_lossy(&checked.stderr),
    );
}
