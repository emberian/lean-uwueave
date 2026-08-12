//! Real-byte acceptance for the thin Rust-to-Lean inspection boundary.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicU64, Ordering};

use serde_json::Value;
use uwueave::persistence::{
    ArtifactFrame, ArtifactJournal, JournalOptions, SyncPolicy, TornTailPolicy,
};

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

fn emit(name: &str) -> Vec<u8> {
    let output = Command::new(repo().join("tools/uwueave-preo-artifact"))
        .args([name, "--stdout"])
        .current_dir(repo())
        .output()
        .expect("launch real Lean artifact emitter");
    assert!(
        output.status.success(),
        "emitter stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    output.stdout
}

fn emit_v3_fixture() -> Vec<u8> {
    let output = Command::new("lake")
        .args([
            "env",
            "lean",
            "--run",
            "tests/ArtifactInspectionV3Fixture.lean",
        ])
        .current_dir(repo())
        .output()
        .expect("launch Lean-owned nonempty V3 fixture");
    assert!(
        output.status.success(),
        "V3 fixture stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    output.stdout
}

fn inspect_frame(path: &Path, extra: &[&str]) -> std::process::Output {
    Command::new(repo().join("tools/uwueave-preo-inspect"))
        .args(["--frame"])
        .arg(path)
        .args(extra)
        .current_dir(repo())
        .output()
        .expect("launch Lean artifact inspector")
}

fn ids(record: &Value, family: &str) -> Vec<u64> {
    record[family]
        .as_array()
        .unwrap()
        .iter()
        .map(|row| row["id"].as_u64().unwrap())
        .collect()
}

#[test]
fn physical_journal_reopens_into_exact_bounded_lean_diagnostics() {
    let semantic = emit("SemanticExport.ArtifactDurableBytes");
    let full = emit("ProjectionV2.Examples.fullExport");
    let semantic_frame = ArtifactFrame::new(semantic.clone()).unwrap();
    let full_frame = ArtifactFrame::new(full.clone()).unwrap();

    let journal_path = TempPath::new("artifact-inspection", "journal");
    {
        let mut journal = ArtifactJournal::open(
            &journal_path.0,
            JournalOptions {
                torn_tail: TornTailPolicy::Refuse,
                sync: SyncPolicy::SyncData,
                ..JournalOptions::default()
            },
        )
        .unwrap();
        assert_eq!(journal.append(semantic_frame).unwrap().sequence, 0);
        assert_eq!(journal.append(full_frame).unwrap().sequence, 1);
        journal.sync(SyncPolicy::SyncData).unwrap();
    }

    let output = Command::new(env!("CARGO_BIN_EXE_uwueave-artifact"))
        .args(["inspect", journal_path.0.to_str().unwrap()])
        .output()
        .expect("run thin physical-journal inspection wrapper");
    assert!(
        output.status.success(),
        "wrapper stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
    let json: Value = serde_json::from_slice(&output.stdout).unwrap();
    assert_eq!(json["schema"], "uwueave/preo-inspection/v1");
    assert_eq!(json["authority"], "diagnostic-only");
    assert_eq!(json["recordCount"], 2);
    assert_eq!(json["completedPrefixLength"], semantic.len() + full.len());
    let records = json["records"].as_array().unwrap();

    assert_eq!(records[0]["declaration"]["id"], 700);
    assert_eq!(ids(&records[0], "futures"), [704]);
    assert_eq!(ids(&records[0], "sessions"), [707, 709]);
    assert_eq!(ids(&records[0], "plans"), [708, 710]);
    assert_eq!(ids(&records[0], "budgets"), [711]);
    assert_eq!(records[0]["startOffset"], 0);
    assert_eq!(records[0]["endOffset"], semantic.len());

    assert_eq!(records[1]["declaration"]["id"], 400);
    assert_eq!(ids(&records[1], "futures"), [404]);
    assert_eq!(ids(&records[1], "sessions"), [407]);
    assert_eq!(ids(&records[1], "plans"), [408]);
    assert_eq!(ids(&records[1], "budgets"), [411]);
    assert_eq!(records[1]["startOffset"], semantic.len());
    assert_eq!(records[1]["endOffset"], semantic.len() + full.len());

    let frame_path = TempPath::new("artifact-inspection-frame", "preo");
    let v3 = emit_v3_fixture();
    fs::write(&frame_path.0, &v3).unwrap();
    let inspected_v3 = inspect_frame(&frame_path.0, &[]);
    assert!(
        inspected_v3.status.success(),
        "V3 inspector stderr: {}",
        String::from_utf8_lossy(&inspected_v3.stderr)
    );
    let v3_json: Value = serde_json::from_slice(&inspected_v3.stdout).unwrap();
    let v3_record = &v3_json["records"][0];
    assert_eq!(v3_record["formatVersion"], 3);
    assert_eq!(v3_record["statusEffect"]["schemaId"], 1000);
    assert_eq!(
        v3_record["statusEffect"]["worldIds"],
        serde_json::json!([1001])
    );
    assert_eq!(v3_record["statusEffect"]["queries"][0]["id"], 1002);
    assert_eq!(
        v3_record["statusEffect"]["queries"][0]["reads"],
        serde_json::json!([402])
    );
    assert_eq!(v3_record["statusEffect"]["results"][0]["id"], 1003);
    assert_eq!(v3_record["statusEffect"]["results"][0]["futureId"], 404);
    assert_eq!(v3_record["statusEffect"]["results"][0]["status"], "exact");
    assert_eq!(
        v3_record["statusEffect"]["results"][0]["effect"],
        serde_json::json!(["exact"])
    );
    assert_eq!(v3_record["statusEffect"]["certificates"][0]["id"], 1006);

    fs::write(&frame_path.0, &semantic).unwrap();
    let bounded = inspect_frame(&frame_path.0, &["--max-refs", "0"]);
    assert!(!bounded.status.success());
    assert!(String::from_utf8_lossy(&bounded.stderr).contains("bounded ProjectionV2"));

    let mut noncanonical = semantic.clone();
    noncanonical[5] = 2;
    fs::write(&frame_path.0, noncanonical).unwrap();
    let refused = inspect_frame(&frame_path.0, &[]);
    assert!(!refused.status.success());
    assert!(
        String::from_utf8_lossy(&refused.stderr).contains("canonical artifact validation refused")
    );

    fs::write(&frame_path.0, &semantic[..semantic.len() - 1]).unwrap();
    let torn = inspect_frame(&frame_path.0, &[]);
    assert!(!torn.status.success());
    assert!(String::from_utf8_lossy(&torn.stderr).contains("torn artifact frame"));

    let mut wrong_version = semantic;
    wrong_version[2] = 1;
    fs::write(&frame_path.0, wrong_version).unwrap();
    let refused = inspect_frame(&frame_path.0, &[]);
    assert!(!refused.status.success());
    assert!(
        String::from_utf8_lossy(&refused.stderr).contains("canonical artifact validation refused")
    );
}
