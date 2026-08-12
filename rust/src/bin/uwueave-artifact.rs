//! Thin host bridge for Lean-owned Preoscript artifact diagnostics.
//!
//! Rust reopens the checksummed physical journal and forwards each unchanged
//! canonical frame as one logical stream.  Lean owns all payload decoding,
//! bounds, and JSON construction; this binary has no artifact semantic twin.

use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, ExitCode, Stdio};

use uwueave::persistence::{ArtifactJournal, JournalOptions, SyncPolicy, TornTailPolicy};

fn usage() -> &'static str {
    "usage: uwueave-artifact inspect JOURNAL [--max-bytes N] [--max-records N] [--max-refs N]"
}

fn repo() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .expect("rust crate is directly below repository root")
        .to_path_buf()
}

fn inspect(path: &Path, bounds: &[String]) -> Result<(), String> {
    if !path.is_file() {
        return Err(format!(
            "artifact journal does not exist: {}",
            path.display()
        ));
    }
    let journal = ArtifactJournal::open(
        path,
        JournalOptions {
            torn_tail: TornTailPolicy::Refuse,
            sync: SyncPolicy::Buffered,
            ..JournalOptions::default()
        },
    )
    .map_err(|error| format!("artifact journal refused: {error}"))?;

    let mut command = Command::new(repo().join("tools/uwueave-preo-inspect"));
    command
        .args(["--journal", "-"])
        .args(bounds)
        .current_dir(repo())
        .stdin(Stdio::piped())
        .stdout(Stdio::inherit())
        .stderr(Stdio::inherit());
    let mut child = command
        .spawn()
        .map_err(|error| format!("launch Lean artifact inspector: {error}"))?;
    {
        let stdin = child
            .stdin
            .as_mut()
            .ok_or_else(|| "Lean artifact inspector stdin was not piped".to_owned())?;
        for frame in journal.frames() {
            stdin
                .write_all(frame.as_bytes())
                .map_err(|error| format!("forward exact artifact frame: {error}"))?;
        }
    }
    let status = child
        .wait()
        .map_err(|error| format!("wait for Lean artifact inspector: {error}"))?;
    if status.success() {
        Ok(())
    } else {
        Err(format!("Lean artifact inspector exited with {status}"))
    }
}

fn run() -> Result<(), String> {
    let mut args = std::env::args().skip(1);
    if args.next().as_deref() != Some("inspect") {
        return Err(usage().to_owned());
    }
    let path = args.next().ok_or_else(|| usage().to_owned())?;
    let bounds: Vec<String> = args.collect();
    let mut cursor = 0;
    while cursor < bounds.len() {
        match bounds[cursor].as_str() {
            "--max-bytes" | "--max-records" | "--max-refs" if cursor + 1 < bounds.len() => {
                cursor += 2
            }
            _ => return Err(usage().to_owned()),
        }
    }
    inspect(Path::new(&path), &bounds)
}

fn main() -> ExitCode {
    match run() {
        Ok(()) => ExitCode::SUCCESS,
        Err(error) => {
            eprintln!("{error}");
            ExitCode::FAILURE
        }
    }
}
