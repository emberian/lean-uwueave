//! Build the exact Lean runtime closure used by the Rust FFI.
//!
//! `Uwueave.RuntimeInit` is the single source of truth: its imports determine
//! both the initializer called by `shim.c` and the native objects archived
//! here. Lake owns dependency discovery, freshness, C generation, and native
//! object compilation. This script never scans `.lake/build/ir` for whatever
//! stale C files happen to exist.

use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};
use std::ffi::OsStr;
use std::fs;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, Output};
#[cfg(any(target_os = "linux", target_os = "macos"))]
use std::{
    fs::OpenOptions,
    os::unix::fs::{MetadataExt, OpenOptionsExt},
};

const PACKAGE: &str = "uwueave";
const RUNTIME_ROOT: &str = "Uwueave.RuntimeInit";
const REQUIRED_KERNELS: [&str; 6] = [
    "Uwueave.Exec",
    "Uwueave.SeqKernel",
    "Uwueave.EraKernel",
    "Uwueave.Preo.ArtifactJournalKernel",
    "Uwueave.RuntimeAuthV4Kernel",
    "Uwueave.RuntimeAuthV4AdmissionTraceKernel",
];
const LEDGER2_MANIFEST: &str = "docs/trust/ledger2-v1.json";
const LEDGER2_OBSERVATION_ENV: &str = "UWUEAVE_LEDGER2_OBSERVATION_OUT";
const SUPPORTED_TARGETS: [&str; 2] = ["aarch64-apple-darwin", "x86_64-unknown-linux-gnu"];

#[derive(Clone, Debug, Eq, PartialEq)]
struct FileState {
    bytes: Vec<u8>,
    modified: Option<std::time::SystemTime>,
}

type SourceSnapshot = BTreeMap<PathBuf, FileState>;

#[derive(Clone, Debug, Eq, PartialEq)]
struct ArchiveMemberObservation {
    bytes: usize,
    kind: &'static str,
    module: Option<String>,
    name: String,
    sha256: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ToolIdentity {
    argv: Vec<String>,
    path: PathBuf,
    sha256: String,
    version: String,
}

fn main() {
    let manifest = required_env_path("CARGO_MANIFEST_DIR");
    let repo = manifest
        .parent()
        .expect("rust crate must live directly below the repository root")
        .to_path_buf();

    let target = guard_native_build();
    let observation_out = std::env::var_os(LEDGER2_OBSERVATION_ENV).map(PathBuf::from);
    let prefix = lean_prefix(&repo);
    let lake = prefix.join("bin/lake");
    executable_path(&lake)
        .unwrap_or_else(|e| panic!("cannot resolve authoritative Lake executable: {e}"));
    emit_rerun_inputs(&repo, &manifest);
    let before = snapshot_inputs(&repo).unwrap_or_else(|e| panic!("source snapshot failed: {e}"));

    // This broad proof gate is intentional. A targeted runtime build must not
    // let Cargo go green while some other theorem/module in the Lean library
    // is red, nor may old generated output substitute for a failed build.
    run_lake_status(&lake, &repo, &["build"], "full `lake build`");

    // Ask Lake for the root C path solely to derive the corresponding setup
    // path. No emitted filename or IR directory is guessed here.
    let root_c = query_paths(&lake, &repo, false, &[format!("+{RUNTIME_ROOT}:c")]);
    let root_c = exactly_one(root_c, "RuntimeInit C query");
    validate_lake_output_path(RUNTIME_ROOT, &root_c, ".c", &repo)
        .unwrap_or_else(|e| panic!("invalid RuntimeInit C result: {e}"));
    let setup_path = root_c.with_extension("setup.json");
    let setup_state = stable_file_state(&setup_path).unwrap_or_else(|e| {
        panic!(
            "invalid Lake setup description {}: {e}",
            setup_path.display()
        )
    });
    let modules = closure_from_setup(&setup_state.bytes, &repo)
        .unwrap_or_else(|e| panic!("invalid RuntimeInit setup description: {e}"));

    // A single ordered query asks Lake to incrementally compile exactly the
    // closure it just reported. Query results correspond positionally to
    // targets, which lets us reject missing, duplicate, or unexpected paths.
    let object_targets: Vec<String> = modules
        .iter()
        .map(|module| format!("+{module}:c.o"))
        .collect();
    let objects = query_paths(&lake, &repo, false, &object_targets);
    validate_object_results(&modules, &objects, &repo)
        .unwrap_or_else(|e| panic!("invalid Lake object result: {e}"));

    let object_states: Vec<FileState> = objects
        .iter()
        .map(|path| {
            stable_file_state(path)
                .unwrap_or_else(|e| panic!("cannot snapshot Lake object {}: {e}", path.display()))
        })
        .collect();
    let object_bytes: usize = object_states.iter().map(|state| state.bytes.len()).sum();
    println!(
        "cargo:warning=Lean runtime closure: {} Lake-owned objects, {} bytes before archive",
        objects.len(),
        object_bytes
    );

    let out_dir = required_env_path("OUT_DIR");
    let staged_objects = stage_object_snapshots(&out_dir, &modules, &object_states)
        .unwrap_or_else(|e| panic!("cannot stage stable Lake object snapshots: {e}"));

    // cc compiles exactly one source (the ABI shim), removes any old archive,
    // and archives that object plus only the stable Lake object snapshots.
    let mut cc = cc::Build::new();
    cc.include(prefix.join("include"));
    cc.file(manifest.join("shim.c"));
    cc.objects(&staged_objects);
    cc.warnings(false);
    cc.opt_level(2);
    let compiler_tool = cc.get_compiler();
    let compiler_command = compiler_tool.to_command();
    let compiler_identity = command_identity(&compiler_command)
        .unwrap_or_else(|e| panic!("cannot identify selected C compiler command: {e}"));
    let compiler_path = executable_path(compiler_tool.path())
        .unwrap_or_else(|e| panic!("cannot resolve selected C compiler: {e}"));
    if observation_out.is_some() && compiler_identity.path != compiler_path {
        panic!(
            "compiler wrappers are outside the reproducible native-evidence policy: selected {} around {}",
            compiler_identity.path.display(),
            compiler_path.display()
        );
    }
    let archiver_command = cc.get_archiver();
    let archiver_identity = command_identity(&archiver_command)
        .unwrap_or_else(|e| panic!("cannot identify selected archiver: {e}"));
    cc.compile("uwueave_kernel");
    let verifier_archiver = prefix.join("bin/llvm-ar");
    let archive_path = out_dir.join("libuwueave_kernel.a");
    let archive_members =
        verify_archive(&verifier_archiver, &archive_path, &staged_objects, &modules)
            .unwrap_or_else(|e| panic!("runtime archive postcondition failed: {e}"));

    // Close both TOCTOU windows. First, the entire default Lean target must
    // still be current without building. Then the root C and every selected
    // object must still be current, and Lake must return the identical paths.
    run_lake_status(
        &lake,
        &repo,
        &["--no-build", "build"],
        "final no-build Lean proof gate",
    );
    let mut final_targets = Vec::with_capacity(1 + object_targets.len());
    final_targets.push(format!("+{RUNTIME_ROOT}:c"));
    final_targets.extend(object_targets);
    let final_paths = query_paths(&lake, &repo, true, &final_targets);
    if final_paths.first() != Some(&root_c) || final_paths.get(1..) != Some(objects.as_slice()) {
        panic!(
            "Lake runtime outputs changed during the Cargo build; refusing to link a mixed generation"
        );
    }
    let final_setup = stable_file_state(&setup_path)
        .unwrap_or_else(|e| panic!("cannot re-read final setup description: {e}"));
    if final_setup != setup_state {
        panic!("RuntimeInit setup description changed while the archive was assembled");
    }
    let final_modules = closure_from_setup(&final_setup.bytes, &repo)
        .unwrap_or_else(|e| panic!("final RuntimeInit setup description is invalid: {e}"));
    if final_modules != modules {
        panic!("RuntimeInit transitive closure changed while the archive was assembled");
    }
    for ((module, path), expected) in modules.iter().zip(&objects).zip(&object_states) {
        let actual = stable_file_state(path)
            .unwrap_or_else(|e| panic!("cannot re-read final object for {module}: {e}"));
        if &actual != expected {
            panic!("Lake object for {module} changed while the archive was assembled");
        }
    }
    let after =
        snapshot_inputs(&repo).unwrap_or_else(|e| panic!("final source snapshot failed: {e}"));
    if before != after {
        panic!(
            "Lean sources or build configuration changed during the Cargo build; retry from one stable source generation"
        );
    }

    if let Some(path) = observation_out {
        let linker = cargo_linker(&target)
            .unwrap_or_else(|e| panic!("native observation requires an exact Cargo linker: {e}"));
        let linker_identity = tool_identity(&linker, &[])
            .unwrap_or_else(|e| panic!("cannot identify selected Cargo linker: {e}"));
        let verifier_identity = tool_identity(&verifier_archiver, &[])
            .unwrap_or_else(|e| panic!("cannot identify Lean archive verifier: {e}"));
        let lean_identity = tool_identity(&prefix.join("bin/lean"), &[])
            .unwrap_or_else(|e| panic!("cannot identify authoritative Lean executable: {e}"));
        let lake_identity = tool_identity(&prefix.join("bin/lake"), &[])
            .unwrap_or_else(|e| panic!("cannot identify authoritative Lake executable: {e}"));
        write_native_observation(
            &path,
            &repo,
            &target,
            &before,
            &setup_path,
            &setup_state,
            &modules,
            &archive_path,
            &archive_members,
            &compiler_identity,
            &archiver_identity,
            &linker_identity,
            &verifier_identity,
            &lean_identity,
            &lake_identity,
            &prefix,
        )
        .unwrap_or_else(|e| panic!("cannot write Ledger-2 native observation: {e}"));
    }

    // Preserve the existing dynamic Lean-runtime link contract.
    let libdir = prefix.join("lib/lean");
    println!("cargo:rustc-link-search=native={}", libdir.display());
    println!("cargo:rustc-link-lib=dylib=leanshared");
    let libdir_text = libdir
        .to_str()
        .expect("Lean library path must be UTF-8 for Cargo linker directives");
    if libdir_text.contains(['\n', '\r']) {
        panic!("Lean library path contains a Cargo-directive newline");
    }
    println!("cargo:rustc-link-arg=-Xlinker");
    println!("cargo:rustc-link-arg=-rpath");
    println!("cargo:rustc-link-arg=-Xlinker");
    println!("cargo:rustc-link-arg={libdir_text}");
}

fn required_env_path(name: &str) -> PathBuf {
    PathBuf::from(
        std::env::var_os(name).unwrap_or_else(|| {
            panic!("Cargo did not provide required environment variable {name}")
        }),
    )
}

fn guard_native_build() -> String {
    let host = std::env::var("HOST").expect("Cargo did not provide HOST");
    let target = std::env::var("TARGET").expect("Cargo did not provide TARGET");
    if host != target {
        panic!(
            "cross-compilation is unsupported: Lake emitted host objects for {host}, but Cargo requested {target}"
        );
    }
    if !SUPPORTED_TARGETS.contains(&target.as_str()) {
        panic!(
            "unsupported native target {target}; v0.2 evidence is scoped exactly to {}",
            SUPPORTED_TARGETS.join(" and ")
        );
    }
    let os = std::env::var("CARGO_CFG_TARGET_OS")
        .expect("Cargo did not provide CARGO_CFG_TARGET_OS to the build script");
    let expected_os = if target == "aarch64-apple-darwin" {
        "macos"
    } else {
        "linux"
    };
    if os != expected_os {
        panic!("Cargo target {target} reported inconsistent target OS {os}");
    }
    target
}

fn emit_rerun_inputs(repo: &Path, manifest: &Path) {
    for path in [
        repo.join("Uwueave"),
        repo.join("Uwueave.lean"),
        repo.join("lakefile.toml"),
        repo.join("lake-manifest.json"),
        repo.join("lean-toolchain"),
        repo.join(LEDGER2_MANIFEST),
        manifest.join("shim.c"),
        manifest.join("build.rs"),
        manifest.join("Cargo.toml"),
        manifest.join("Cargo.lock"),
    ] {
        println!("cargo:rerun-if-changed={}", path.display());
    }
    println!("cargo:rerun-if-env-changed={LEDGER2_OBSERVATION_ENV}");
    for target in SUPPORTED_TARGETS {
        println!(
            "cargo:rerun-if-env-changed=CARGO_TARGET_{}_LINKER",
            target.replace('-', "_").to_ascii_uppercase()
        );
    }
}

fn snapshot_inputs(repo: &Path) -> Result<SourceSnapshot, String> {
    let mut paths = vec![
        repo.join("Uwueave.lean"),
        repo.join("lakefile.toml"),
        repo.join("lake-manifest.json"),
        repo.join("lean-toolchain"),
        repo.join(LEDGER2_MANIFEST),
        repo.join("rust/shim.c"),
        repo.join("rust/build.rs"),
        repo.join("rust/Cargo.toml"),
        repo.join("rust/Cargo.lock"),
    ];
    collect_lean_files(&repo.join("Uwueave"), &mut paths)?;
    paths.sort();
    paths.dedup();

    let mut snapshot = BTreeMap::new();
    for path in paths {
        let state = stable_file_state(&path)?;
        let relative = path
            .strip_prefix(repo)
            .map_err(|_| format!("input escaped repository: {}", path.display()))?
            .to_path_buf();
        snapshot.insert(relative, state);
    }
    Ok(snapshot)
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn stable_file_state(path: &Path) -> Result<FileState, String> {
    stable_file_state_with_pre_open(path, || {})
}

#[cfg(not(any(target_os = "linux", target_os = "macos")))]
fn stable_file_state(path: &Path) -> Result<FileState, String> {
    Err(format!(
        "descriptor-bound no-follow reads are unsupported on this target: {}",
        path.display()
    ))
}

#[cfg(target_os = "linux")]
const O_NOFOLLOW_FLAG: i32 = 0x20000;
#[cfg(target_os = "macos")]
const O_NOFOLLOW_FLAG: i32 = 0x0100;

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn metadata_identity(metadata: &fs::Metadata) -> (u64, u64, u32, u64, i64, i64, i64, i64) {
    (
        metadata.dev(),
        metadata.ino(),
        metadata.mode(),
        metadata.len(),
        metadata.mtime(),
        metadata.mtime_nsec(),
        metadata.ctime(),
        metadata.ctime_nsec(),
    )
}

#[cfg(any(target_os = "linux", target_os = "macos"))]
fn stable_file_state_with_pre_open<F>(path: &Path, pre_open: F) -> Result<FileState, String>
where
    F: FnOnce(),
{
    let path_before = fs::symlink_metadata(path)
        .map_err(|e| format!("cannot inspect {}: {e}", path.display()))?;
    if path_before.file_type().is_symlink() || !path_before.is_file() {
        return Err(format!(
            "path is not a non-symlink regular file: {}",
            path.display()
        ));
    }
    let canonical = fs::canonicalize(path)
        .map_err(|e| format!("cannot canonicalize {}: {e}", path.display()))?;
    if canonical != path {
        return Err(format!("path is not canonical: {}", path.display()));
    }

    // Unit tests use this hook to deterministically reproduce the exact race
    // between pathname validation and descriptor acquisition.
    pre_open();
    let mut file = OpenOptions::new()
        .read(true)
        .custom_flags(O_NOFOLLOW_FLAG)
        .open(path)
        .map_err(|e| format!("cannot open no-follow descriptor {}: {e}", path.display()))?;
    let descriptor_before = file
        .metadata()
        .map_err(|e| format!("cannot inspect opened descriptor {}: {e}", path.display()))?;
    if !descriptor_before.is_file()
        || metadata_identity(&descriptor_before) != metadata_identity(&path_before)
    {
        return Err(format!(
            "path changed before its descriptor was opened: {}",
            path.display()
        ));
    }
    let mut bytes = Vec::new();
    file.read_to_end(&mut bytes)
        .map_err(|e| format!("cannot read opened descriptor {}: {e}", path.display()))?;
    let descriptor_after = file.metadata().map_err(|e| {
        format!(
            "cannot re-inspect opened descriptor {}: {e}",
            path.display()
        )
    })?;
    let path_after = fs::symlink_metadata(path)
        .map_err(|e| format!("cannot re-inspect {}: {e}", path.display()))?;
    if path_after.file_type().is_symlink()
        || !path_after.is_file()
        || metadata_identity(&descriptor_before) != metadata_identity(&descriptor_after)
        || metadata_identity(&descriptor_after) != metadata_identity(&path_after)
        || descriptor_after.len() != bytes.len() as u64
    {
        return Err(format!(
            "file changed while its descriptor was read: {}",
            path.display()
        ));
    }
    Ok(FileState {
        bytes,
        modified: descriptor_after.modified().ok(),
    })
}

fn collect_lean_files(dir: &Path, out: &mut Vec<PathBuf>) -> Result<(), String> {
    let entries = fs::read_dir(dir)
        .map_err(|e| format!("cannot read Lean source directory {}: {e}", dir.display()))?;
    for entry in entries {
        let entry = entry.map_err(|e| format!("cannot read entry in {}: {e}", dir.display()))?;
        let path = entry.path();
        let file_type = entry
            .file_type()
            .map_err(|e| format!("cannot inspect source path {}: {e}", path.display()))?;
        if file_type.is_symlink() {
            return Err(format!(
                "symlinks are not allowed in Lean sources: {}",
                path.display()
            ));
        }
        if file_type.is_dir() {
            collect_lean_files(&path, out)?;
        } else if file_type.is_file() && path.extension() == Some(OsStr::new("lean")) {
            out.push(path);
        }
    }
    Ok(())
}

fn run_lake_status(lake: &Path, repo: &Path, args: &[&str], label: &str) {
    let status = Command::new(lake)
        .args(args)
        .current_dir(repo)
        .status()
        .unwrap_or_else(|e| panic!("failed to launch {label}: {e}"));
    if !status.success() {
        panic!(
            "{label} failed. This crate wraps Lean-compiled semantics; stale generated output is never accepted."
        );
    }
}

fn lake_query(lake: &Path, repo: &Path, no_build: bool, targets: &[String]) -> Output {
    let mut command = Command::new(lake);
    if no_build {
        command.arg("--no-build");
    }
    command.args(["--quiet", "--json", "query"]);
    command.args(targets);
    command
        .current_dir(repo)
        .output()
        .unwrap_or_else(|e| panic!("failed to launch Lake query: {e}"))
}

fn query_paths(lake: &Path, repo: &Path, no_build: bool, targets: &[String]) -> Vec<PathBuf> {
    let output = lake_query(lake, repo, no_build, targets);
    if !output.status.success() {
        panic!(
            "Lake {}query failed for exact runtime targets.\nstdout:\n{}\nstderr:\n{}",
            if no_build { "no-build " } else { "" },
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    parse_query_paths(&output.stdout, targets.len())
        .unwrap_or_else(|e| panic!("malformed Lake query output: {e}"))
}

fn parse_query_paths(bytes: &[u8], expected: usize) -> Result<Vec<PathBuf>, String> {
    let stream = serde_json::Deserializer::from_slice(bytes).into_iter::<Value>();
    let mut paths = Vec::new();
    for value in stream {
        let value = value.map_err(|e| format!("invalid JSON value: {e}"))?;
        let path = value
            .as_str()
            .ok_or_else(|| format!("expected a JSON path string, got {value}"))?;
        if path.is_empty() {
            return Err("Lake returned an empty output path".into());
        }
        paths.push(PathBuf::from(path));
    }
    if paths.len() != expected {
        return Err(format!(
            "expected {expected} target results, received {}",
            paths.len()
        ));
    }
    Ok(paths)
}

fn exactly_one(mut paths: Vec<PathBuf>, context: &str) -> PathBuf {
    if paths.len() != 1 {
        panic!("{context} returned {} paths instead of one", paths.len());
    }
    paths.pop().unwrap()
}

fn closure_from_setup(bytes: &[u8], repo: &Path) -> Result<Vec<String>, String> {
    let value: Value = serde_json::from_slice(bytes).map_err(|e| format!("invalid JSON: {e}"))?;
    let setup = value
        .as_object()
        .ok_or_else(|| "top-level setup value is not an object".to_string())?;
    if setup.get("package").and_then(Value::as_str) != Some(PACKAGE) {
        return Err(format!("setup package is not {PACKAGE:?}"));
    }
    if setup.get("name").and_then(Value::as_str) != Some(RUNTIME_ROOT) {
        return Err(format!("setup name is not {RUNTIME_ROOT:?}"));
    }
    let expected_fields: BTreeSet<&str> = [
        "plugins",
        "package",
        "options",
        "name",
        "isModule",
        "importArts",
        "dynlibs",
    ]
    .into_iter()
    .collect();
    let actual_fields: BTreeSet<&str> = setup.keys().map(String::as_str).collect();
    if actual_fields != expected_fields {
        return Err(format!(
            "unexpected setup schema: expected {expected_fields:?}, got {actual_fields:?}"
        ));
    }
    if setup.get("isModule") != Some(&Value::Bool(false)) {
        return Err("setup isModule field is not the expected false value".into());
    }
    if setup.get("options").and_then(Value::as_object).is_none() {
        return Err("setup options field is not an object".into());
    }
    for field in ["plugins", "dynlibs"] {
        let entries = setup
            .get(field)
            .and_then(Value::as_array)
            .ok_or_else(|| format!("setup {field} field is not an array"))?;
        if !entries.is_empty() {
            return Err(format!(
                "setup {field} is nonempty, but the runtime archive has no policy for it"
            ));
        }
    }
    let imports = setup
        .get("importArts")
        .and_then(Value::as_object)
        .ok_or_else(|| "setup importArts field is missing or not an object".to_string())?;

    let mut modules = BTreeSet::new();
    modules.insert(RUNTIME_ROOT.to_string());
    let mut artifact_root: Option<PathBuf> = None;
    for (module, artifacts) in imports {
        validate_module_name(module)?;
        if module == RUNTIME_ROOT {
            return Err("RuntimeInit unexpectedly imports itself".into());
        }
        let artifacts = artifacts
            .as_array()
            .ok_or_else(|| format!("importArts[{module:?}] is not an array"))?;
        if artifacts.len() != 1 {
            return Err(format!(
                "importArts[{module:?}] must name exactly one olean, got {}",
                artifacts.len()
            ));
        }
        let artifact = artifacts[0]
            .as_str()
            .ok_or_else(|| format!("importArts[{module:?}] is not a string path"))?;
        validate_import_artifact(module, Path::new(artifact), repo, &mut artifact_root)?;
        if !modules.insert(module.clone()) {
            return Err(format!("duplicate imported module {module:?}"));
        }
    }
    for required in REQUIRED_KERNELS {
        if !modules.contains(required) {
            return Err(format!("required runtime kernel {required:?} is absent"));
        }
    }
    Ok(modules.into_iter().collect())
}

fn validate_module_name(module: &str) -> Result<(), String> {
    let Some(rest) = module.strip_prefix("Uwueave.") else {
        return Err(format!("unexpected non-Uwueave module {module:?}"));
    };
    if rest.is_empty()
        || rest.split('.').any(|segment| {
            segment.is_empty()
                || !segment
                    .bytes()
                    .all(|b| b.is_ascii_alphanumeric() || b == b'_')
        })
    {
        return Err(format!("malformed module name {module:?}"));
    }
    Ok(())
}

fn module_suffix(module: &str, ending: &str) -> PathBuf {
    let mut parts = module.split('.').collect::<Vec<_>>();
    let last = parts.pop().expect("validated module has a segment");
    let mut suffix = PathBuf::new();
    for part in parts {
        suffix.push(part);
    }
    suffix.push(format!("{last}{ending}"));
    suffix
}

fn strip_path_suffix<'a>(path: &'a Path, suffix: &Path) -> Option<&'a Path> {
    if !path.ends_with(suffix) {
        return None;
    }
    path.ancestors().nth(suffix.components().count())
}

fn validate_lake_output_path(
    module: &str,
    path: &Path,
    ending: &str,
    repo: &Path,
) -> Result<PathBuf, String> {
    if !path.is_absolute() {
        return Err(format!("path is not absolute: {}", path.display()));
    }
    let metadata = fs::symlink_metadata(path)
        .map_err(|e| format!("cannot inspect {}: {e}", path.display()))?;
    if metadata.file_type().is_symlink() || !metadata.is_file() {
        return Err(format!(
            "path is not a non-symlink regular file: {}",
            path.display()
        ));
    }
    let canonical = fs::canonicalize(path)
        .map_err(|e| format!("cannot canonicalize {}: {e}", path.display()))?;
    if canonical != path {
        return Err(format!(
            "Lake path is not already canonical: {} resolves to {}",
            path.display(),
            canonical.display()
        ));
    }
    let suffix = module_suffix(module, ending);
    let root = strip_path_suffix(path, &suffix).ok_or_else(|| {
        format!(
            "path {} does not match module {module:?} and suffix {ending:?}",
            path.display()
        )
    })?;
    let canonical_repo = fs::canonicalize(repo)
        .map_err(|e| format!("cannot canonicalize repository {}: {e}", repo.display()))?;
    if !root.starts_with(&canonical_repo) {
        return Err(format!(
            "Lake path escaped this repository: {}",
            path.display()
        ));
    }
    Ok(root.to_path_buf())
}

fn validate_import_artifact(
    module: &str,
    artifact: &Path,
    repo: &Path,
    common_root: &mut Option<PathBuf>,
) -> Result<(), String> {
    let root = validate_lake_output_path(module, artifact, ".olean", repo)?;
    match common_root {
        Some(expected) if expected != &root => {
            return Err(format!(
                "import artifacts have inconsistent roots: {} and {}",
                expected.display(),
                root.display()
            ));
        }
        None => *common_root = Some(root),
        _ => {}
    }
    Ok(())
}

fn validate_object_results(
    modules: &[String],
    objects: &[PathBuf],
    repo: &Path,
) -> Result<(), String> {
    if modules.len() != objects.len() {
        return Err(format!(
            "{} modules produced {} object results",
            modules.len(),
            objects.len()
        ));
    }
    let mut seen = BTreeSet::new();
    let mut object_root: Option<PathBuf> = None;
    for (module, object) in modules.iter().zip(objects) {
        if !seen.insert(object.clone()) {
            return Err(format!("duplicate Lake object path: {}", object.display()));
        }
        let root = validate_lake_output_path(module, object, ".c.o.export", repo)?;
        match &object_root {
            Some(expected) if expected != &root => {
                return Err(format!(
                    "Lake objects have inconsistent roots: {} and {}",
                    expected.display(),
                    root.display()
                ));
            }
            None => object_root = Some(root),
            _ => {}
        }
    }
    Ok(())
}

fn stage_object_snapshots(
    out_dir: &Path,
    modules: &[String],
    states: &[FileState],
) -> Result<Vec<PathBuf>, String> {
    if modules.len() != states.len() {
        return Err("module/object snapshot count mismatch".into());
    }
    let stage = out_dir.join("lean-runtime-closure");
    match fs::symlink_metadata(&stage) {
        Ok(metadata) if metadata.file_type().is_symlink() || !metadata.is_dir() => {
            return Err(format!(
                "object staging path is not a non-symlink directory: {}",
                stage.display()
            ));
        }
        Ok(_) => {}
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
            fs::create_dir(&stage)
                .map_err(|e| format!("cannot create staging directory {}: {e}", stage.display()))?;
        }
        Err(error) => {
            return Err(format!(
                "cannot inspect staging directory {}: {error}",
                stage.display()
            ));
        }
    }
    let mut paths = Vec::with_capacity(modules.len());
    let mut names = BTreeSet::new();
    for (index, (module, state)) in modules.iter().zip(states).enumerate() {
        let name = format!("{index:03}-{}.o", module.replace('.', "__"));
        if !names.insert(name.clone()) {
            return Err(format!("duplicate staged object member name {name:?}"));
        }
        let path = stage.join(name);
        match fs::remove_file(&path) {
            Ok(()) => {}
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
            Err(error) => {
                return Err(format!(
                    "cannot replace staged object {}: {error}",
                    path.display()
                ));
            }
        }
        let mut file = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)
            .map_err(|e| format!("cannot create staged object {}: {e}", path.display()))?;
        file.write_all(&state.bytes)
            .map_err(|e| format!("cannot write staged object {}: {e}", path.display()))?;
        file.flush()
            .map_err(|e| format!("cannot flush staged object {}: {e}", path.display()))?;
        drop(file);
        let staged = stable_file_state(&path)?;
        if staged.bytes != state.bytes {
            return Err(format!(
                "staged object differs from Lake object for {module}"
            ));
        }
        paths.push(path);
    }
    Ok(paths)
}

fn verify_archive(
    llvm_ar: &Path,
    archive: &Path,
    staged_objects: &[PathBuf],
    modules: &[String],
) -> Result<Vec<ArchiveMemberObservation>, String> {
    if staged_objects.len() != modules.len() {
        return Err("archive observation module/object count mismatch".into());
    }
    if !llvm_ar.is_absolute() || !llvm_ar.is_file() {
        return Err(format!(
            "Lean toolchain llvm-ar is missing: {}",
            llvm_ar.display()
        ));
    }
    let before = stable_file_state(archive)?;
    let listing = Command::new(llvm_ar)
        .args(["t", archive.to_str().ok_or("archive path is not UTF-8")?])
        .output()
        .map_err(|e| format!("cannot list runtime archive: {e}"))?;
    if !listing.status.success() {
        return Err(format!(
            "llvm-ar could not list runtime archive: {}",
            String::from_utf8_lossy(&listing.stderr)
        ));
    }
    let listing = std::str::from_utf8(&listing.stdout)
        .map_err(|e| format!("archive member listing is not UTF-8: {e}"))?;
    let members: Vec<&str> = listing.lines().filter(|line| !line.is_empty()).collect();
    if members.len() != staged_objects.len() + 1 {
        return Err(format!(
            "archive has {} members; expected {} Lake objects plus one shim",
            members.len(),
            staged_objects.len()
        ));
    }
    let unique: BTreeSet<&str> = members.iter().copied().collect();
    if unique.len() != members.len() {
        return Err("archive contains duplicate member names".into());
    }

    let mut expected = BTreeSet::new();
    let mut observations = Vec::with_capacity(members.len());
    for (object, module) in staged_objects.iter().zip(modules) {
        let name = object
            .file_name()
            .and_then(OsStr::to_str)
            .ok_or_else(|| format!("staged object name is not UTF-8: {}", object.display()))?;
        expected.insert(name);
        if !unique.contains(name) {
            return Err(format!("archive is missing staged Lake object {name:?}"));
        }
        let extracted = Command::new(llvm_ar)
            .args([
                "p",
                archive.to_str().ok_or("archive path is not UTF-8")?,
                name,
            ])
            .output()
            .map_err(|e| format!("cannot extract archive member {name:?}: {e}"))?;
        if !extracted.status.success() {
            return Err(format!(
                "llvm-ar could not extract {name:?}: {}",
                String::from_utf8_lossy(&extracted.stderr)
            ));
        }
        let source = stable_file_state(object)?;
        if extracted.stdout != source.bytes {
            return Err(format!("archived bytes differ for Lake object {name:?}"));
        }
        observations.push(ArchiveMemberObservation {
            bytes: extracted.stdout.len(),
            kind: "lake",
            module: Some(module.clone()),
            name: name.to_string(),
            sha256: sha256_hex(&extracted.stdout),
        });
    }
    let extras: Vec<&str> = members
        .iter()
        .copied()
        .filter(|member| !expected.contains(member))
        .collect();
    if extras.len() != 1 || !extras[0].ends_with("shim.o") {
        return Err(format!(
            "archive's sole non-Lake member is not the compiled shim: {extras:?}"
        ));
    }
    let shim_name = extras[0];
    let shim = Command::new(llvm_ar)
        .args([
            "p",
            archive.to_str().ok_or("archive path is not UTF-8")?,
            shim_name,
        ])
        .output()
        .map_err(|e| format!("cannot extract compiled shim {shim_name:?}: {e}"))?;
    if !shim.status.success() {
        return Err(format!(
            "llvm-ar could not extract shim {shim_name:?}: {}",
            String::from_utf8_lossy(&shim.stderr)
        ));
    }
    observations.push(ArchiveMemberObservation {
        bytes: shim.stdout.len(),
        kind: "shim",
        module: None,
        name: shim_name.to_string(),
        sha256: sha256_hex(&shim.stdout),
    });
    let observations: Vec<ArchiveMemberObservation> = members
        .iter()
        .map(|name| {
            observations
                .iter()
                .find(|entry| entry.name == **name)
                .cloned()
                .ok_or_else(|| format!("archive member {name:?} lacks an observation"))
        })
        .collect::<Result<_, _>>()?;
    let after = stable_file_state(archive)?;
    if before != after {
        return Err("archive changed while its exact membership was verified".into());
    }
    Ok(observations)
}

fn locate_executable(program: &Path) -> Result<(PathBuf, PathBuf), String> {
    let invocation = if program.components().count() > 1 || program.is_absolute() {
        program.to_path_buf()
    } else {
        let path = std::env::var_os("PATH").ok_or("PATH is absent")?;
        std::env::split_paths(&path)
            .map(|directory| directory.join(program))
            .find(|candidate| candidate.is_file())
            .ok_or_else(|| format!("executable {:?} is absent from PATH", program))?
    };
    let canonical = fs::canonicalize(&invocation).map_err(|e| {
        format!(
            "cannot canonicalize executable {}: {e}",
            invocation.display()
        )
    })?;
    stable_file_state(&canonical)?;
    Ok((invocation, canonical))
}

fn executable_path(program: &Path) -> Result<PathBuf, String> {
    Ok(locate_executable(program)?.1)
}

fn tool_identity(program: &Path, args: &[std::ffi::OsString]) -> Result<ToolIdentity, String> {
    let (invocation, path) = locate_executable(program)?;
    let argv: Vec<String> = args
        .iter()
        .map(|arg| {
            arg.to_str()
                .map(str::to_string)
                .ok_or_else(|| "selected tool argument is not UTF-8".to_string())
        })
        .collect::<Result<_, _>>()?;
    let output = Command::new(&invocation)
        .arg("--version")
        .output()
        .map_err(|e| format!("cannot query {} --version: {e}", path.display()))?;
    let mut version = format!("exit={}\n", output.status.code().unwrap_or(-1));
    version.push_str(&String::from_utf8_lossy(&output.stdout));
    version.push_str(&String::from_utf8_lossy(&output.stderr));
    if version.len() > 64 * 1024 {
        return Err(format!(
            "tool version output is unbounded: {}",
            path.display()
        ));
    }
    if version.contains('\0') {
        return Err(format!(
            "tool version output contains NUL: {}",
            path.display()
        ));
    }
    let state = stable_file_state(&path)?;
    Ok(ToolIdentity {
        argv,
        path,
        sha256: sha256_hex(&state.bytes),
        version,
    })
}

fn command_identity(command: &Command) -> Result<ToolIdentity, String> {
    let args: Vec<std::ffi::OsString> = command.get_args().map(OsStr::to_os_string).collect();
    tool_identity(Path::new(command.get_program()), &args)
}

fn cargo_linker(target: &str) -> Result<PathBuf, String> {
    let key = format!(
        "CARGO_TARGET_{}_LINKER",
        target.replace('-', "_").to_ascii_uppercase()
    );
    let value = std::env::var_os(&key)
        .ok_or_else(|| format!("{key} is absent; CI must select the linker explicitly"))?;
    executable_path(Path::new(&value))
}

fn runtime_library(prefix: &Path, target: &str) -> Result<PathBuf, String> {
    let extension = if target == "aarch64-apple-darwin" {
        "dylib"
    } else {
        "so"
    };
    let path = prefix.join(format!("lib/lean/libleanshared.{extension}"));
    let canonical = fs::canonicalize(&path)
        .map_err(|e| format!("cannot find selected Lean runtime {}: {e}", path.display()))?;
    stable_file_state(&canonical)?;
    Ok(canonical)
}

fn tool_json(identity: &ToolIdentity) -> Value {
    serde_json::json!({
        "argv": identity.argv,
        "path": identity.path,
        "sha256": identity.sha256,
        "version": identity.version,
    })
}

#[allow(clippy::too_many_arguments)]
fn write_native_observation(
    output: &Path,
    repo: &Path,
    target: &str,
    snapshot: &SourceSnapshot,
    setup_path: &Path,
    setup: &FileState,
    modules: &[String],
    archive: &Path,
    members: &[ArchiveMemberObservation],
    compiler: &ToolIdentity,
    archiver: &ToolIdentity,
    linker: &ToolIdentity,
    verifier_archiver: &ToolIdentity,
    lean: &ToolIdentity,
    lake: &ToolIdentity,
    prefix: &Path,
) -> Result<(), String> {
    let parent = observation_output_parent(output)?;
    let archive_state = stable_file_state(archive)?;
    let runtime_path = runtime_library(prefix, target)?;
    let runtime_state = stable_file_state(&runtime_path)?;
    let manifest_path = repo.join(LEDGER2_MANIFEST);
    let manifest_state = stable_file_state(&manifest_path)?;
    let toolchain = stable_file_state(&repo.join("lean-toolchain"))?;
    let toolchain = std::str::from_utf8(&toolchain.bytes)
        .map_err(|e| format!("lean-toolchain is not UTF-8: {e}"))?
        .trim();
    if toolchain.is_empty() || toolchain.contains(['\n', '\r']) {
        return Err("lean-toolchain does not contain one exact toolchain name".into());
    }
    let member_values: Vec<Value> = members
        .iter()
        .map(|member| {
            serde_json::json!({
                "bytes": member.bytes,
                "kind": member.kind,
                "module": member.module,
                "name": member.name,
                "sha256": member.sha256,
            })
        })
        .collect();
    let source_files: Vec<Value> = snapshot
        .iter()
        .map(|(relative, state)| {
            let path = relative
                .to_str()
                .ok_or_else(|| format!("snapshot path is not UTF-8: {}", relative.display()))?;
            Ok(serde_json::json!({
                "bytes": state.bytes.len(),
                "path": path,
                "sha256": sha256_hex(&state.bytes),
            }))
        })
        .collect::<Result<_, String>>()?;
    let value = serde_json::json!({
        "archive": {
            "bytes": archive_state.bytes.len(),
            "members": member_values,
            "path": fs::canonicalize(archive).map_err(|e| format!("cannot canonicalize archive: {e}"))?,
            "sha256": sha256_hex(&archive_state.bytes),
        },
        "closure": {
            "modules": modules,
            "setup_sha256": sha256_hex(&setup.bytes),
            "source_files": source_files,
            "source_snapshot_sha256": source_snapshot_sha256(snapshot)?,
        },
        "manifest_sha256": sha256_hex(&manifest_state.bytes),
        "runtime": {
            "bytes": runtime_state.bytes.len(),
            "lean_toolchain": toolchain,
            "path": runtime_path,
            "sha256": sha256_hex(&runtime_state.bytes),
        },
        "schema": 1,
        "target": target,
        "tools": {
            "archiver": tool_json(archiver),
            "compiler": tool_json(compiler),
            "lake": tool_json(lake),
            "lean": tool_json(lean),
            "linker": tool_json(linker),
            "verifier_archiver": tool_json(verifier_archiver),
        },
    });
    let tools = [
        ("compiler", compiler),
        ("archiver", archiver),
        ("linker", linker),
        ("verifier_archiver", verifier_archiver),
        ("lean", lean),
        ("lake", lake),
    ];
    recheck_observation_inputs(
        repo,
        snapshot,
        setup_path,
        setup,
        archive,
        &archive_state,
        &runtime_path,
        &runtime_state,
        &manifest_path,
        &manifest_state,
        &tools,
    )?;
    let mut bytes =
        serde_json::to_vec(&value).map_err(|e| format!("cannot encode observation JSON: {e}"))?;
    bytes.push(b'\n');
    let (temporary, mut file) = create_observation_temp(&parent)?;
    file.write_all(&bytes)
        .map_err(|e| format!("cannot write {}: {e}", temporary.display()))?;
    file.sync_all()
        .map_err(|e| format!("cannot sync {}: {e}", temporary.display()))?;
    drop(file);
    // Serialization and temporary-file I/O are deliberately inside the race
    // window.  Recheck every live authority immediately before publication.
    if let Err(error) = recheck_observation_inputs(
        repo,
        snapshot,
        setup_path,
        setup,
        archive,
        &archive_state,
        &runtime_path,
        &runtime_state,
        &manifest_path,
        &manifest_state,
        &tools,
    ) {
        let temporary_rollback = fs::remove_file(&temporary);
        let directory_rollback = sync_directory(&parent);
        return Err(format!(
            "{error}; temporary rollback: {temporary_rollback:?}; rollback directory sync: \
             {directory_rollback:?}"
        ));
    }
    if let Err(error) = fs::hard_link(&temporary, output) {
        let _ = fs::remove_file(&temporary);
        return Err(format!(
            "cannot install new observation {}: {error}",
            output.display()
        ));
    }
    if let Err(error) = sync_directory(&parent) {
        return Err(rollback_observation(
            output,
            Some(&temporary),
            &parent,
            format!("cannot durably install observation: {error}"),
        ));
    }
    if let Err(error) = fs::remove_file(&temporary) {
        return Err(rollback_observation(
            output,
            Some(&temporary),
            &parent,
            format!("cannot remove temporary observation: {error}"),
        ));
    }
    if let Err(error) = sync_directory(&parent) {
        return Err(rollback_observation(
            output,
            None,
            &parent,
            format!("cannot durably remove temporary observation: {error}"),
        ));
    }
    Ok(())
}

#[allow(clippy::too_many_arguments)]
fn recheck_observation_inputs(
    repo: &Path,
    snapshot: &SourceSnapshot,
    setup_path: &Path,
    setup: &FileState,
    archive: &Path,
    archive_state: &FileState,
    runtime_path: &Path,
    runtime_state: &FileState,
    manifest_path: &Path,
    manifest_state: &FileState,
    tools: &[(&str, &ToolIdentity)],
) -> Result<(), String> {
    if snapshot_inputs(repo)? != *snapshot {
        return Err("source generation changed while the observation was assembled".into());
    }
    if stable_file_state(setup_path)? != *setup {
        return Err("RuntimeInit setup changed while the observation was assembled".into());
    }
    if stable_file_state(archive)? != *archive_state {
        return Err("runtime archive changed while the observation was assembled".into());
    }
    if stable_file_state(runtime_path)? != *runtime_state {
        return Err("Lean runtime changed while the observation was assembled".into());
    }
    if stable_file_state(manifest_path)? != *manifest_state {
        return Err("Ledger-2 manifest changed while the observation was assembled".into());
    }
    for (role, identity) in tools {
        let state = stable_file_state(&identity.path)?;
        if sha256_hex(&state.bytes) != identity.sha256 {
            return Err(format!(
                "selected {role} executable changed while the observation was assembled"
            ));
        }
    }
    Ok(())
}

fn rollback_observation(
    output: &Path,
    temporary: Option<&Path>,
    parent: &Path,
    reason: String,
) -> String {
    let output_rollback = fs::remove_file(output);
    let temporary_rollback = temporary.map(fs::remove_file);
    let directory_rollback = sync_directory(parent);
    format!(
        "{reason}; output rollback: {output_rollback:?}; temporary rollback: \
         {temporary_rollback:?}; rollback directory sync: {directory_rollback:?}"
    )
}

fn create_observation_temp(parent: &Path) -> Result<(PathBuf, fs::File), String> {
    for attempt in 0..128_u32 {
        let path = parent.join(format!(
            ".uwueave-ledger2-observation-{}-{attempt}.tmp",
            std::process::id()
        ));
        match fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&path)
        {
            Ok(file) => return Ok((path, file)),
            Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
            Err(error) => return Err(format!("cannot create {}: {error}", path.display())),
        }
    }
    Err("cannot reserve a unique observation temporary after 128 attempts".into())
}

fn sync_directory(path: &Path) -> Result<(), String> {
    fs::File::open(path)
        .and_then(|directory| directory.sync_all())
        .map_err(|error| {
            format!(
                "cannot sync observation directory {}: {error}",
                path.display()
            )
        })
}

fn observation_output_parent(output: &Path) -> Result<PathBuf, String> {
    if !output.is_absolute() {
        return Err(format!(
            "observation output is not absolute: {}",
            output.display()
        ));
    }
    match fs::symlink_metadata(output) {
        Ok(_) => {
            return Err(format!(
                "observation output already exists: {}",
                output.display()
            ))
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => return Err(format!("cannot inspect {}: {error}", output.display())),
    }
    let parent = output.parent().ok_or("observation output has no parent")?;
    let parent = fs::canonicalize(parent)
        .map_err(|e| format!("cannot canonicalize observation directory: {e}"))?;
    if output.parent() != Some(parent.as_path()) {
        return Err("observation output parent is not already canonical".into());
    }
    Ok(parent)
}

fn source_snapshot_sha256(snapshot: &SourceSnapshot) -> Result<String, String> {
    let mut bytes = b"uwueave.ledger2.source-snapshot.v1\0".to_vec();
    for (relative, state) in snapshot {
        let name = relative
            .to_str()
            .ok_or_else(|| format!("snapshot path is not UTF-8: {}", relative.display()))?
            .as_bytes();
        bytes.extend_from_slice(&(name.len() as u64).to_be_bytes());
        bytes.extend_from_slice(name);
        bytes.extend_from_slice(&(state.bytes.len() as u64).to_be_bytes());
        bytes.extend_from_slice(&state.bytes);
    }
    Ok(sha256_hex(&bytes))
}

fn sha256_hex(input: &[u8]) -> String {
    const INITIAL: [u32; 8] = [
        0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab,
        0x5be0cd19,
    ];
    const K: [u32; 64] = [
        0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4,
        0xab1c5ed5, 0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe,
        0x9bdc06a7, 0xc19bf174, 0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f,
        0x4a7484aa, 0x5cb0a9dc, 0x76f988da, 0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7,
        0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967, 0x27b70a85, 0x2e1b2138, 0x4d2c6dfc,
        0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85, 0xa2bfe8a1, 0xa81a664b,
        0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070, 0x19a4c116,
        0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
        0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7,
        0xc67178f2,
    ];
    let bit_len = (input.len() as u64).wrapping_mul(8);
    let mut padded = input.to_vec();
    padded.push(0x80);
    while padded.len() % 64 != 56 {
        padded.push(0);
    }
    padded.extend_from_slice(&bit_len.to_be_bytes());
    let mut state = INITIAL;
    for chunk in padded.chunks_exact(64) {
        let mut w = [0u32; 64];
        for (index, word) in w[..16].iter_mut().enumerate() {
            *word = u32::from_be_bytes(chunk[index * 4..index * 4 + 4].try_into().unwrap());
        }
        for index in 16..64 {
            let s0 = w[index - 15].rotate_right(7)
                ^ w[index - 15].rotate_right(18)
                ^ (w[index - 15] >> 3);
            let s1 = w[index - 2].rotate_right(17)
                ^ w[index - 2].rotate_right(19)
                ^ (w[index - 2] >> 10);
            w[index] = w[index - 16]
                .wrapping_add(s0)
                .wrapping_add(w[index - 7])
                .wrapping_add(s1);
        }
        let [mut a, mut b, mut c, mut d, mut e, mut f, mut g, mut h] = state;
        for index in 0..64 {
            let s1 = e.rotate_right(6) ^ e.rotate_right(11) ^ e.rotate_right(25);
            let choice = (e & f) ^ ((!e) & g);
            let t1 = h
                .wrapping_add(s1)
                .wrapping_add(choice)
                .wrapping_add(K[index])
                .wrapping_add(w[index]);
            let s0 = a.rotate_right(2) ^ a.rotate_right(13) ^ a.rotate_right(22);
            let majority = (a & b) ^ (a & c) ^ (b & c);
            let t2 = s0.wrapping_add(majority);
            h = g;
            g = f;
            f = e;
            e = d.wrapping_add(t1);
            d = c;
            c = b;
            b = a;
            a = t1.wrapping_add(t2);
        }
        state[0] = state[0].wrapping_add(a);
        state[1] = state[1].wrapping_add(b);
        state[2] = state[2].wrapping_add(c);
        state[3] = state[3].wrapping_add(d);
        state[4] = state[4].wrapping_add(e);
        state[5] = state[5].wrapping_add(f);
        state[6] = state[6].wrapping_add(g);
        state[7] = state[7].wrapping_add(h);
    }
    state.iter().map(|word| format!("{word:08x}")).collect()
}

fn lean_prefix(repo: &Path) -> PathBuf {
    let output = Command::new("lean")
        .arg("--print-prefix")
        .current_dir(repo)
        .output()
        .unwrap_or_else(|e| panic!("`lean --print-prefix` failed to launch: {e}"));
    if !output.status.success() {
        panic!(
            "`lean --print-prefix` failed:\n{}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let text = std::str::from_utf8(&output.stdout)
        .unwrap_or_else(|e| panic!("Lean prefix is not UTF-8: {e}"))
        .trim();
    if text.is_empty() {
        panic!("`lean --print-prefix` returned an empty path");
    }
    let prefix = PathBuf::from(text);
    if !prefix.is_absolute() || !prefix.join("include/lean/lean.h").is_file() {
        panic!(
            "Lean prefix is malformed or incomplete: {}",
            prefix.display()
        );
    }
    prefix
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::atomic::{AtomicU64, Ordering};

    static NEXT_TEST_REPO: AtomicU64 = AtomicU64::new(0);

    struct TestRepo(PathBuf);

    impl TestRepo {
        fn new() -> Self {
            let nonce = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            let serial = NEXT_TEST_REPO.fetch_add(1, Ordering::Relaxed);
            let path = std::env::temp_dir().join(format!(
                "uwueave-runtime-closure-test-{}-{nonce}-{serial}",
                std::process::id()
            ));
            fs::create_dir(&path).unwrap();
            Self(fs::canonicalize(path).unwrap())
        }

        fn artifact(&self, module: &str, ending: &str) -> PathBuf {
            let path = self
                .0
                .join("lake-owned")
                .join(module_suffix(module, ending));
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(&path, b"fixture").unwrap();
            path
        }
    }

    impl Drop for TestRepo {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }

    fn setup(imports: Value) -> Vec<u8> {
        serde_json::to_vec(&serde_json::json!({
            "plugins": [],
            "package": PACKAGE,
            "options": {},
            "name": RUNTIME_ROOT,
            "isModule": false,
            "importArts": imports,
            "dynlibs": []
        }))
        .unwrap()
    }

    #[test]
    fn query_parser_requires_exact_string_results() {
        let parsed = parse_query_paths(b"\"/a\"\n\"/b\"\n", 2).unwrap();
        assert_eq!(parsed, [PathBuf::from("/a"), PathBuf::from("/b")]);
        assert!(parse_query_paths(b"\"/a\"\n", 2).is_err());
        assert!(parse_query_paths(b"null\n", 1).is_err());
        assert!(parse_query_paths(b"\"/a\" trailing", 1).is_err());
    }

    #[test]
    fn sha256_implementation_matches_standard_vectors() {
        assert_eq!(
            sha256_hex(b""),
            "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
        );
        assert_eq!(
            sha256_hex(b"abc"),
            "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
        );
    }

    #[test]
    fn source_snapshot_hash_is_path_and_content_bound() {
        let state = |bytes: &[u8]| FileState {
            bytes: bytes.to_vec(),
            modified: None,
        };
        let mut first = SourceSnapshot::new();
        first.insert(PathBuf::from("a"), state(b"bc"));
        let mut changed_path = SourceSnapshot::new();
        changed_path.insert(PathBuf::from("ab"), state(b"c"));
        let mut changed_bytes = SourceSnapshot::new();
        changed_bytes.insert(PathBuf::from("a"), state(b"bd"));
        assert_ne!(
            source_snapshot_sha256(&first).unwrap(),
            source_snapshot_sha256(&changed_path).unwrap()
        );
        assert_ne!(
            source_snapshot_sha256(&first).unwrap(),
            source_snapshot_sha256(&changed_bytes).unwrap()
        );
    }

    #[cfg(any(target_os = "linux", target_os = "macos"))]
    #[test]
    fn stable_file_state_rejects_symlink_swap_before_descriptor_open() {
        let repo = TestRepo::new();
        let path = repo.0.join("observed");
        let moved = repo.0.join("observed-original");
        let replacement = repo.0.join("replacement");
        fs::write(&path, b"trusted generation").unwrap();
        fs::write(&replacement, b"swapped generation").unwrap();
        let result = stable_file_state_with_pre_open(&path, || {
            fs::rename(&path, &moved).unwrap();
            std::os::unix::fs::symlink(&replacement, &path).unwrap();
        });
        assert!(
            result
                .unwrap_err()
                .contains("cannot open no-follow descriptor"),
            "a final-component symlink swap must fail at descriptor acquisition"
        );
    }

    #[test]
    fn native_observation_scope_is_exact() {
        assert_eq!(
            SUPPORTED_TARGETS,
            ["aarch64-apple-darwin", "x86_64-unknown-linux-gnu"]
        );
    }

    #[test]
    fn observation_output_must_be_new_absolute_and_canonical() {
        assert!(observation_output_parent(Path::new("relative.json")).is_err());
        let repo = TestRepo::new();
        let existing = repo.0.join("existing.json");
        fs::write(&existing, b"occupied").unwrap();
        assert!(observation_output_parent(&existing).is_err());
        let fresh = repo.0.join("fresh.json");
        assert_eq!(observation_output_parent(&fresh).unwrap(), repo.0);
    }

    #[test]
    fn observation_temporary_skips_a_poisoned_pid_name() {
        let repo = TestRepo::new();
        let poisoned = repo.0.join(format!(
            ".uwueave-ledger2-observation-{}-0.tmp",
            std::process::id()
        ));
        fs::write(&poisoned, b"occupied").unwrap();
        let (selected, _file) = create_observation_temp(&repo.0).unwrap();
        assert_ne!(selected, poisoned);
    }

    #[test]
    fn malformed_and_foreign_module_names_are_rejected() {
        for bad in ["Std.Data", "Uwueave", "Uwueave.", "Uwueave.Bad-Name"] {
            assert!(validate_module_name(bad).is_err(), "accepted {bad}");
        }
        assert!(validate_module_name("Uwueave.Preo.Artifact").is_ok());
    }

    #[test]
    fn setup_rejects_missing_required_kernel_before_paths() {
        let bytes = setup(serde_json::json!({}));
        let err = closure_from_setup(&bytes, Path::new("/repo")).unwrap_err();
        assert!(err.contains("required runtime kernel"));
    }

    #[test]
    fn setup_rejects_wrong_identity_and_shape() {
        let mut value: Value = serde_json::from_slice(&setup(serde_json::json!({}))).unwrap();
        value["name"] = Value::String("Uwueave.NotRuntime".into());
        assert!(
            closure_from_setup(&serde_json::to_vec(&value).unwrap(), Path::new("/repo"))
                .unwrap_err()
                .contains("setup name")
        );

        let mut value: Value = serde_json::from_slice(&setup(serde_json::json!({}))).unwrap();
        value["importArts"] = Value::Array(vec![]);
        assert!(
            closure_from_setup(&serde_json::to_vec(&value).unwrap(), Path::new("/repo"))
                .unwrap_err()
                .contains("importArts")
        );
    }

    #[test]
    fn setup_and_object_mapping_accept_exact_closure() {
        let repo = TestRepo::new();
        let mut imports = serde_json::Map::new();
        for module in REQUIRED_KERNELS {
            imports.insert(
                module.into(),
                serde_json::json!([repo.artifact(module, ".olean")]),
            );
        }
        let modules = closure_from_setup(&setup(Value::Object(imports)), &repo.0).unwrap();
        assert_eq!(modules.len(), REQUIRED_KERNELS.len() + 1);
        assert!(modules.iter().any(|module| module == RUNTIME_ROOT));

        let objects: Vec<PathBuf> = modules
            .iter()
            .map(|module| repo.artifact(module, ".c.o.export"))
            .collect();
        validate_object_results(&modules, &objects, &repo.0).unwrap();

        let mut swapped = objects;
        swapped.swap(0, 1);
        assert!(validate_object_results(&modules, &swapped, &repo.0).is_err());
    }

    #[test]
    fn setup_rejects_foreign_or_nonmatching_artifact() {
        let repo = TestRepo::new();
        let wrong = repo.artifact("Uwueave.NotExec", ".olean");
        let bytes = setup(serde_json::json!({
            "Uwueave.Exec": [wrong],
            "Uwueave.SeqKernel": [repo.artifact("Uwueave.SeqKernel", ".olean")],
            "Uwueave.EraKernel": [repo.artifact("Uwueave.EraKernel", ".olean")],
            "Uwueave.Preo.ArtifactJournalKernel": [repo.artifact("Uwueave.Preo.ArtifactJournalKernel", ".olean")]
        }));
        assert!(closure_from_setup(&bytes, &repo.0)
            .unwrap_err()
            .contains("does not match module"));
    }
}
