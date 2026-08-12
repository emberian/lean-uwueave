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
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output};

const PACKAGE: &str = "uwueave";
const RUNTIME_ROOT: &str = "Uwueave.RuntimeInit";
const REQUIRED_KERNELS: [&str; 4] = [
    "Uwueave.Exec",
    "Uwueave.SeqKernel",
    "Uwueave.EraKernel",
    "Uwueave.Preo.ArtifactJournalKernel",
];

#[derive(Clone, Debug, Eq, PartialEq)]
struct FileState {
    bytes: Vec<u8>,
    modified: Option<std::time::SystemTime>,
}

type SourceSnapshot = BTreeMap<PathBuf, FileState>;

fn main() {
    let manifest = required_env_path("CARGO_MANIFEST_DIR");
    let repo = manifest
        .parent()
        .expect("rust crate must live directly below the repository root")
        .to_path_buf();

    guard_native_build();
    emit_rerun_inputs(&repo, &manifest);
    let before = snapshot_inputs(&repo).unwrap_or_else(|e| panic!("source snapshot failed: {e}"));

    // This broad proof gate is intentional. A targeted runtime build must not
    // let Cargo go green while some other theorem/module in the Lean library
    // is red, nor may old generated output substitute for a failed build.
    run_lake_status(&repo, &["build"], "full `lake build`");

    // Ask Lake for the root C path solely to derive the corresponding setup
    // path. No emitted filename or IR directory is guessed here.
    let root_c = query_paths(&repo, false, &[format!("+{RUNTIME_ROOT}:c")]);
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
    let objects = query_paths(&repo, false, &object_targets);
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

    let prefix = lean_prefix(&repo);
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
    cc.compile("uwueave_kernel");
    verify_archive(
        &prefix.join("bin/llvm-ar"),
        &out_dir.join("libuwueave_kernel.a"),
        &staged_objects,
    )
    .unwrap_or_else(|e| panic!("runtime archive postcondition failed: {e}"));

    // Close both TOCTOU windows. First, the entire default Lean target must
    // still be current without building. Then the root C and every selected
    // object must still be current, and Lake must return the identical paths.
    run_lake_status(
        &repo,
        &["--no-build", "build"],
        "final no-build Lean proof gate",
    );
    let mut final_targets = Vec::with_capacity(1 + object_targets.len());
    final_targets.push(format!("+{RUNTIME_ROOT}:c"));
    final_targets.extend(object_targets);
    let final_paths = query_paths(&repo, true, &final_targets);
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

fn guard_native_build() {
    let host = std::env::var("HOST").expect("Cargo did not provide HOST");
    let target = std::env::var("TARGET").expect("Cargo did not provide TARGET");
    if host != target {
        panic!(
            "cross-compilation is unsupported: Lake emitted host objects for {host}, but Cargo requested {target}"
        );
    }
    let os = std::env::var("CARGO_CFG_TARGET_OS")
        .expect("Cargo did not provide CARGO_CFG_TARGET_OS to the build script");
    if os != "macos" && os != "linux" {
        panic!("the Lean shared-runtime link contract supports native macOS and Linux, not {os}");
    }
}

fn emit_rerun_inputs(repo: &Path, manifest: &Path) {
    for path in [
        repo.join("Uwueave"),
        repo.join("Uwueave.lean"),
        repo.join("lakefile.toml"),
        repo.join("lake-manifest.json"),
        repo.join("lean-toolchain"),
        manifest.join("shim.c"),
        manifest.join("build.rs"),
        manifest.join("Cargo.toml"),
        manifest.join("Cargo.lock"),
    ] {
        println!("cargo:rerun-if-changed={}", path.display());
    }
}

fn snapshot_inputs(repo: &Path) -> Result<SourceSnapshot, String> {
    let mut paths = vec![
        repo.join("Uwueave.lean"),
        repo.join("lakefile.toml"),
        repo.join("lake-manifest.json"),
        repo.join("lean-toolchain"),
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

fn stable_file_state(path: &Path) -> Result<FileState, String> {
    let before = fs::symlink_metadata(path)
        .map_err(|e| format!("cannot inspect {}: {e}", path.display()))?;
    if before.file_type().is_symlink() || !before.is_file() {
        return Err(format!(
            "path is not a non-symlink regular file: {}",
            path.display()
        ));
    }
    let bytes = fs::read(path).map_err(|e| format!("cannot read {}: {e}", path.display()))?;
    let after = fs::symlink_metadata(path)
        .map_err(|e| format!("cannot re-inspect {}: {e}", path.display()))?;
    if after.file_type().is_symlink()
        || !after.is_file()
        || before.len() != after.len()
        || before.modified().ok() != after.modified().ok()
        || after.len() != bytes.len() as u64
    {
        return Err(format!(
            "file changed while it was read: {}",
            path.display()
        ));
    }
    Ok(FileState {
        bytes,
        modified: after.modified().ok(),
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

fn run_lake_status(repo: &Path, args: &[&str], label: &str) {
    let status = Command::new("lake")
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

fn lake_query(repo: &Path, no_build: bool, targets: &[String]) -> Output {
    let mut command = Command::new("lake");
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

fn query_paths(repo: &Path, no_build: bool, targets: &[String]) -> Vec<PathBuf> {
    let output = lake_query(repo, no_build, targets);
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
) -> Result<(), String> {
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
    for object in staged_objects {
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
    let after = stable_file_state(archive)?;
    if before != after {
        return Err("archive changed while its exact membership was verified".into());
    }
    Ok(())
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

    struct TestRepo(PathBuf);

    impl TestRepo {
        fn new() -> Self {
            let nonce = std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos();
            let path = std::env::temp_dir().join(format!(
                "uwueave-runtime-closure-test-{}-{nonce}",
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
