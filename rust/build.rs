//! Compiles the Lean-emitted C (the semantics) plus the one-file shim, and
//! links the Lean runtime. Requires a Lean toolchain (elan) on PATH — that is
//! the point of this crate's architecture: the replay semantics are *authored
//! in Lean*; Rust only wraps the compiled artifact.

use std::path::PathBuf;
use std::process::Command;

fn main() {
    let manifest = PathBuf::from(std::env::var("CARGO_MANIFEST_DIR").unwrap());
    let repo = manifest.parent().unwrap().to_path_buf();
    let ir = repo.join(".lake/build/ir");

    // Re-emit the C whenever the Lean sources change.
    println!("cargo:rerun-if-changed={}", repo.join("Uwueave").display());
    println!("cargo:rerun-if-changed={}", manifest.join("shim.c").display());

    // 1. Ask lake to (re)build the Lean library → .lake/build/ir/**/*.c
    let lake_ok = Command::new("lake")
        .arg("build")
        .current_dir(&repo)
        .status()
        .map(|s| s.success())
        .unwrap_or(false);
    // FAIL CLOSED. A previous successful build leaves `Uwueave.c` on disk, so
    // tolerating a failed `lake build` whenever that file exists would link
    // STALE semantics — a green `cargo test` reachable from a red `lake build`,
    // which is precisely the gate-that-cannot-go-red failure this project
    // audits for elsewhere. (Found by the docs/TRUST.md pass, 2026-08-11.)
    if !lake_ok {
        panic!(
            "`lake build` failed. This crate wraps Lean-compiled semantics: \
             the decision layers are authored in Lean and emitted to C, so a \
             failed Lean build means the C on disk is stale or absent and \
             linking it would ship semantics nobody proved. Install a Lean \
             toolchain (https://elan.lean-lang.org) and fix the Lean errors."
        );
    }

    // 2. Locate the Lean sysroot for headers and the runtime library.
    let prefix = Command::new("lean")
        .arg("--print-prefix")
        .output()
        .expect("`lean --print-prefix` failed — is elan installed?");
    let prefix = PathBuf::from(String::from_utf8(prefix.stdout).unwrap().trim());

    // 3. Compile every emitted module + the shim.
    let mut cc = cc::Build::new();
    cc.include(prefix.join("include"));
    cc.file(manifest.join("shim.c"));
    cc.file(ir.join("Uwueave.c"));
    // RECURSIVE, and it must be. A Lean submodule (`Uwueave/Tactics/Core.lean`)
    // emits to `ir/Uwueave/Tactics/Core.c`, one directory down; a flat
    // `read_dir` drops it and the failure is a link error at the *importers* —
    // `undefined symbol: initialize_uwueave_Uwueave_Tactics_Core` — which reads
    // like a Lean problem and is not one. Found when `Uwueave/Tactics/Core.lean`
    // became the tree's first submodule (2026-08-11).
    fn add_emitted_c(dir: &std::path::Path, cc: &mut cc::Build) {
        for entry in std::fs::read_dir(dir).expect("ir dir") {
            let p = entry.unwrap().path();
            if p.is_dir() {
                add_emitted_c(&p, cc);
            } else if p.extension().map(|e| e == "c").unwrap_or(false) {
                cc.file(&p);
            }
        }
    }
    add_emitted_c(&ir.join("Uwueave"), &mut cc);
    // Lean-emitted C is not warning-clean under default cc flags; that's fine.
    cc.warnings(false);
    cc.opt_level(2);
    cc.compile("uwueave_kernel");

    // 4. Link the Lean runtime (shared, from the toolchain).
    let libdir = prefix.join("lib/lean");
    println!("cargo:rustc-link-search=native={}", libdir.display());
    println!("cargo:rustc-link-lib=dylib=leanshared");
    // Make test/binary runs find libleanshared without LD_LIBRARY_PATH.
    println!("cargo:rustc-link-arg=-Wl,-rpath,{}", libdir.display());
}
