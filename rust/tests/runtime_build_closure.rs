// Compile build.rs as an ordinary module so its pure setup/query validators
// run under `cargo test`; Cargo itself executes the same file as the build
// script, providing the end-to-end Lake/cc integration gate.
#![allow(dead_code)]

#[path = "../build.rs"]
mod build_script;
