//! Compiler-AST inventory for the complete Rust source surface.
//!
//! Package-level `unsafe_code` and `unsafe_op_in_unsafe_fn` lints cover every
//! Cargo target; the shipping library grants the sole narrow exception to
//! `src/ffi.rs`. This independent AST inventory binds the exact complete source
//! counts to Ledger 2's machine manifest.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};

use syn::visit::{self, Visit};

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct Counts {
    blocks: usize,
    functions: usize,
    impls: usize,
    traits: usize,
}

impl Counts {
    fn nonzero(self) -> bool {
        self.blocks != 0 || self.functions != 0 || self.impls != 0 || self.traits != 0
    }
}

impl<'ast> Visit<'ast> for Counts {
    fn visit_expr_unsafe(&mut self, node: &'ast syn::ExprUnsafe) {
        self.blocks += 1;
        visit::visit_expr_unsafe(self, node);
    }

    fn visit_item_fn(&mut self, node: &'ast syn::ItemFn) {
        self.functions += usize::from(node.sig.unsafety.is_some());
        visit::visit_item_fn(self, node);
    }

    fn visit_impl_item_fn(&mut self, node: &'ast syn::ImplItemFn) {
        self.functions += usize::from(node.sig.unsafety.is_some());
        visit::visit_impl_item_fn(self, node);
    }

    fn visit_trait_item_fn(&mut self, node: &'ast syn::TraitItemFn) {
        self.functions += usize::from(node.sig.unsafety.is_some());
        visit::visit_trait_item_fn(self, node);
    }

    fn visit_item_impl(&mut self, node: &'ast syn::ItemImpl) {
        self.impls += usize::from(node.unsafety.is_some());
        visit::visit_item_impl(self, node);
    }

    fn visit_item_trait(&mut self, node: &'ast syn::ItemTrait) {
        self.traits += usize::from(node.unsafety.is_some());
        visit::visit_item_trait(self, node);
    }
}

fn collect_rs(path: &Path, out: &mut Vec<PathBuf>) {
    if path.is_file() {
        if path.extension().and_then(|value| value.to_str()) == Some("rs") {
            out.push(path.to_path_buf());
        }
        return;
    }
    if !path.exists() {
        return;
    }
    for entry in fs::read_dir(path).expect("source directory must be readable") {
        let entry = entry.expect("source entry must be readable");
        collect_rs(&entry.path(), out);
    }
}

#[test]
fn every_rust_unsafe_ast_node_is_exactly_in_the_ffi_boundary() {
    let crate_root = Path::new(env!("CARGO_MANIFEST_DIR"));
    let repo = crate_root
        .parent()
        .expect("crate lives below repository root");
    let mut paths = Vec::new();
    for relative in ["build.rs", "src", "examples", "benches", "tests"] {
        collect_rs(&crate_root.join(relative), &mut paths);
    }
    paths.sort();
    paths.dedup();

    let mut actual = BTreeMap::new();
    for path in paths {
        let text = fs::read_to_string(&path).expect("Rust source must be UTF-8");
        let syntax = syn::parse_file(&text).unwrap_or_else(|error| {
            panic!(
                "cannot parse {} as a Rust syntax tree: {error}",
                path.display()
            )
        });
        let mut counts = Counts::default();
        counts.visit_file(&syntax);
        if counts.nonzero() {
            actual.insert(
                path.strip_prefix(repo)
                    .expect("source stays below repository")
                    .to_string_lossy()
                    .replace('\\', "/"),
                counts,
            );
        }
    }

    let expected = BTreeMap::from([(
        "rust/src/ffi.rs".to_string(),
        Counts {
            blocks: 18,
            functions: 1,
            impls: 0,
            traits: 0,
        },
    )]);
    assert_eq!(
        actual, expected,
        "the complete Rust unsafe AST surface drifted"
    );
}
