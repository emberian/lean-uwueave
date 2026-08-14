#!/usr/bin/env python3
"""Mutation negatives for the canonical Rust/C/Lean ABI gate."""

from __future__ import annotations

import copy
import importlib.util
from pathlib import Path
import sys
import tempfile
import unittest


REPO = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
SPEC = importlib.util.spec_from_file_location("abi_gate", REPO / "scripts/abi-gate.py")
assert SPEC and SPEC.loader
gate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gate)


class AbiGateTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls) -> None:
        cls.descriptor = gate.load_descriptor(REPO)
        cls.c_source = (REPO / "rust/shim.c").read_text(encoding="utf-8")
        cls.rust_source = (REPO / "rust/src/ffi.rs").read_text(encoding="utf-8")

    def test_repository_source_contract_passes(self) -> None:
        gate.check_source(REPO)

    def test_c_layout_mutation_is_rejected(self) -> None:
        mutated = self.c_source.replace("sizeof(shim_replay_op) == 40",
                                        "sizeof(shim_replay_op) == 41", 1)
        with self.assertRaisesRegex(gate.AbiError, "missing layout assertion"):
            gate.validate_c_surface(self.descriptor, mutated)

    def test_c_calling_signature_mutation_is_rejected(self) -> None:
        mutated = self.c_source.replace("size_t len, size_t *out_len)",
                                        "uint64_t len, size_t *out_len)", 1)
        with self.assertRaisesRegex(gate.AbiError, "shim definition drift"):
            gate.validate_c_surface(self.descriptor, mutated)

    def test_rust_calling_signature_mutation_is_rejected(self) -> None:
        mutated = self.rust_source.replace("input: *const u8, len: usize",
                                           "input: *const u8, len: u64", 1)
        with self.assertRaisesRegex(gate.AbiError, "signature drift"):
            gate.validate_rust_surface(self.descriptor, mutated)

    def test_generated_lean_prototype_arity_mutation_is_rejected(self) -> None:
        sources: dict[str, str] = {}
        for export in self.descriptor["lean_exports"]:
            parameters = ", ".join(
                f"lean_object* value_{index}" for index in range(export["arity"])
            )
            prototype = f"LEAN_EXPORT lean_object* {export['symbol']}({parameters});\n"
            definition = f"LEAN_EXPORT lean_object* {export['symbol']}({parameters}) {{}}\n"
            sources.setdefault(export["module"], "")
            sources[export["module"]] += prototype + definition
        gate.validate_lean_c_prototypes(self.descriptor, sources)
        target = self.descriptor["lean_exports"][0]
        sources[target["module"]] = sources[target["module"]].replace(
            f"{target['symbol']}(lean_object* value_0)",
            f"{target['symbol']}(lean_object* value_0, lean_object* extra)",
            1,
        )
        with self.assertRaisesRegex(gate.AbiError, "prototype drift"):
            gate.validate_lean_c_prototypes(self.descriptor, sources)

    def test_ledger_symbol_mapping_mutation_is_rejected(self) -> None:
        ledger = gate.load_json(REPO / gate.LEDGER, canonical=True)
        mutated = copy.deepcopy(self.descriptor)
        mutated["shim_functions"][0]["lean_export"] = "uwueave_era_resolve"
        with self.assertRaisesRegex(gate.AbiError, "descriptor and Ledger-2 exports differ"):
            gate.validate_ledger_mapping(mutated, ledger)

    def test_native_symbol_allowlist_parser_retains_only_defined_globals(self) -> None:
        output = """
0000000000000000 T _shim_uweave_init
                 U _lean_dec_ref
0000000000000010 t _private_helper
0000000000000020 D _unexpected_global
"""
        self.assertEqual(
            gate.parse_defined_globals(output),
            {"shim_uweave_init", "unexpected_global"},
        )

    def test_shim_ownership_release_mutation_is_rejected(self) -> None:
        mutated = self.c_source.replace("  lean_dec_ref(out);\n", "", 1)
        with tempfile.TemporaryDirectory(prefix="uwueave-abi-test-") as temporary:
            shim = Path(temporary) / "shim.c"
            shim.write_text(mutated, encoding="utf-8")
            with self.assertRaisesRegex(gate.AbiError, "copy/free path drift"):
                gate.validate_shim_ast(REPO, shim)

    def test_shim_bounds_mutation_is_rejected(self) -> None:
        mutated = self.c_source.replace("len > SIZE_MAX / 5",
                                        "len > SIZE_MAX / 6", 1)
        with tempfile.TemporaryDirectory(prefix="uwueave-abi-test-") as temporary:
            shim = Path(temporary) / "shim.c"
            shim.write_text(mutated, encoding="utf-8")
            with self.assertRaisesRegex(gate.AbiError, "bounds/index arithmetic drift"):
                gate.validate_shim_ast(REPO, shim)

    def test_shim_construction_lane_mutation_is_rejected(self) -> None:
        mutated = self.c_source.replace("ops[i].lamport", "ops[i].replica", 1)
        with tempfile.TemporaryDirectory(prefix="uwueave-abi-test-") as temporary:
            shim = Path(temporary) / "shim.c"
            shim.write_text(mutated, encoding="utf-8")
            with self.assertRaisesRegex(gate.AbiError, "bounds/index arithmetic drift"):
                gate.validate_shim_ast(REPO, shim)


if __name__ == "__main__":
    unittest.main(verbosity=2)
