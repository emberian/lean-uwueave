#!/usr/bin/env python3
"""Adversarial tests for scripts/ledger2-gate.py."""

from __future__ import annotations

import hashlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


REPO = Path(__file__).resolve().parents[1]
sys.dont_write_bytecode = True
SPEC = importlib.util.spec_from_file_location("ledger2_gate", REPO / "scripts/ledger2-gate.py")
assert SPEC and SPEC.loader
gate = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(gate)


def canonical(value: object) -> bytes:
    return (json.dumps(value, ensure_ascii=False, allow_nan=False,
                       sort_keys=True, separators=(",", ":")) + "\n").encode()


class Fixture:
    def __init__(self) -> None:
        self.original_prior_pins = dict(gate.PINNED_PRIOR_IDENTITIES)
        self.temporary = tempfile.TemporaryDirectory(prefix="uwueave-ledger2-test-")
        self.root = Path(self.temporary.name)
        files = [
            ".github/workflows/ci.yml", "README.md", "RELEASE.md",
            "Uwueave.lean", "lakefile.toml",
            "lake-manifest.json", "lean-toolchain", "rust/build.rs",
            "rust/Cargo.toml", "rust/Cargo.lock", "rust/shim.c",
            "docs/TRUST.md", "docs/RUNTIME.md", "docs/COHERENCE.md",
            "docs/MAP.md", "docs/PERFORMANCE.md", "docs/index.html",
            "docs/trust/ledger2-v1.json", "docs/debt/active.jsonl",
            "scripts/v02-policy.sh",
        ]
        for relative in files:
            source, target = REPO / relative, self.root / relative
            target.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(source, target)
        shutil.copytree(REPO / "Uwueave", self.root / "Uwueave", dirs_exist_ok=True)
        shutil.copytree(REPO / "docs/debt/closed", self.root / "docs/debt/closed")
        shutil.copytree(REPO / "tests/DebtClosures", self.root / "tests/DebtClosures")
        shutil.copytree(REPO / "rust/src", self.root / "rust/src")
        shutil.copytree(REPO / "rust/tests", self.root / "rust/tests")
        shutil.copytree(REPO / "rust/examples", self.root / "rust/examples")
        benches = REPO / "rust/benches"
        if benches.exists(): shutil.copytree(benches, self.root / "rust/benches")

    def close(self) -> None:
        gate.PINNED_PRIOR_IDENTITIES.clear()
        gate.PINNED_PRIOR_IDENTITIES.update(self.original_prior_pins)
        self.temporary.cleanup()

    def text(self, relative: str) -> str:
        return (self.root / relative).read_text(encoding="utf-8")

    def write_text(self, relative: str, text: str) -> None:
        (self.root / relative).write_text(text, encoding="utf-8")

    def active_without(self, debt_id: str) -> None:
        lines = [line for line in self.text("docs/debt/active.jsonl").splitlines()
                 if json.loads(line)["id"] != debt_id]
        self.write_text("docs/debt/active.jsonl", "\n".join(lines) + "\n")

    def receipt(self, debt_id: str, disposition: str, replacement: str | None = None) -> None:
        evidence = []
        if disposition in {"implemented", "obsolete"}:
            stem = debt_id.replace("-", "_")
            relative = f"tests/DebtClosures/{stem}.case.json"
            rust_relative = f"rust/tests/debt_{stem.lower()}.rs"
            rust_payload = (f"#[test]\nfn debt_closure_{stem.lower()}_fixture() {{}}\n").encode()
            rust_path = self.root / rust_relative
            rust_path.parent.mkdir(parents=True, exist_ok=True)
            rust_path.write_bytes(rust_payload)
            payload = canonical({"checks": [{"kind": "rust_test",
                                              "sha256": hashlib.sha256(rust_payload).hexdigest()}],
                                 "id": debt_id, "schema": 1})
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(payload)
            evidence = [{"kind": "case_manifest", "path": relative,
                         "sha256": hashlib.sha256(payload).hexdigest()}]
        value = {
            "disposition": disposition, "evidence": evidence, "id": debt_id,
            "prior_entry_sha256": "0" * 64, "prior_marker_sha256": "1" * 64,
            "rationale": "fixture", "schema": 1,
        }
        if replacement is not None: value["replacement_id"] = replacement
        gate.PINNED_PRIOR_IDENTITIES.setdefault(debt_id, ("0" * 64, "1" * 64))
        (self.root / "docs/debt/closed" / f"{debt_id}.json").write_bytes(canonical(value))


class Ledger2StaticGateTests(unittest.TestCase):
    def setUp(self) -> None:
        self.fixture = Fixture()

    def tearDown(self) -> None:
        self.fixture.close()

    def check(self) -> dict:
        return gate.check(self.fixture.root)

    def test_repository_fixture_passes(self) -> None:
        self.check()

    def test_manifest_must_be_canonical(self) -> None:
        path = self.fixture.root / "docs/trust/ledger2-v1.json"
        path.write_text(json.dumps(json.loads(path.read_text()), indent=2) + "\n")
        with self.assertRaisesRegex(gate.GateError, "not canonical"):
            self.check()

    def test_manifest_cannot_drop_a_release_surface(self) -> None:
        path = self.fixture.root / "docs/trust/ledger2-v1.json"
        manifest = json.loads(path.read_text())
        del manifest["documentation"]["live_surfaces"]["RELEASE.md"]
        path.write_bytes(canonical(manifest))
        with self.assertRaisesRegex(gate.GateError, "release/historical surface drift"):
            self.check()

    def test_manifest_cannot_weaken_native_nonclaims(self) -> None:
        path = self.fixture.root / "docs/trust/ledger2-v1.json"
        manifest = json.loads(path.read_text())
        manifest["native"]["nonclaims"] = []
        path.write_bytes(canonical(manifest))
        with self.assertRaisesRegex(gate.GateError, "archive rule/nonclaims drift"):
            self.check()

    def test_manifest_cannot_reclassify_a_premise(self) -> None:
        path = self.fixture.root / "docs/trust/ledger2-v1.json"
        manifest = json.loads(path.read_text())
        row = next(row for row in manifest["ledger"]["rows"] if row["id"] == "U-0162")
        row.update({"class": "obligation", "marker": "UNDONE", "severity": "P1"})
        path.write_bytes(canonical(manifest))
        with self.assertRaisesRegex(gate.GateError, "exact successor identities"):
            self.check()

    def test_native_ci_cannot_infer_architecture_from_runner_label(self) -> None:
        path = ".github/workflows/ci.yml"
        text = self.fixture.text(path).replace(
            "target: aarch64-apple-darwin", "target: x86_64-apple-darwin", 1)
        self.fixture.write_text(path, text)
        with self.assertRaisesRegex(gate.GateError, "native workflow fragment absent"):
            self.check()

    def test_native_ci_job_cannot_be_disabled(self) -> None:
        path = ".github/workflows/ci.yml"
        text = self.fixture.text(path).replace(
            "  native:\n", "  native:\n    if: false\n", 1)
        self.fixture.write_text(path, text)
        with self.assertRaisesRegex(gate.GateError, "may not be conditional"):
            self.check()

    def test_native_ci_spaced_conditional_key_is_rejected(self) -> None:
        path = ".github/workflows/ci.yml"
        text = self.fixture.text(path).replace(
            "  native:\n", "  native:\n    if : false\n", 1)
        self.fixture.write_text(path, text)
        with self.assertRaisesRegex(gate.GateError, "may not be conditional"):
            self.check()

    def test_native_ci_early_success_is_rejected(self) -> None:
        path = ".github/workflows/ci.yml"
        text = self.fixture.text(path).replace(
            "        run: |\n          set -euo pipefail",
            "        run: |\n          exit 0\n          set -euo pipefail", 1)
        self.fixture.write_text(path, text)
        with self.assertRaisesRegex(gate.GateError, "early-success bypass"):
            self.check()

    def test_policy_cannot_drop_ledger2_adversarial_tests(self) -> None:
        path = "scripts/v02-policy.sh"
        text = self.fixture.text(path).replace(
            "python3 tests/ledger2_gate_test.py", "true # fixture removed tests", 1)
        self.fixture.write_text(path, text)
        with self.assertRaisesRegex(gate.GateError, "policy fragment absent"):
            self.check()

    def test_policy_early_success_is_rejected(self) -> None:
        path = "scripts/v02-policy.sh"
        text = self.fixture.text(path).replace(
            "set -euo pipefail", "set -euo pipefail\nexit 0", 1)
        self.fixture.write_text(path, text)
        with self.assertRaisesRegex(gate.GateError, "early-success bypass"):
            self.check()

    def test_semantically_inert_ci_drift_is_rejected_by_exact_pin(self) -> None:
        path = ".github/workflows/ci.yml"
        self.fixture.write_text(path, self.fixture.text(path) + "\n# unreviewed fixture drift\n")
        with self.assertRaisesRegex(gate.GateError, "exact executable enforcement bytes"):
            self.check()

    def test_semantically_inert_policy_drift_is_rejected_by_exact_pin(self) -> None:
        path = "scripts/v02-policy.sh"
        self.fixture.write_text(path, self.fixture.text(path) + "\n# unreviewed fixture drift\n")
        with self.assertRaisesRegex(gate.GateError, "exact executable enforcement bytes"):
            self.check()

    def test_premise_cannot_be_paid(self) -> None:
        self.fixture.active_without("U-0162")
        self.fixture.receipt("U-0162", "implemented")
        with self.assertRaisesRegex(gate.GateError, "premise U-0162 cannot become paid"):
            self.check()

    def test_decomposition_receipt_mapping_is_pinned(self) -> None:
        path = self.fixture.root / "docs/debt/closed/U-0056.json"
        receipt = json.loads(path.read_text())
        receipt["replacement_id"] = "U-0170"
        path.write_bytes(canonical(receipt))
        with self.assertRaisesRegex(gate.GateError, "decomposition receipt drift"):
            self.check()

    def test_obsolete_is_never_an_allowed_resolution(self) -> None:
        self.fixture.active_without("U-0161")
        self.fixture.receipt("U-0161", "obsolete")
        with self.assertRaisesRegex(gate.GateError, "cannot resolve as obsolete"):
            self.check()

    def test_active_and_closed_dual_state_is_rejected(self) -> None:
        self.fixture.receipt("U-0161", "implemented")
        with self.assertRaisesRegex(gate.GateError, "both active and closed"):
            self.check()

    def test_active_registry_symlink_swap_at_descriptor_open_is_rejected(self) -> None:
        root = self.fixture.root.resolve()
        active = root / "docs/debt/active.jsonl"
        moved = root / "docs/debt/active-original.jsonl"
        replacement = root / "docs/debt/active-replacement.jsonl"
        replacement.write_bytes(active.read_bytes())
        real_open = os.open
        swapped = False

        def swap_then_open(path: object, flags: int, *args: object, **kwargs: object) -> int:
            nonlocal swapped
            if Path(path) == active and not swapped:
                swapped = True
                active.rename(moved)
                active.symlink_to(replacement)
            return real_open(path, flags, *args, **kwargs)

        with mock.patch.object(gate.os, "open", side_effect=swap_then_open), \
                self.assertRaisesRegex(gate.GateError, "cannot open regular file"):
            self.check()

    def test_implemented_receipt_requires_real_evidence(self) -> None:
        self.fixture.active_without("U-0161")
        self.fixture.receipt("U-0161", "implemented")
        path = self.fixture.root / "docs/debt/closed/U-0161.json"
        receipt = json.loads(path.read_text())
        receipt["evidence"] = []
        path.write_bytes(canonical(receipt))
        with self.assertRaisesRegex(gate.GateError, "needs one evidence item"):
            self.check()

    def test_receipt_schema_boolean_is_rejected(self) -> None:
        self.fixture.active_without("U-0161")
        self.fixture.receipt("U-0161", "implemented")
        path = self.fixture.root / "docs/debt/closed/U-0161.json"
        receipt = json.loads(path.read_text())
        receipt["schema"] = True
        path.write_bytes(canonical(receipt))
        with self.assertRaisesRegex(gate.GateError, "identity/schema"):
            self.check()

    def test_receipt_rationale_control_or_padding_is_rejected(self) -> None:
        self.fixture.active_without("U-0161")
        self.fixture.receipt("U-0161", "implemented")
        path = self.fixture.root / "docs/debt/closed/U-0161.json"
        receipt = json.loads(path.read_text())
        receipt["rationale"] = " fixture\t"
        path.write_bytes(canonical(receipt))
        with self.assertRaisesRegex(gate.GateError, "malformed rationale"):
            self.check()

    def test_case_manifest_unknown_check_kind_is_rejected(self) -> None:
        self.fixture.active_without("U-0161")
        self.fixture.receipt("U-0161", "implemented")
        path = self.fixture.root / "tests/DebtClosures/U_0161.case.json"
        case = json.loads(path.read_text())
        case["checks"][0]["kind"] = "fixture"
        payload = canonical(case)
        path.write_bytes(payload)
        receipt_path = self.fixture.root / "docs/debt/closed/U-0161.json"
        receipt = json.loads(receipt_path.read_text())
        receipt["evidence"][0]["sha256"] = hashlib.sha256(payload).hexdigest()
        receipt_path.write_bytes(canonical(receipt))
        with self.assertRaisesRegex(gate.GateError, "malformed case check"):
            self.check()

    def test_current_receipt_prior_identities_are_pinned(self) -> None:
        path = self.fixture.root / "docs/debt/closed/U-0170.json"
        receipt = json.loads(path.read_text())
        receipt["prior_entry_sha256"] = "0" * 64
        path.write_bytes(canonical(receipt))
        with self.assertRaisesRegex(gate.GateError, "prior active identity drift"):
            self.check()

    def test_unpinned_receipt_without_auditable_history_is_rejected(self) -> None:
        self.fixture.active_without("U-0161")
        self.fixture.receipt("U-0161", "implemented")
        gate.PINNED_PRIOR_IDENTITIES.pop("U-0161")
        with self.assertRaisesRegex(gate.GateError, "no auditable Git history"):
            self.check()

    def test_same_class_and_severity_supersession_lineage_is_allowed(self) -> None:
        self.fixture.active_without("U-0161")
        self.fixture.receipt("U-0161", "superseded", "U-0164")
        self.check()

    def test_obligation_implemented_closure_is_allowed(self) -> None:
        self.fixture.active_without("U-0164")
        self.fixture.receipt("U-0164", "implemented")
        self.check()

    def test_umbrella_closure_does_not_skip_successor_checks(self) -> None:
        self.fixture.active_without("U-0162")
        self.fixture.receipt("U-0162", "implemented")
        with self.assertRaisesRegex(gate.GateError, "premise U-0162 cannot become paid"):
            self.check()

    def test_supersession_cycle_is_rejected(self) -> None:
        self.fixture.active_without("U-0161")
        self.fixture.active_without("U-0164")
        self.fixture.receipt("U-0161", "superseded", "U-0164")
        self.fixture.receipt("U-0164", "superseded", "U-0161")
        with self.assertRaisesRegex(gate.GateError, "supersession cycle"):
            self.check()

    def test_later_same_class_successor_id_is_allowed(self) -> None:
        self.fixture.active_without("U-0161")
        self.fixture.receipt("U-0161", "superseded", "U-0999")
        successor = {
            "acceptance": "fixture", "class": "obligation", "id": "U-0999",
            "marker_sha256": "3" * 64, "schema": 1, "severity": "P1",
            "source": "Uwueave/Gated.lean", "summary": "fixture",
        }
        path = self.fixture.root / "docs/debt/active.jsonl"
        entries = [json.loads(line) for line in path.read_text().splitlines()]
        entries.append(successor)
        entries.sort(key=lambda entry: entry["id"])
        path.write_bytes(b"".join(canonical(entry) for entry in entries))
        self.check()

    def test_cross_class_supersession_is_rejected(self) -> None:
        self.fixture.active_without("U-0162")
        self.fixture.receipt("U-0162", "superseded", "U-0164")
        with self.assertRaisesRegex(gate.GateError, "changes class/severity"):
            self.check()

    def test_umbrella_reference_loss_is_rejected(self) -> None:
        source = self.fixture.text("Uwueave/Gated.lean")
        self.fixture.write_text("Uwueave/Gated.lean", source.replace("⟨DEBT-REF U-0165⟩", "U-0165", 1))
        with self.assertRaisesRegex(gate.GateError, "references drifted"):
            self.check()

    def test_umbrella_duplicate_reference_is_rejected(self) -> None:
        source = self.fixture.text("Uwueave/Gated.lean")
        needle = "⟨DEBT-REF U-0165⟩"
        self.fixture.write_text("Uwueave/Gated.lean", source.replace(
            needle, f"{needle} {needle}", 1))
        with self.assertRaisesRegex(gate.GateError, "references drifted"):
            self.check()

    def test_runtimeinit_must_remain_data_free(self) -> None:
        path = "Uwueave/RuntimeInit.lean"
        self.fixture.write_text(path, self.fixture.text(path) + "\ndef forbidden := 1\n")
        with self.assertRaisesRegex(gate.GateError, "RuntimeInit drift"):
            self.check()

    def test_source_symlink_is_rejected_by_no_follow_read(self) -> None:
        path = self.fixture.root / "Uwueave/RuntimeInit.lean"
        target = self.fixture.root / "runtime-init-fixture.lean"
        target.write_bytes(path.read_bytes())
        path.unlink()
        path.symlink_to(target)
        with self.assertRaisesRegex(gate.GateError, "cannot open regular file"):
            self.check()

    def test_fake_exports_and_unsafe_tokens_in_comments_and_strings_are_ignored(self) -> None:
        lean_path = "Uwueave/RuntimeInit.lean"
        self.fixture.write_text(lean_path, self.fixture.text(lean_path) +
                                '\n-- @[export fake]\n/- @[export also_fake] -/\n')
        rust_path = "rust/src/status.rs"
        self.fixture.write_text(rust_path, self.fixture.text(rust_path) +
                                '\n// unsafe { fake(); }\nconst FAKE: &str = r#"unsafe fn nope() {}"#;\n')
        self.check()

    def test_real_unsafe_token_outside_inventory_is_rejected(self) -> None:
        path = "rust/src/status.rs"
        self.fixture.write_text(path, self.fixture.text(path) +
                                "\nfn fixture() { unsafe { core::hint::unreachable_unchecked() } }\n")
        with self.assertRaisesRegex(gate.GateError, "unsafe inventory drift"):
            self.check()

    def test_live_native_fingerprint_is_rejected(self) -> None:
        self.fixture.write_text("docs/RUNTIME.md", self.fixture.text("docs/RUNTIME.md") +
                                "\nThe closure was 1,049,544 bytes.\n")
        with self.assertRaisesRegex(gate.GateError, "stale live fingerprint"):
            self.check()

    def test_novel_live_native_count_is_rejected(self) -> None:
        self.fixture.write_text("docs/RUNTIME.md", self.fixture.text("docs/RUNTIME.md") +
                                "\nThe build has 42 Lake-owned objects.\n")
        with self.assertRaisesRegex(gate.GateError, "unstable native fingerprint pattern"):
            self.check()

    def test_stale_live_unsafe_count_is_rejected(self) -> None:
        text = self.fixture.text("docs/TRUST.md").replace("**21 unsafe blocks**", "**20 unsafe blocks**")
        self.fixture.write_text("docs/TRUST.md", text)
        with self.assertRaisesRegex(gate.GateError, "stale total unsafe count"):
            self.check()


class Ledger2ObservationTests(unittest.TestCase):
    def setUp(self) -> None:
        self.fixture = Fixture()
        self.manifest = gate.check(self.fixture.root)
        self.temp = Path(self.fixture.temporary.name) / "native"
        self.temp.mkdir()
        lean = shutil.which("lean")
        if lean is None: self.skipTest("Lean is unavailable")
        prefix = subprocess.run([lean, "--print-prefix"], check=True, capture_output=True,
                                text=True).stdout.strip()
        resolved = Path(prefix) / "bin/llvm-ar"
        if not resolved.is_file(): self.skipTest("Lean llvm-ar is unavailable")
        self.archiver = resolved.resolve()
        compiler = shutil.which("cc")
        if compiler is None: self.skipTest("cc is unavailable")
        fixture_c = self.temp / "fixture.c"
        fixture_c.write_text("typedef int uwueave_ledger2_fixture;\n")
        template_object = self.temp / "template.o"
        subprocess.run([compiler, "-c", fixture_c, "-o", template_object], check=True)
        host = (platform.system(), platform.machine().lower())
        if host == ("Darwin", "arm64"):
            self.target = "aarch64-apple-darwin"
        elif host == ("Linux", "x86_64"):
            self.target = "x86_64-unknown-linux-gnu"
        else:
            self.skipTest(f"unsupported native Ledger-2 fixture host: {host}")
        modules = sorted({self.manifest["runtime_surface"]["root"],
                          *self.manifest["runtime_surface"]["direct_imports"]})
        self.queried_modules = list(modules)
        members = []
        object_paths = []
        for index, module in enumerate(modules):
            path = self.temp / f"{index:03}-{module.replace('.', '__')}.o"
            shutil.copy2(template_object, path)
            object_paths.append(path)
            members.append({"bytes": path.stat().st_size, "kind": "lake",
                            "module": module, "name": path.name,
                            "sha256": hashlib.sha256(path.read_bytes()).hexdigest()})
        shim = self.temp / "fixture_shim.o"
        shutil.copy2(template_object, shim)
        object_paths.append(shim)
        members.append({"bytes": shim.stat().st_size, "kind": "shim", "module": None,
                        "name": shim.name,
                        "sha256": hashlib.sha256(shim.read_bytes()).hexdigest()})
        self.archive = self.temp / "libfixture.a"
        subprocess.run([self.archiver, "crs", self.archive, *object_paths], check=True)
        runtime = self.temp / "libleanshared.fixture"
        runtime.write_bytes(template_object.read_bytes())
        tool_hash = gate.sha256_file(self.archiver)
        identity = {"argv": [], "path": str(self.archiver), "sha256": tool_hash,
                    "version": gate.live_tool_version(self.archiver)}
        source_files, source_hash = gate.source_snapshot(self.fixture.root)
        self.value = {
            "archive": {"bytes": self.archive.stat().st_size, "members": members,
                        "path": str(self.archive.resolve()),
                        "sha256": hashlib.sha256(self.archive.read_bytes()).hexdigest()},
            "closure": {"modules": modules, "setup_sha256": "2" * 64,
                        "source_files": source_files,
                        "source_snapshot_sha256": source_hash},
            "manifest_sha256": gate.sha256_file(self.fixture.root / gate.MANIFEST),
            "runtime": {"bytes": runtime.stat().st_size,
                        "lean_toolchain": self.fixture.text("lean-toolchain").strip(),
                        "path": str(runtime.resolve()),
                        "sha256": hashlib.sha256(runtime.read_bytes()).hexdigest()},
            "schema": 1, "target": self.target,
            "tools": {name: dict(identity) for name in
                      ["archiver", "compiler", "lake", "lean", "linker",
                       "verifier_archiver"]},
        }
        self.value["tools"]["compiler"]["argv"] = [
            "-O2", "-I", str(self.archiver.parent.parent / "include"), "-w"
        ]
        self.authorities = {name: self.archiver for name in
                            ["archiver", "compiler", "lake", "lean", "linker",
                             "verifier_archiver"]}
        self.authorities["runtime"] = runtime.resolve()
        self.path = self.temp / "observation.json"
        self.write()

    def tearDown(self) -> None:
        self.fixture.close()

    def write(self) -> None:
        self.path.write_bytes(canonical(self.value))

    def validate(self) -> None:
        with mock.patch.object(gate, "query_runtime_setup",
                               return_value=(self.queried_modules, "2" * 64)), \
                mock.patch.object(gate, "native_authorities",
                                  return_value=self.authorities), \
                mock.patch.dict(os.environ, {"CC": str(self.archiver),
                                             "AR": str(self.archiver)}, clear=False):
            gate.validate_observation(self.fixture.root, self.manifest, self.path,
                                      self.target)

    def test_exact_observation_passes(self) -> None:
        self.validate()

    def test_runner_label_cannot_spoof_actual_target(self) -> None:
        other = ("x86_64-unknown-linux-gnu" if self.target == "aarch64-apple-darwin"
                 else "aarch64-apple-darwin")
        with self.assertRaisesRegex(gate.GateError, "expected actual supported target"):
            gate.validate_observation(self.fixture.root, self.manifest, self.path,
                                      other)

    def test_underfilled_transitive_closure_is_rejected(self) -> None:
        self.queried_modules.append("Uwueave.TransitiveFixture")
        self.queried_modules.sort()
        with self.assertRaisesRegex(gate.GateError, "differs from live RuntimeInit setup"):
            self.validate()

    def test_tool_version_spoof_is_rejected(self) -> None:
        self.value["tools"]["lean"]["version"] = "fixture lie"
        self.write()
        with self.assertRaisesRegex(gate.GateError, "version output mismatch"):
            self.validate()

    def test_noncompiler_argv_is_rejected(self) -> None:
        self.value["tools"]["lean"]["argv"] = ["--version"]
        self.write()
        with self.assertRaisesRegex(gate.GateError, "exact empty argv"):
            self.validate()

    def test_compiler_argv_must_bind_toolchain_include(self) -> None:
        self.value["tools"]["compiler"]["argv"] = ["-O2", "-I", "/tmp/spoof", "-w"]
        self.write()
        with self.assertRaisesRegex(gate.GateError, "bounded build configuration"):
            self.validate()

    def test_tool_role_spoof_is_rejected(self) -> None:
        compiler = Path(shutil.which("cc") or "").resolve()
        if compiler == self.archiver:
            self.skipTest("fixture compiler and archiver are the same path")
        self.value["tools"]["compiler"] = {
            "argv": list(self.value["tools"]["compiler"]["argv"]),
            "path": str(compiler), "sha256": gate.sha256_file(compiler),
            "version": gate.live_tool_version(compiler),
        }
        self.write()
        with self.assertRaisesRegex(gate.GateError, "not the authoritative selected tool"):
            self.validate()

    def test_target_relabel_is_rejected_by_artifact_architecture(self) -> None:
        other = ("x86_64-unknown-linux-gnu" if self.target == "aarch64-apple-darwin"
                 else "aarch64-apple-darwin")
        self.value["target"] = other
        self.write()
        with mock.patch.object(gate, "query_runtime_setup",
                               return_value=(self.queried_modules, "2" * 64)), \
                mock.patch.object(gate, "native_authorities",
                                  return_value=self.authorities), \
                mock.patch.dict(os.environ, {"CC": str(self.archiver),
                                             "AR": str(self.archiver)}, clear=False):
            with self.assertRaisesRegex(gate.GateError, "architecture does not match target"):
                gate.validate_observation(self.fixture.root, self.manifest, self.path, other)

    def test_tool_binary_mutation_is_rejected(self) -> None:
        self.value["tools"]["linker"]["sha256"] = "0" * 64
        self.write()
        with self.assertRaisesRegex(gate.GateError, "executable hash mismatch"):
            self.validate()

    def test_member_hash_mutation_is_rejected(self) -> None:
        self.value["archive"]["members"][0]["sha256"] = "0" * 64
        self.write()
        with self.assertRaisesRegex(gate.GateError, "member identity mismatch"):
            self.validate()

    def test_source_generation_mutation_is_rejected(self) -> None:
        self.fixture.write_text("Uwueave/RuntimeInit.lean",
                                self.fixture.text("Uwueave/RuntimeInit.lean") + "\n-- mutation\n")
        with self.assertRaisesRegex(gate.GateError, "source file identity list mismatch"):
            self.validate()


if __name__ == "__main__":
    unittest.main(verbosity=2)
