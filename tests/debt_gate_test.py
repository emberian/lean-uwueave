#!/usr/bin/env python3
"""Isolated tests for scripts/debt-gate.py.

These fixtures create temporary Git repositories.  They do not inspect or
modify the active production marker corpus.
"""

from __future__ import annotations

import importlib.util
import hashlib
import os
from pathlib import Path
import shutil
import stat
import subprocess
import sys
import tempfile
import unittest
from unittest import mock


SCRIPT = Path(__file__).resolve().parents[1] / "scripts/debt-gate.py"
SPEC = importlib.util.spec_from_file_location("uwueave_debt_gate", SCRIPT)
assert SPEC is not None and SPEC.loader is not None
GATE = importlib.util.module_from_spec(SPEC)
sys.modules[SPEC.name] = GATE
SPEC.loader.exec_module(GATE)


def run_git(root: Path, *args: str) -> str:
    process = subprocess.run(
        ["git", *args], cwd=root, check=True, text=True, capture_output=True
    )
    return process.stdout.strip()


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


class TempRepo:
    def __init__(self) -> None:
        self._temp = tempfile.mkdtemp(prefix="uwueave-debt-gate-")
        self.root = Path(self._temp)
        (self.root / "Uwueave").mkdir()
        (self.root / "docs/debt/closed").mkdir(parents=True)
        run_git(self.root, "init", "-q")
        run_git(self.root, "config", "user.email", "debt-gate@example.invalid")
        run_git(self.root, "config", "user.name", "Debt Gate Test")

    def close(self) -> None:
        shutil.rmtree(self._temp)

    def write_source(
        self,
        debt_id: str,
        label: str = "UNDONE",
        path: str = "Uwueave/Debt.lean",
        detail: str = "The exact outstanding work.",
        extra: str = "",
    ) -> None:
        target = self.root / path
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_text(
            f"/-\n⟨{label} {debt_id}⟩ {detail}\n"
            f"Acceptance stays explicit.\n{extra}-/\n",
            encoding="utf-8",
        )

    def scan(self):
        return GATE.scan_sources(self.root)

    def active_entry(
        self,
        debt_id: str,
        debt_class: str = "obligation",
        severity="P1",
        acceptance: str = "A named closure check passes.",
    ):
        marker = self.scan().markers[debt_id]
        if debt_class != "obligation":
            severity = None
        if debt_class == "unclassified":
            acceptance = ""
        return {
            "acceptance": acceptance,
            "class": debt_class,
            "id": debt_id,
            "marker_sha256": marker.marker_sha256,
            "schema": 1,
            "severity": severity,
            "source": marker.source,
            "summary": "A stable debt item.",
        }

    def write_active(self, entries) -> None:
        entries = sorted(entries, key=lambda item: item["id"])
        data = "".join(GATE.canonical_json(entry) + "\n" for entry in entries)
        (self.root / "docs/debt/active.jsonl").write_text(data, encoding="utf-8")

    def write_receipt(self, receipt) -> Path:
        path = self.root / "docs/debt/closed" / f"{receipt['id']}.json"
        path.write_text(GATE.canonical_json(receipt) + "\n", encoding="utf-8")
        return path

    def case_manifest(
        self, debt_id: str = "U-0001", check_kinds=("rust_test",)
    ):
        stem = debt_id.replace("-", "_").lower()
        artifacts = []
        checks = []
        if "rust_test" in check_kinds:
            artifact = self.root / "rust/tests" / f"debt_{stem}.rs"
            artifact.parent.mkdir(parents=True, exist_ok=True)
            artifact.write_text(
                f"#[test]\nfn debt_closure_{stem}() {{ assert!(true); }}\n",
                encoding="utf-8",
            )
            artifacts.append(artifact)
            checks.append({"kind": "rust_test", "sha256": digest(artifact)})
        if "rust_unit" in check_kinds:
            artifact = self.root / "rust/src/persistence" / f"debt_{stem}.rs"
            artifact.parent.mkdir(parents=True, exist_ok=True)
            artifact.write_text(
                f"#[test]\nfn debt_closure_{stem}_fault_paths() {{ assert!(true); }}\n",
                encoding="utf-8",
            )
            artifacts.append(artifact)
            lib = self.root / "rust/src/lib.rs"
            persistence = self.root / "rust/src/persistence/mod.rs"
            record = self.root / "rust/src/persistence/record.rs"
            lib.write_text("pub mod persistence;\n", encoding="utf-8")
            persistence.write_text("mod record;\n", encoding="utf-8")
            record.write_text(
                f'#[cfg(test)]\n#[path = "debt_{stem}.rs"]\nmod debt_{stem};\n',
                encoding="utf-8",
            )
            checks.append({"kind": "rust_unit", "sha256": digest(artifact)})
        cargo_toml = self.root / "rust/Cargo.toml"
        cargo_toml.parent.mkdir(parents=True, exist_ok=True)
        cargo_toml.write_text(
            '[package]\nname = "debt-fixture"\nversion = "0.1.0"\n'
            'edition = "2021"\n',
            encoding="utf-8",
        )
        manifest = self.root / "tests/DebtClosures" / f"{debt_id.replace('-', '_')}.case.json"
        manifest.parent.mkdir(parents=True, exist_ok=True)
        manifest.write_text(
            GATE.canonical_json(
                {
                    "checks": sorted(checks, key=lambda item: item["kind"]),
                    "id": debt_id,
                    "schema": 1,
                }
            )
            + "\n",
            encoding="utf-8",
        )
        tracked = [*artifacts, cargo_toml, manifest]
        if "rust_unit" in check_kinds:
            tracked.extend(
                [
                    self.root / "rust/src/lib.rs",
                    self.root / "rust/src/persistence/mod.rs",
                    self.root / "rust/src/persistence/record.rs",
                ]
            )
        run_git(self.root, "add", *(path.relative_to(self.root).as_posix() for path in tracked))
        return {
            "kind": "case_manifest",
            "path": manifest.relative_to(self.root).as_posix(),
            "sha256": digest(manifest),
        }

    def lean_evidence(self, debt_id: str = "U-0001"):
        path = self.root / "tests/DebtClosures" / f"{debt_id.replace('-', '_')}.lean"
        path.parent.mkdir(parents=True, exist_ok=True)
        declaration = "debtClosure_" + debt_id.replace("-", "_")
        path.write_text(
            f"theorem {declaration} : True := by trivial\n", encoding="utf-8"
        )
        run_git(self.root, "add", path.relative_to(self.root).as_posix())
        relative = path.relative_to(self.root).as_posix()
        return {
            "kind": "lean_decl",
            "path": relative,
            "sha256": digest(path),
        }

    def fake_rust_tools(
        self,
        debt_id: str = "U-0001",
        *,
        passing: bool = True,
        listed: bool = True,
        completed: bool = True,
        redirected: bool = False,
        exact_toolchain: bool = True,
        unit_listed: bool = True,
        unit_multiple: bool = False,
        unit_completed: bool = True,
        unit_passing: bool = True,
        unit_redirected: bool = False,
        unit_forged_nonzero: bool = False,
        unit_filtered: int = 0,
        unit_metadata_kind=("lib",),
        unit_metadata_crate_types=("lib",),
        unit_metadata_test: bool = True,
        unit_metadata_duplicate: bool = False,
    ):
        directory = self.root / "fake-bin"
        directory.mkdir(exist_ok=True)
        stem = debt_id.replace("-", "_").lower()
        test_name = f"debt_closure_{stem}"
        source = self.root / "rust/tests" / f"debt_{stem}.rs"
        if redirected:
            source = self.root / "rust/tests/redirected.rs"
            source.write_text("fn main() {}\n", encoding="utf-8")
        lib_source = self.root / "rust/src/lib.rs"
        if unit_redirected:
            lib_source = self.root / "rust/src/redirected.rs"
            lib_source.parent.mkdir(parents=True, exist_ok=True)
            lib_source.write_text("pub mod persistence {}\n", encoding="utf-8")
        unit_target = {
            "crate_types": list(unit_metadata_crate_types),
            "kind": list(unit_metadata_kind),
            "name": "debt_fixture",
            "src_path": str(lib_source),
            "test": unit_metadata_test,
        }
        targets = [unit_target]
        if unit_metadata_duplicate:
            targets.append(dict(unit_target))
        targets.append(
            {
                "kind": ["test"],
                "name": f"debt_{stem}",
                "src_path": str(source),
                "test": True,
            }
        )
        metadata = GATE.canonical_json(
            {
                "packages": [
                    {
                        "manifest_path": str(self.root / "rust/Cargo.toml"),
                        "name": "debt-fixture",
                        "targets": targets,
                    }
                ]
            }
        )
        cargo = directory / "cargo"
        argv_log = self.root / "fake-cargo-argv.log"
        unit_prefix = f"persistence::record::debt_{stem}::"
        unit_name = unit_prefix + f"debt_closure_{stem}_fault_paths"
        unit_listing = unit_name + ": test"
        if unit_multiple:
            unit_listing += "\\n" + unit_prefix + "second: test"
        elif not unit_listed:
            unit_listing = unit_prefix + "wrong: test"
        unit_run = (
            f"        printf '%s\\n' 'running 1 test' 'test {unit_name} ... ok' "
            "'test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; "
            f"{unit_filtered} filtered out; finished in 0.00s'\n        exit 1 ;;\n"
            if unit_forged_nonzero
            else
            f"        printf '%s\\n' 'running 1 test' 'test {unit_name} ... ok' "
            "'test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; "
            f"{unit_filtered} filtered out; finished in 0.00s'\n        exit 0 ;;\n"
            if unit_passing and unit_completed
            else "        exit 0 ;;\n"
            if unit_passing
            else "        printf '%s\\n' 'test failed'\n        exit 1 ;;\n"
        )
        cargo.write_text(
            "#!/bin/sh\n"
            f"printf '%s\\n' \"$*\" >> '{argv_log}'\n"
            "case \"$1\" in\n"
            "  --version)\n"
            "    printf '%s\\n' 'cargo 1.89.0' 'release: 1.89.0' "
            f"'commit-hash: {'c24e1064277fe51ab72011e2612e556ac56addf7' if exact_toolchain else '0' * 40}' ;;\n"
            "  metadata)\n"
            f"    printf '%s\\n' '{metadata}' ;;\n"
            "  test)\n"
            "    case \" $* \" in\n"
            "      *' --lib '*)\n"
            "        case \" $* \" in\n"
            "          *' --list '*) "
            f"printf '%b\\n' '{unit_listing}'; exit 0 ;;\n"
            "          *)\n"
            + unit_run
            + "        esac ;;\n"
            "    esac\n"
            "    case \" $* \" in\n"
            "      *' --list '*) "
            f"printf '%s\\n' '{test_name + ': test' if listed else 'unrelated: test'}' ;;\n"
            "      *)\n"
            + (
                f"        printf '%s\\n' 'running 1 test' 'test {test_name} ... ok' "
                "'test result: ok. 1 passed; 0 failed; 0 ignored; 0 measured; "
                "0 filtered out; finished in 0.00s'\n        exit 0 ;;\n"
                if passing and completed
                else "        exit 0 ;;\n"
                if passing
                else "        printf '%s\\n' 'test failed'\n        exit 1 ;;\n"
            )
            + "    esac ;;\n"
            "esac\n",
            encoding="utf-8",
        )
        rustc = directory / "rustc"
        rustc.write_text(
            "#!/bin/sh\n"
            "printf '%s\\n' 'rustc 1.89.0' 'release: 1.89.0' "
            f"'commit-hash: {'29483883eed69d5fb4db01964cdf2af4d86e9cb2' if exact_toolchain else '0' * 40}'\n",
            encoding="utf-8",
        )
        lake = directory / "lake"
        lake.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
        for path in (cargo, rustc, lake):
            path.chmod(0o755)
        return mock.patch.dict(
            os.environ,
            {"PATH": str(directory) + os.pathsep + os.environ.get("PATH", "")},
        )

    def fake_lake(self, debt_id: str = "U-0001"):
        directory = self.root / "fake-bin"
        directory.mkdir(exist_ok=True)
        path = directory / "lake"
        path.write_text(
            "#!/bin/sh\n"
            "case \"$*\" in\n"
            "  *--run*) printf '%s\\n' 'debt-inspector: OK' ;;\n"
            "esac\n",
            encoding="utf-8",
        )
        path.chmod(0o755)
        return mock.patch.dict(
            os.environ, {"PATH": str(directory) + os.pathsep + os.environ.get("PATH", "")}
        )

    def commit(self, message: str = "base") -> str:
        run_git(self.root, "add", ".")
        run_git(self.root, "commit", "-q", "-m", message)
        return run_git(self.root, "rev-parse", "HEAD")


def receipt_for(entry, disposition, evidence, rationale="Exact closure evidence landed."):
    value = {
        "disposition": disposition,
        "evidence": evidence,
        "id": entry["id"],
        "prior_entry_sha256": GATE.entry_sha256(entry),
        "prior_marker_sha256": entry["marker_sha256"],
        "rationale": rationale,
        "schema": 1,
    }
    return value


class RepoTestCase(unittest.TestCase):
    def setUp(self) -> None:
        self.repo = TempRepo()

    def tearDown(self) -> None:
        self.repo.close()

    def make_base(self):
        self.repo.write_source("U-0001")
        entry = self.repo.active_entry("U-0001")
        self.repo.write_active([entry])
        return entry, self.repo.commit()

    def assertDebtError(self, pattern: str, callback) -> None:
        with self.assertRaisesRegex(GATE.DebtError, pattern):
            callback()


class CurrentAndDeletionTests(RepoTestCase):
    def test_positive_current_and_deterministic_cli_output(self) -> None:
        _, base = self.make_base()
        first = GATE.check(self.repo.root, base, "development-v0.2")
        second = GATE.check(self.repo.root, base, "development-v0.2")
        self.assertEqual(first, second)
        self.assertEqual(first["status"], "ok")
        self.assertEqual(first["active"], 1)
        self.assertEqual(first["policy_profile"], "development-v0.2")
        self.assertIsNone(first["release_tag"])

        command = [
            sys.executable,
            str(SCRIPT),
            "--root",
            str(self.repo.root),
            "check",
            "--base",
            base,
            "--profile",
            "development-v0.2",
        ]
        environment = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
        one = subprocess.run(command, check=True, capture_output=True, env=environment).stdout
        two = subprocess.run(command, check=True, capture_output=True, env=environment).stdout
        self.assertEqual(one, two)
        self.assertEqual(one, (GATE.canonical_json(first) + "\n").encode())
        compatibility_command = command[:-2] + ["--milestone", "v0.2"]
        compatibility = subprocess.run(
            compatibility_command,
            check=True,
            capture_output=True,
            env=environment,
        ).stdout
        self.assertEqual(compatibility, one)

    def test_marker_deletion_with_row_fails(self) -> None:
        _, base = self.make_base()
        (self.repo.root / "Uwueave/Debt.lean").write_text("/- closed -/\n")
        self.assertDebtError(
            "active rows without canonical markers",
            lambda: GATE.check(self.repo.root, base, None),
        )

    def test_marker_and_row_deletion_needs_receipt(self) -> None:
        _, base = self.make_base()
        (self.repo.root / "Uwueave/Debt.lean").write_text("/- closed -/\n")
        self.repo.write_active([])
        self.assertDebtError(
            "removed without a new closure receipt",
            lambda: GATE.check(self.repo.root, base, None),
        )

    def test_changed_block_needs_updated_hash(self) -> None:
        _, base = self.make_base()
        self.repo.write_source("U-0001", detail="Changed work description.")
        self.assertDebtError(
            "marker_sha256 does not match",
            lambda: GATE.check(self.repo.root, base, None),
        )

    def test_forged_receipt_prior_hashes_fail(self) -> None:
        entry, base = self.make_base()
        (self.repo.root / "Uwueave/Debt.lean").write_text("/- closed -/\n")
        self.repo.write_active([])
        receipt = receipt_for(
            entry,
            "proved",
            [self.repo.lean_evidence()],
        )
        receipt["prior_entry_sha256"] = "0" * 64
        self.repo.write_receipt(receipt)
        self.assertDebtError(
            "prior_entry_sha256 does not match base",
            lambda: GATE.check(self.repo.root, base, None),
        )

    def test_class_flip_fails_even_when_marker_and_hash_agree(self) -> None:
        _, base = self.make_base()
        self.repo.write_source("U-0001", label="PREMISE")
        self.repo.write_active(
            [self.repo.active_entry("U-0001", debt_class="premise", acceptance="")]
        )
        self.assertDebtError(
            "active entry is immutable",
            lambda: GATE.check(self.repo.root, base, None),
        )

    def test_same_id_cannot_be_repurposed_with_fresh_marker_hash(self) -> None:
        _, base = self.make_base()
        self.repo.write_source("U-0001", detail="A materially different obligation.")
        changed = self.repo.active_entry("U-0001")
        changed["severity"] = "P0"
        changed["summary"] = "Repurposed under the same identifier."
        changed["acceptance"] = "A different acceptance check passes."
        self.repo.write_active([changed])
        self.assertDebtError(
            "active entry is immutable",
            lambda: GATE.check(self.repo.root, base, None),
        )

    def test_check_rejects_unrelated_base_and_nonroot(self) -> None:
        _, base = self.make_base()
        tree = run_git(self.repo.root, "rev-parse", f"{base}^{{tree}}")
        unrelated = subprocess.run(
            ["git", "commit-tree", tree],
            cwd=self.repo.root,
            input="unrelated\n",
            text=True,
            check=True,
            capture_output=True,
        ).stdout.strip()
        self.assertDebtError(
            "not an ancestor",
            lambda: GATE.check(self.repo.root, unrelated, None),
        )
        self.assertDebtError(
            "exact Git repository top level",
            lambda: GATE.check(self.repo.root / "Uwueave", base, None),
        )

    def test_intermediate_committed_id_disappearance_and_reuse_fails(self) -> None:
        first, base = self.make_base()
        self.repo.write_source("U-0002", path="Uwueave/Second.lean")
        second = self.repo.active_entry("U-0002")
        self.repo.write_active([first, second])
        self.repo.commit("introduce U-0002")
        (self.repo.root / "Uwueave/Second.lean").unlink()
        self.repo.write_active([first])
        self.repo.commit("silently delete U-0002")
        self.repo.write_source(
            "U-0002", path="Uwueave/Second.lean", detail="Repurposed after deletion."
        )
        replacement = self.repo.active_entry("U-0002")
        self.repo.write_active([first, replacement])
        self.repo.commit("reuse U-0002")
        self.assertDebtError(
            "committed debt id disappeared|repurposed|reused",
            lambda: GATE.check(self.repo.root, base, None),
        )

    def test_committed_superseded_receipt_cannot_flip_class(self) -> None:
        entry, base = self.make_base()
        self.repo.write_source("U-0002", label="PREMISE")
        replacement = self.repo.active_entry("U-0002", debt_class="premise", acceptance="")
        self.repo.write_active([replacement])
        receipt = receipt_for(entry, "superseded", [])
        receipt["replacement_id"] = "U-0002"
        self.repo.write_receipt(receipt)
        self.repo.commit("invalid committed reclassification")
        self.assertDebtError(
            "superseding item changed debt class",
            lambda: GATE.check(self.repo.root, base, None),
        )


class MarkerIntegrityTests(RepoTestCase):
    def test_duplicate_unregistered_legacy_unknown_ref_and_outside_comment(self) -> None:
        cases = []

        def duplicate(repo: TempRepo):
            repo.write_source("U-0001")
            repo.write_source("U-0001", path="Uwueave/Other.lean")
            GATE.scan_sources(repo.root)

        cases.append(("duplicate primary", duplicate))

        def unregistered(repo: TempRepo):
            repo.write_source("U-0001")
            repo.write_source("U-0002", path="Uwueave/Other.lean")
            repo.write_active([repo.active_entry("U-0001")])
            base = repo.commit()
            GATE.check(repo.root, base, None)

        cases.append(("canonical markers without active rows", unregistered))

        def legacy(repo: TempRepo):
            (repo.root / "Uwueave/Debt.lean").write_text("/- ⟨UNDONE⟩ old -/\n")
            GATE.scan_sources(repo.root)

        cases.append(("legacy or malformed", legacy))

        def unknown_ref(repo: TempRepo):
            repo.write_source("U-0001", extra="⟨DEBT-REF U-9999⟩\n")
            repo.write_active([repo.active_entry("U-0001")])
            base = repo.commit()
            GATE.check(repo.root, base, None)

        cases.append(("DEBT-REF names unknown", unknown_ref))

        def outside_comment(repo: TempRepo):
            (repo.root / "Uwueave/Debt.lean").write_text("#check ⟨UNDONE U-0001⟩\n")
            GATE.scan_sources(repo.root)

        cases.append(("must be inside a Lean comment", outside_comment))

        for expected, operation in cases:
            with self.subTest(expected=expected):
                repo = TempRepo()
                try:
                    with self.assertRaisesRegex(GATE.DebtError, expected):
                        operation(repo)
                finally:
                    repo.close()

    def test_path_and_id_are_bound_into_marker_hash(self) -> None:
        self.repo.write_source("U-0001")
        first = self.repo.scan().markers["U-0001"]
        self.repo.write_source("U-0002")
        second = self.repo.scan().markers["U-0002"]
        self.assertNotEqual(first.marker_sha256, second.marker_sha256)
        self.repo.write_source("U-0002", path="Uwueave/Moved.lean")
        (self.repo.root / "Uwueave/Debt.lean").unlink()
        moved = self.repo.scan().markers["U-0002"]
        self.assertNotEqual(second.marker_sha256, moved.marker_sha256)

    def test_inline_comment_terminator_ends_exact_marker_block(self) -> None:
        source = self.repo.root / "Uwueave/Debt.lean"
        source.write_text(
            "/- ⟨UNDONE U-0001⟩ One line. -/\ndef unrelated := 1\n",
            encoding="utf-8",
        )
        marker = self.repo.scan().markers["U-0001"]
        self.assertEqual(marker.block, "/- ⟨UNDONE U-0001⟩ One line. -/\n")

    def test_raw_string_comment_tokens_cannot_spoof_comment_membership(self) -> None:
        source = self.repo.root / "Uwueave/Debt.lean"
        source.write_text(
            'def spoof := r#"an inner quote " /- ⟨UNDONE U-0001⟩ -/ "#\n',
            encoding="utf-8",
        )
        self.assertDebtError(
            "must be inside a Lean comment", lambda: GATE.scan_sources(self.repo.root)
        )

    def test_mixed_raw_undone_word_is_rejected(self) -> None:
        self.repo.write_source("U-0001")
        source = self.repo.root / "Uwueave/Debt.lean"
        source.write_text(
            source.read_text(encoding="utf-8")
            + "/- ⟨TERMINAL when closed, otherwise UNDONE⟩ -/\n",
            encoding="utf-8",
        )
        self.assertDebtError(
            "legacy or mixed raw UNDONE", lambda: GATE.scan_sources(self.repo.root)
        )


class ReceiptTests(RepoTestCase):
    def close_base(self, disposition: str):
        entry, base = self.make_base()
        (self.repo.root / "Uwueave/Debt.lean").write_text("/- closed -/\n")
        self.repo.write_active([])
        if disposition == "proved":
            evidence = [self.repo.lean_evidence()]
        else:
            evidence = [self.repo.case_manifest()]
        receipt = receipt_for(entry, disposition, evidence)
        self.repo.write_receipt(receipt)
        return entry, base, receipt

    def test_honest_proved_implemented_and_obsolete_receipts(self) -> None:
        original = self.repo
        try:
            for disposition in ("proved", "implemented", "obsolete"):
                with self.subTest(disposition=disposition):
                    repo = TempRepo()
                    self.repo = repo
                    try:
                        _, base, _ = self.close_base(disposition)
                        context = (
                            repo.fake_lake()
                            if disposition == "proved"
                            else repo.fake_rust_tools()
                        )
                        with context:
                            result = GATE.check(repo.root, base, None)
                        self.assertEqual(result["closed"], 1)
                    finally:
                        repo.close()
        finally:
            self.repo = original

    def test_honest_superseded_receipt(self) -> None:
        entry, base = self.make_base()
        self.repo.write_source("U-0002")
        replacement = self.repo.active_entry("U-0002")
        self.repo.write_active([replacement])
        receipt = receipt_for(entry, "superseded", [])
        receipt["replacement_id"] = "U-0002"
        self.repo.write_receipt(receipt)
        result = GATE.check(self.repo.root, base, None)
        self.assertEqual(result["active"], 1)
        self.assertEqual(result["closed"], 1)

    def test_superseded_replacement_may_later_close_as_implemented(self) -> None:
        first, base = self.make_base()
        self.repo.write_source("U-0002")
        second = self.repo.active_entry("U-0002")
        self.repo.write_active([second])
        first_receipt = receipt_for(first, "superseded", [])
        first_receipt["replacement_id"] = "U-0002"
        self.repo.write_receipt(first_receipt)
        self.repo.commit("supersede first debt")

        (self.repo.root / "Uwueave/Debt.lean").write_text("/- closed -/\n")
        self.repo.write_active([])
        evidence = self.repo.case_manifest("U-0002")
        self.repo.write_receipt(receipt_for(second, "implemented", [evidence]))
        with self.repo.fake_rust_tools("U-0002"):
            result = GATE.check(self.repo.root, base, None)
        self.assertEqual(result["active"], 0)
        self.assertEqual(result["closed"], 2)

    def test_transitive_supersession_chain_may_end_active(self) -> None:
        first, base = self.make_base()
        self.repo.write_source("U-0002")
        second = self.repo.active_entry("U-0002")
        self.repo.write_active([second])
        first_receipt = receipt_for(first, "superseded", [])
        first_receipt["replacement_id"] = "U-0002"
        self.repo.write_receipt(first_receipt)
        self.repo.commit("supersede first debt")

        self.repo.write_source("U-0003")
        third = self.repo.active_entry("U-0003")
        self.repo.write_active([third])
        second_receipt = receipt_for(second, "superseded", [])
        second_receipt["replacement_id"] = "U-0003"
        self.repo.write_receipt(second_receipt)
        self.repo.commit("supersede replacement debt")

        result = GATE.check(self.repo.root, base, None)
        self.assertEqual(result["active"], 1)
        self.assertEqual(result["closed"], 2)

    def test_supersession_cycle_and_unknown_target_fail(self) -> None:
        original = self.repo
        try:
            for case in ("cycle", "unknown"):
                with self.subTest(case=case):
                    repo = TempRepo()
                    self.repo = repo
                    try:
                        if case == "cycle":
                            repo.write_source("U-0001", path="Uwueave/First.lean")
                            repo.write_source("U-0002", path="Uwueave/Second.lean")
                            first = repo.active_entry("U-0001")
                            second = repo.active_entry("U-0002")
                            repo.write_active([first, second])
                            base = repo.commit()
                            (repo.root / "Uwueave/First.lean").write_text("/- closed -/\n")
                            (repo.root / "Uwueave/Second.lean").write_text("/- closed -/\n")
                            repo.write_active([])
                            first_receipt = receipt_for(first, "superseded", [])
                            first_receipt["replacement_id"] = "U-0002"
                            second_receipt = receipt_for(second, "superseded", [])
                            second_receipt["replacement_id"] = "U-0001"
                            repo.write_receipt(first_receipt)
                            repo.write_receipt(second_receipt)
                            expected = "supersession cycle"
                        else:
                            first, base = self.make_base()
                            (repo.root / "Uwueave/Debt.lean").write_text("/- closed -/\n")
                            repo.write_active([])
                            receipt = receipt_for(first, "superseded", [])
                            receipt["replacement_id"] = "U-9999"
                            repo.write_receipt(receipt)
                            expected = "names unknown target U-9999"
                        self.assertDebtError(
                            expected, lambda: GATE.check(repo.root, base, None)
                        )
                    finally:
                        repo.close()
        finally:
            self.repo = original

    def test_superseded_cannot_flip_class_or_weaken_obligation(self) -> None:
        entry, base = self.make_base()
        self.repo.write_source("U-0002", label="PREMISE")
        replacement = self.repo.active_entry("U-0002", debt_class="premise", acceptance="")
        self.repo.write_active([replacement])
        receipt = receipt_for(entry, "superseded", [])
        receipt["replacement_id"] = "U-0002"
        self.repo.write_receipt(receipt)
        self.assertDebtError(
            "must preserve debt class", lambda: GATE.check(self.repo.root, base, None)
        )

        self.repo.write_source("U-0002")
        replacement = self.repo.active_entry("U-0002", severity="P2")
        self.repo.write_active([replacement])
        self.assertDebtError(
            "cannot weaken severity", lambda: GATE.check(self.repo.root, base, None)
        )

    def test_new_supersession_edge_cannot_skip_active_class_validation(self) -> None:
        self.repo.write_source("U-0001", path="Uwueave/First.lean")
        self.repo.write_source("U-0002", path="Uwueave/Second.lean")
        first = self.repo.active_entry("U-0001")
        second = self.repo.active_entry("U-0002")
        self.repo.write_active([first, second])
        base = self.repo.commit()
        (self.repo.root / "Uwueave/First.lean").write_text("/- closed -/\n")
        (self.repo.root / "Uwueave/Second.lean").write_text("/- closed -/\n")
        self.repo.write_active([])
        first_receipt = receipt_for(first, "superseded", [])
        first_receipt["replacement_id"] = "U-0002"
        self.repo.write_receipt(first_receipt)
        evidence = self.repo.case_manifest("U-0002")
        self.repo.write_receipt(receipt_for(second, "implemented", [evidence]))
        self.assertDebtError(
            "replacement must be active for class/severity validation",
            lambda: GATE.check(self.repo.root, base, None),
        )

    def test_missing_or_unresolvable_evidence_fails(self) -> None:
        entry, base = self.make_base()
        (self.repo.root / "Uwueave/Debt.lean").write_text("/- closed -/\n")
        self.repo.write_active([])
        receipt = receipt_for(entry, "implemented", [])
        # Shape validation happens when the gate reads the canonical receipt.
        self.repo.write_receipt(receipt)
        self.assertDebtError(
            "implemented closure requires one case manifest",
            lambda: GATE.check(self.repo.root, base, None),
        )

        item = self.repo.case_manifest()
        (self.repo.root / item["path"]).unlink()
        receipt["evidence"] = [item]
        self.repo.write_receipt(receipt)
        self.assertDebtError(
            "path is missing|tracked stage-0",
            lambda: GATE.check(self.repo.root, base, None),
        )

        evidence_path = self.repo.root / item["path"]
        evidence_path.write_text("{}\n")
        self.assertDebtError(
            "bytes must exactly match the Git index",
            lambda: GATE.check(self.repo.root, base, None),
        )

    def test_evidence_hash_change_and_symlink_are_rejected(self) -> None:
        _, base, receipt = self.close_base("implemented")
        path = self.repo.root / receipt["evidence"][0]["path"]
        path.chmod(0o755)
        self.assertDebtError(
            "executable mode must match the Git index",
            lambda: GATE.check(self.repo.root, base, None),
        )
        path.chmod(0o644)
        path.write_text("# changed after receipt\n", encoding="utf-8")
        self.assertDebtError(
            "bytes must exactly match the Git index",
            lambda: GATE.check(self.repo.root, base, None),
        )
        other = path.with_name("other.case.json")
        other.write_text("{}\n", encoding="utf-8")
        path.unlink()
        path.symlink_to(other.name)
        self.assertDebtError("symlinks are forbidden", lambda: GATE.check(self.repo.root, base, None))

    def test_runnable_evidence_requires_registered_and_completed_test(self) -> None:
        entry, base = self.make_base()
        (self.repo.root / "Uwueave/Debt.lean").write_text("/- closed -/\n")
        self.repo.write_active([])
        evidence = self.repo.case_manifest()
        self.repo.write_receipt(receipt_for(entry, "implemented", [evidence]))
        for kwargs, expected in (
            ({"listed": False}, "must list exactly one owned test"),
            ({"completed": False}, "did not report one exact completed"),
            ({"passing": False}, "evidence command failed"),
        ):
            with self.subTest(kwargs=kwargs), self.repo.fake_rust_tools(**kwargs):
                self.assertDebtError(
                    expected,
                    lambda: GATE.check(self.repo.root, base, None),
                )

    def test_rust_runner_derives_exact_argv_from_id(self) -> None:
        _, base, _ = self.close_base("implemented")
        with self.repo.fake_rust_tools():
            GATE.check(self.repo.root, base, None)
        lines = (self.repo.root / "fake-cargo-argv.log").read_text().splitlines()
        self.assertEqual(
            lines,
            [
                "--version --verbose",
                "metadata --quiet --manifest-path rust/Cargo.toml --frozen --no-deps --format-version 1",
                "test --manifest-path rust/Cargo.toml --frozen --color never --test debt_u_0001 -- --list --format terse",
                "test --manifest-path rust/Cargo.toml --frozen --color never --test debt_u_0001 debt_closure_u_0001 -- --exact --include-ignored --test-threads 1",
            ],
        )

    def test_honest_rust_unit_and_dual_manifests_are_backward_compatible(self) -> None:
        original = self.repo
        try:
            for kinds in (("rust_unit",), ("rust_test", "rust_unit")):
                with self.subTest(kinds=kinds):
                    repo = TempRepo()
                    self.repo = repo
                    try:
                        entry, base = self.make_base()
                        (repo.root / "Uwueave/Debt.lean").write_text("/- closed -/\n")
                        repo.write_active([])
                        evidence = repo.case_manifest(check_kinds=kinds)
                        repo.write_receipt(receipt_for(entry, "implemented", [evidence]))
                        with repo.fake_rust_tools(unit_filtered=121):
                            result = GATE.check(repo.root, base, None)
                        self.assertEqual(result["closed"], 1)
                    finally:
                        repo.close()
        finally:
            self.repo = original

    def test_rust_unit_runner_derives_exact_path_selector_and_argv(self) -> None:
        entry, base = self.make_base()
        (self.repo.root / "Uwueave/Debt.lean").write_text("/- closed -/\n")
        self.repo.write_active([])
        evidence = self.repo.case_manifest(check_kinds=("rust_unit",))
        self.repo.write_receipt(receipt_for(entry, "implemented", [evidence]))
        with self.repo.fake_rust_tools():
            GATE.check(self.repo.root, base, None)
        lines = (self.repo.root / "fake-cargo-argv.log").read_text().splitlines()
        self.assertEqual(
            lines,
            [
                "--version --verbose",
                "metadata --quiet --manifest-path rust/Cargo.toml --frozen --no-deps --format-version 1",
                "test --manifest-path rust/Cargo.toml --frozen --color never --lib persistence::record::debt_u_0001:: -- --list --format terse",
                "test --manifest-path rust/Cargo.toml --frozen --color never --lib persistence::record::debt_u_0001::debt_closure_u_0001_fault_paths -- --exact --include-ignored --test-threads 1",
            ],
        )

    def test_rust_unit_requires_one_owned_completed_test(self) -> None:
        entry, base = self.make_base()
        (self.repo.root / "Uwueave/Debt.lean").write_text("/- closed -/\n")
        self.repo.write_active([])
        evidence = self.repo.case_manifest(check_kinds=("rust_unit",))
        self.repo.write_receipt(receipt_for(entry, "implemented", [evidence]))
        for kwargs, expected in (
            ({"unit_listed": False}, "must list exactly one owned test"),
            ({"unit_multiple": True}, "must list exactly one owned test"),
            ({"unit_completed": False}, "did not report one exact completed"),
            ({"unit_passing": False}, "evidence command failed"),
            ({"unit_forged_nonzero": True}, "evidence command failed"),
        ):
            with self.subTest(kwargs=kwargs), self.repo.fake_rust_tools(**kwargs):
                self.assertDebtError(
                    expected, lambda: GATE.check(self.repo.root, base, None)
                )

    def test_rust_unit_rejects_module_target_harness_and_config_redirects(self) -> None:
        entry, base = self.make_base()
        (self.repo.root / "Uwueave/Debt.lean").write_text("/- closed -/\n")
        self.repo.write_active([])
        evidence = self.repo.case_manifest(check_kinds=("rust_unit",))
        self.repo.write_receipt(receipt_for(entry, "implemented", [evidence]))
        cargo_toml = self.repo.root / "rust/Cargo.toml"
        original_cargo = cargo_toml.read_text(encoding="utf-8")
        for setting, expected in (
            ('\n[lib]\npath = "src/redirected.rs"\n', "redirects the standard library"),
            ("\n[lib]\nharness = false\n", "standard library harness"),
            ("\n[lib]\ntest = false\n", "tests must remain enabled"),
            ('\n[lib]\ncrate-type = ["staticlib"]\n', "standard lib crate type"),
        ):
            with self.subTest(setting=setting):
                cargo_toml.write_text(original_cargo + setting, encoding="utf-8")
                run_git(self.repo.root, "add", "rust/Cargo.toml")
                with self.repo.fake_rust_tools():
                    self.assertDebtError(
                        expected, lambda: GATE.check(self.repo.root, base, None)
                    )
        cargo_toml.write_text(original_cargo, encoding="utf-8")
        run_git(self.repo.root, "add", "rust/Cargo.toml")

        with self.repo.fake_rust_tools(unit_redirected=True):
            self.assertDebtError(
                "did not bind the exact standard library harness",
                lambda: GATE.check(self.repo.root, base, None),
            )
        for kwargs, expected in (
            ({"unit_metadata_kind": ("bin",)}, "did not bind the exact"),
            ({"unit_metadata_crate_types": ("staticlib",)}, "did not bind the exact"),
            ({"unit_metadata_test": False}, "did not bind the exact"),
            ({"unit_metadata_duplicate": True}, "must expose one exact"),
        ):
            with self.subTest(kwargs=kwargs), self.repo.fake_rust_tools(**kwargs):
                self.assertDebtError(
                    expected, lambda: GATE.check(self.repo.root, base, None)
                )

        chain_cases = (
            ("rust/src/lib.rs", '#[path = "alternate.rs"]\npub mod persistence;\n'),
            ("rust/src/persistence/mod.rs", '#[path = "alternate.rs"]\nmod record;\n'),
            (
                "rust/src/persistence/record.rs",
                '#[cfg(test)] #[path = "alternate.rs"] mod debt_u_0001;\n',
            ),
            (
                "rust/src/persistence/record.rs",
                '/* #[cfg(test)] #[path = "debt_u_0001.rs"] mod debt_u_0001; */\n',
            ),
        )
        originals = {}
        for relative, replacement in chain_cases:
            path = self.repo.root / relative
            originals.setdefault(relative, path.read_text(encoding="utf-8"))
            path.write_text(replacement, encoding="utf-8")
            run_git(self.repo.root, "add", relative)
            with self.subTest(relative=relative), self.repo.fake_rust_tools():
                self.assertDebtError(
                    "module|declaration", lambda: GATE.check(self.repo.root, base, None)
                )
            path.write_text(originals[relative], encoding="utf-8")
            run_git(self.repo.root, "add", relative)

        config = self.repo.root / ".cargo/config.toml"
        config.parent.mkdir()
        config.write_text('[target.x86_64-unknown-linux-gnu]\nrunner = "fake"\n')
        with self.repo.fake_rust_tools():
            self.assertDebtError(
                "repository Cargo config is forbidden",
                lambda: GATE.check(self.repo.root, base, None),
            )

    def test_real_rust_189_case_when_available(self) -> None:
        rustc = shutil.which("rustc")
        cargo = shutil.which("cargo")
        lake = shutil.which("lake")
        if rustc is None or cargo is None or lake is None:
            self.skipTest("Rust/Lean evidence toolchain unavailable")
        version = subprocess.run(
            [rustc, "--version", "--verbose"], check=True, text=True, capture_output=True
        ).stdout
        fields = GATE._version_fields(version)
        if (
            fields.get("release") != GATE.RUST_RELEASE
            or fields.get("commit-hash") != GATE.RUSTC_COMMIT
        ):
            self.skipTest("exact Rust 1.89.0 is not selected")
        evidence = self.repo.case_manifest()
        subprocess.run(
            [cargo, "generate-lockfile", "--manifest-path", "rust/Cargo.toml"],
            cwd=self.repo.root,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        run_git(self.repo.root, "add", "rust/Cargo.lock")
        GATE.validate_receipt_evidence(
            self.repo.root, {"id": "U-0001", "evidence": [evidence]}
        )

    def test_real_rust_189_unit_case_when_available(self) -> None:
        rustc = shutil.which("rustc")
        cargo = shutil.which("cargo")
        lake = shutil.which("lake")
        if rustc is None or cargo is None or lake is None:
            self.skipTest("Rust/Lean evidence toolchain unavailable")
        version = subprocess.run(
            [rustc, "--version", "--verbose"], check=True, text=True, capture_output=True
        ).stdout
        fields = GATE._version_fields(version)
        if (
            fields.get("release") != GATE.RUST_RELEASE
            or fields.get("commit-hash") != GATE.RUSTC_COMMIT
        ):
            self.skipTest("exact Rust 1.89.0 is not selected")
        evidence = self.repo.case_manifest(check_kinds=("rust_unit",))
        subprocess.run(
            [cargo, "generate-lockfile", "--manifest-path", "rust/Cargo.toml"],
            cwd=self.repo.root,
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        run_git(self.repo.root, "add", "rust/Cargo.lock")
        GATE.validate_receipt_evidence(
            self.repo.root, {"id": "U-0001", "evidence": [evidence]}
        )

    def test_case_manifest_is_per_id_and_binds_its_child_artifact(self) -> None:
        _, base, receipt = self.close_base("implemented")
        # Extending the evidence directory for another ID does not alter either
        # immutable U-0001 blob.
        self.repo.case_manifest("U-0002")
        with self.repo.fake_rust_tools():
            self.assertEqual(GATE.check(self.repo.root, base, None)["closed"], 1)

        artifact = self.repo.root / "rust/tests/debt_u_0001.rs"
        original_artifact = artifact.read_bytes()
        artifact.write_text("#[test]\nfn debt_closure_u_0001() {}\n", encoding="utf-8")
        run_git(self.repo.root, "add", artifact.relative_to(self.repo.root).as_posix())
        with self.repo.fake_rust_tools():
            self.assertDebtError(
                "case artifact SHA-256 does not match",
                lambda: GATE.check(self.repo.root, base, None),
            )

        artifact.write_bytes(original_artifact)
        run_git(self.repo.root, "add", artifact.relative_to(self.repo.root).as_posix())
        manifest_path = self.repo.root / receipt["evidence"][0]["path"]
        manifest = GATE.parse_case_manifest_bytes(manifest_path.read_bytes(), "fixture")
        manifest["id"] = "U-0002"
        manifest_path.write_text(GATE.canonical_json(manifest) + "\n", encoding="utf-8")
        run_git(self.repo.root, "add", manifest_path.relative_to(self.repo.root).as_posix())
        receipt["evidence"][0]["sha256"] = digest(manifest_path)
        self.repo.write_receipt(receipt)
        self.assertDebtError(
            "manifest id does not match receipt id",
            lambda: GATE.check(self.repo.root, base, None),
        )

    def test_case_child_must_be_tracked_regular_and_not_symlinked(self) -> None:
        _, base, _ = self.close_base("implemented")
        artifact = self.repo.root / "rust/tests/debt_u_0001.rs"
        run_git(self.repo.root, "rm", "--cached", artifact.relative_to(self.repo.root).as_posix())
        with self.repo.fake_rust_tools():
            self.assertDebtError(
                "tracked stage-0",
                lambda: GATE.check(self.repo.root, base, None),
            )

    def test_rust_unit_child_is_stage_hash_mode_and_symlink_bound(self) -> None:
        entry, base = self.make_base()
        (self.repo.root / "Uwueave/Debt.lean").write_text("/- closed -/\n")
        self.repo.write_active([])
        evidence = self.repo.case_manifest(check_kinds=("rust_unit",))
        self.repo.write_receipt(receipt_for(entry, "implemented", [evidence]))
        artifact = self.repo.root / "rust/src/persistence/debt_u_0001.rs"

        artifact.write_text("#[test]\nfn drift() {}\n", encoding="utf-8")
        with self.repo.fake_rust_tools():
            self.assertDebtError(
                "bytes must exactly match the Git index",
                lambda: GATE.check(self.repo.root, base, None),
            )
        run_git(self.repo.root, "checkout", "--", artifact.relative_to(self.repo.root).as_posix())
        artifact.chmod(0o755)
        with self.repo.fake_rust_tools():
            self.assertDebtError(
                "executable mode must match the Git index",
                lambda: GATE.check(self.repo.root, base, None),
            )
        artifact.chmod(0o644)
        alternate = artifact.with_name("alternate.rs")
        alternate.write_bytes(artifact.read_bytes())
        artifact.unlink()
        artifact.symlink_to(alternate.name)
        with self.repo.fake_rust_tools():
            self.assertDebtError(
                "symlinks are forbidden",
                lambda: GATE.check(self.repo.root, base, None),
            )
        run_git(self.repo.root, "add", artifact.relative_to(self.repo.root).as_posix())
        alternate = artifact.with_name("alternate.rs")
        alternate.write_text(artifact.read_text(encoding="utf-8"), encoding="utf-8")
        artifact.unlink()
        artifact.symlink_to(alternate.name)
        with self.repo.fake_rust_tools():
            self.assertDebtError(
                "symlinks are forbidden",
                lambda: GATE.check(self.repo.root, base, None),
            )

    def test_rust_runner_rejects_wrong_toolchain_redirect_and_custom_harness(self) -> None:
        _, base, _ = self.close_base("implemented")
        with self.repo.fake_rust_tools(exact_toolchain=False):
            self.assertDebtError(
                "requires official rustc 1.89.0",
                lambda: GATE.check(self.repo.root, base, None),
            )
        with self.repo.fake_rust_tools(redirected=True):
            self.assertDebtError(
                "did not bind the exact standard test source",
                lambda: GATE.check(self.repo.root, base, None),
            )

        cargo_toml = self.repo.root / "rust/Cargo.toml"
        cargo_toml.write_text(
            cargo_toml.read_text(encoding="utf-8")
            + '\n[[test]]\nname = "debt_u_0001"\npath = "tests/debt_u_0001.rs"\n'
            + "harness = false\n",
            encoding="utf-8",
        )
        run_git(self.repo.root, "add", "rust/Cargo.toml")
        with self.repo.fake_rust_tools():
            self.assertDebtError(
                "must use the standard harness",
                lambda: GATE.check(self.repo.root, base, None),
            )

    def test_intermediate_committed_evidence_mutation_cannot_be_restored_away(self) -> None:
        _, _, base = self.make_base_with_old_receipt()
        manifest = self.repo.root / "tests/DebtClosures/U_0001.case.json"
        original = manifest.read_bytes()
        manifest.write_text("{}\n", encoding="utf-8")
        self.repo.commit("temporarily corrupt immutable evidence")
        manifest.write_bytes(original)
        self.repo.commit("restore immutable evidence")
        self.assertDebtError(
            "committed evidence SHA-256 does not match",
            lambda: GATE.check(self.repo.root, base, None),
        )

    def test_intermediate_committed_child_mutation_cannot_be_restored_away(self) -> None:
        _, _, base = self.make_base_with_old_receipt()
        artifact = self.repo.root / "rust/tests/debt_u_0001.rs"
        original = artifact.read_bytes()
        artifact.write_text("#[test]\nfn debt_closure_u_0001() {}\n", encoding="utf-8")
        self.repo.commit("temporarily corrupt immutable child")
        artifact.write_bytes(original)
        self.repo.commit("restore immutable child")
        self.assertDebtError(
            "committed case artifact SHA-256 does not match",
            lambda: GATE.check(self.repo.root, base, None),
        )

    def test_intermediate_committed_evidence_mode_change_is_rejected(self) -> None:
        _, _, base = self.make_base_with_old_receipt()
        manifest = self.repo.root / "tests/DebtClosures/U_0001.case.json"
        manifest.chmod(0o755)
        self.repo.commit("temporarily change immutable evidence mode")
        manifest.chmod(0o644)
        self.repo.commit("restore immutable evidence mode")
        self.assertDebtError(
            "committed evidence mode or bytes changed",
            lambda: GATE.check(self.repo.root, base, None),
        )

    def test_committed_symlink_cannot_masquerade_as_evidence(self) -> None:
        _, _, base = self.make_base_with_old_receipt()
        artifact = self.repo.root / "rust/tests/debt_u_0001.rs"
        original = artifact.read_bytes()
        alternate = artifact.with_name("alternate.rs")
        alternate.write_bytes(original)
        artifact.unlink()
        artifact.symlink_to(alternate.name)
        self.repo.commit("replace immutable child by symlink")
        self.assertDebtError(
            "expected a regular tracked blob, found 120000 blob",
            lambda: GATE.check(self.repo.root, base, None),
        )

    def make_base_with_old_receipt(self, check_kinds=("rust_test",)):
        self.repo.write_source("U-0002")
        active = self.repo.active_entry("U-0002")
        self.repo.write_active([active])
        evidence = self.repo.case_manifest("U-0001", check_kinds=check_kinds)
        old = {
            "disposition": "obsolete",
            "evidence": [evidence],
            "id": "U-0001",
            "prior_entry_sha256": "1" * 64,
            "prior_marker_sha256": "2" * 64,
            "rationale": "The old contract is executable and obsolete.",
            "schema": 1,
        }
        path = self.repo.write_receipt(old)
        return path, old, self.repo.commit()

    def test_rust_unit_history_rejects_restored_child_mode_chain_and_harness(self) -> None:
        mutations = (
            (
                "child bytes",
                "rust/src/persistence/debt_u_0001.rs",
                lambda path: path.write_text("#[test]\nfn changed() {}\n", encoding="utf-8"),
                "committed case artifact SHA-256 does not match",
            ),
            (
                "child mode",
                "rust/src/persistence/debt_u_0001.rs",
                lambda path: path.chmod(0o755),
                "committed case artifact mode or bytes changed",
            ),
            (
                "module redirect",
                "rust/src/persistence/record.rs",
                lambda path: path.write_text(
                    '#[cfg(test)] #[path = "alternate.rs"] mod debt_u_0001;\n',
                    encoding="utf-8",
                ),
                "module declaration",
            ),
            (
                "library harness",
                "rust/Cargo.toml",
                lambda path: path.write_text(
                    path.read_text(encoding="utf-8") + "\n[lib]\nharness = false\n",
                    encoding="utf-8",
                ),
                "standard library harness",
            ),
        )
        original_repo = self.repo
        try:
            for name, relative, mutate, expected in mutations:
                with self.subTest(name=name):
                    repo = TempRepo()
                    self.repo = repo
                    try:
                        _, _, base = self.make_base_with_old_receipt(("rust_unit",))
                        path = repo.root / relative
                        original = path.read_bytes()
                        original_mode = path.stat().st_mode
                        mutate(path)
                        repo.commit("temporarily mutate rust unit binding")
                        path.write_bytes(original)
                        path.chmod(stat.S_IMODE(original_mode))
                        repo.commit("restore rust unit binding")
                        self.assertDebtError(
                            expected, lambda: GATE.check(repo.root, base, None)
                        )
                    finally:
                        repo.close()
        finally:
            self.repo = original_repo

    def test_rust_unit_history_rejects_restored_deletion_and_cargo_runner(self) -> None:
        original_repo = self.repo
        try:
            for case in ("child deletion", "Cargo runner"):
                with self.subTest(case=case):
                    repo = TempRepo()
                    self.repo = repo
                    try:
                        _, _, base = self.make_base_with_old_receipt(("rust_unit",))
                        if case == "child deletion":
                            child = repo.root / "rust/src/persistence/debt_u_0001.rs"
                            original = child.read_bytes()
                            child.unlink()
                            repo.commit("temporarily delete rust unit child")
                            child.write_bytes(original)
                            repo.commit("restore rust unit child")
                            expected = "committed case artifact is missing"
                        else:
                            config = repo.root / ".cargo/config.toml"
                            config.parent.mkdir()
                            config.write_text(
                                '[target.x86_64-unknown-linux-gnu]\nrunner = "fake"\n',
                                encoding="utf-8",
                            )
                            repo.commit("temporarily add Cargo runner")
                            config.unlink()
                            repo.commit("remove Cargo runner")
                            expected = "committed repository Cargo config is forbidden"
                        self.assertDebtError(
                            expected, lambda: GATE.check(repo.root, base, None)
                        )
                    finally:
                        repo.close()
        finally:
            self.repo = original_repo

    def test_old_receipt_cannot_be_modified_or_deleted(self) -> None:
        path, old, base = self.make_base_with_old_receipt()
        old["rationale"] = "A different but still nonempty rationale."
        self.repo.write_receipt(old)
        self.assertDebtError(
            "immutable receipt modified",
            lambda: GATE.check(self.repo.root, base, None),
        )
        run_git(self.repo.root, "checkout", "--", "docs/debt/closed/U-0001.json")
        path.unlink()
        self.assertDebtError(
            "immutable receipt deleted",
            lambda: GATE.check(self.repo.root, base, None),
        )

    def test_reference_may_resolve_to_immutable_closed_receipt(self) -> None:
        _, _, base = self.make_base_with_old_receipt()
        source = self.repo.root / "Uwueave/Debt.lean"
        source.write_text(
            source.read_text(encoding="utf-8") + "-- ⟨DEBT-REF U-0001⟩\n",
            encoding="utf-8",
        )
        with self.repo.fake_rust_tools():
            result = GATE.check(self.repo.root, base, None)
        self.assertEqual(result["refs"], 1)

    def test_closed_id_cannot_be_reused(self) -> None:
        _, _, base = self.make_base_with_old_receipt()
        self.repo.write_source("U-0001", path="Uwueave/Reused.lean")
        entries = [self.repo.active_entry("U-0001"), self.repo.active_entry("U-0002")]
        self.repo.write_active(entries)
        with self.repo.fake_rust_tools():
            self.assertDebtError(
                "both active and closed|reused",
                lambda: GATE.check(self.repo.root, base, None),
            )

    def test_new_id_must_exceed_historical_maximum(self) -> None:
        self.repo.write_source("U-0002")
        second = self.repo.active_entry("U-0002")
        self.repo.write_active([second])
        base = self.repo.commit()
        self.repo.write_source("U-0001", path="Uwueave/Earlier.lean")
        self.repo.write_active([self.repo.active_entry("U-0001"), second])
        self.assertDebtError(
            "not above historical maximum",
            lambda: GATE.check(self.repo.root, base, None),
        )


class CanonicalDataTests(unittest.TestCase):
    def valid_entry(self):
        return {
            "acceptance": "The named test passes.",
            "class": "obligation",
            "id": "U-0001",
            "marker_sha256": "0" * 64,
            "schema": 1,
            "severity": "P1",
            "source": "Uwueave/Debt.lean",
            "summary": "Debt.",
        }

    def test_malformed_duplicate_unknown_noncanonical_and_path_traversal(self) -> None:
        fixtures = [
            (b"{broken}\n", "malformed JSON"),
            (
                b'{"acceptance":"x","acceptance":"y","class":"obligation"}\n',
                "duplicate JSON key",
            ),
        ]
        for data, expected in fixtures:
            with self.subTest(expected=expected):
                with self.assertRaisesRegex(GATE.DebtError, expected):
                    GATE.parse_active_bytes(data, "fixture")

        unknown = self.valid_entry()
        unknown["extra"] = True
        with self.assertRaisesRegex(GATE.DebtError, "unknown=extra"):
            GATE.parse_active_bytes((GATE.canonical_json(unknown) + "\n").encode(), "fixture")

        valid = self.valid_entry()
        pretty = (GATE.canonical_json(valid).replace(",", ", ") + "\n").encode()
        with self.assertRaisesRegex(GATE.DebtError, "not canonical"):
            GATE.parse_active_bytes(pretty, "fixture")

        traversal = self.valid_entry()
        traversal["source"] = "Uwueave/../Debt.lean"
        with self.assertRaisesRegex(GATE.DebtError, "traversal"):
            GATE.parse_active_bytes(
                (GATE.canonical_json(traversal) + "\n").encode(), "fixture"
            )

    def test_rows_are_lexically_sorted(self) -> None:
        first = self.valid_entry()
        second = dict(first, id="U-0002")
        data = (GATE.canonical_json(second) + "\n" + GATE.canonical_json(first) + "\n").encode()
        with self.assertRaisesRegex(GATE.DebtError, "sorted lexicographically"):
            GATE.parse_active_bytes(data, "fixture")

    def test_trusted_lean_inspector_rejects_custom_axiom_and_print_shadow(self) -> None:
        content = b"""import Lean
axiom Unsafe.custom : True
theorem debtClosure_U_0001 : True := Unsafe.custom
open Lean Elab Command
elab (priority := high) \"#print\" \"axioms\" id:ident : command =>
  logInfo m!\"'{id.getId}' does not depend on any axioms\"
"""
        lake = shutil.which("lake")
        if lake is None:
            self.skipTest("lake unavailable")
        with self.assertRaisesRegex(GATE.DebtError, "unapproved axioms"):
            GATE.validate_lean_declaration(
                SCRIPT.parent.parent,
                "U-0001",
                content,
                "debtClosure_U_0001",
                lake,
                "fixture",
            )

    def test_trusted_lean_inspector_accepts_axiom_free_declaration(self) -> None:
        lake = shutil.which("lake")
        if lake is None:
            self.skipTest("lake unavailable")
        GATE.validate_lean_declaration(
            SCRIPT.parent.parent,
            "U-0001",
            b"theorem debtClosure_U_0001 : True := by trivial\n",
            "debtClosure_U_0001",
            lake,
            "fixture",
        )

    def test_receipt_duplicate_unknown_and_evidence_traversal_fail(self) -> None:
        duplicate = (
            '{"disposition":"implemented","disposition":"proved","evidence":[],'
            '"id":"U-0001","prior_entry_sha256":"' + "0" * 64 + '",'
            '"prior_marker_sha256":"' + "1" * 64 + '","rationale":"x","schema":1}\n'
        ).encode()
        with self.assertRaisesRegex(GATE.DebtError, "duplicate JSON key"):
            GATE.parse_receipt_bytes(duplicate, "receipt")

        receipt = {
            "disposition": "implemented",
            "evidence": [
                {
                    "kind": "case_manifest",
                    "path": "tests/../escape.case.json",
                    "sha256": "2" * 64,
                }
            ],
            "id": "U-0001",
            "prior_entry_sha256": "0" * 64,
            "prior_marker_sha256": "1" * 64,
            "rationale": "Executable closure.",
            "schema": 1,
        }
        with self.assertRaisesRegex(GATE.DebtError, "traversal"):
            GATE.parse_receipt_bytes(
                (GATE.canonical_json(receipt) + "\n").encode(), "receipt"
            )

        receipt["evidence"] = [
            {
                "kind": "case_manifest",
                "path": "tests/DebtClosures/U_0001.case.json",
                "sha256": "2" * 64,
            }
        ]
        receipt["extra"] = True
        with self.assertRaisesRegex(GATE.DebtError, "unknown=extra"):
            GATE.parse_receipt_bytes(
                (GATE.canonical_json(receipt) + "\n").encode(), "receipt"
            )

    def test_case_manifest_canonical_shape_and_runner_fields_are_fail_closed(self) -> None:
        self.assertEqual(
            GATE.case_artifact_relative("U-0170", "rust_unit"),
            "rust/src/persistence/debt_u_0170.rs",
        )
        self.assertEqual(
            GATE.rust_unit_case_binding("U-0170"),
            (
                "debt_u_0170",
                "persistence::record::debt_u_0170::",
                "persistence::record::debt_u_0170::debt_closure_u_0170_fault_paths",
                '#[cfg(test)]\n#[path = "debt_u_0170.rs"]\nmod debt_u_0170;',
            ),
        )
        valid = {
            "checks": [{"kind": "rust_test", "sha256": "2" * 64}],
            "id": "U-0001",
            "schema": 1,
        }
        parsed = GATE.parse_case_manifest_bytes(
            (GATE.canonical_json(valid) + "\n").encode(), "manifest", "U-0001"
        )
        self.assertEqual(parsed, valid)
        unit = {"kind": "rust_unit", "sha256": "3" * 64}
        dual = {**valid, "checks": [valid["checks"][0], unit]}
        self.assertEqual(
            GATE.parse_case_manifest_bytes(
                (GATE.canonical_json(dual) + "\n").encode(), "manifest", "U-0001"
            ),
            dual,
        )
        cases = []
        for data, expected in (
            (b"\xef\xbb\xbf{}\n", "BOM"),
            (b"{}\r\n", "LF, not CR"),
            (b"{}", "end with one LF"),
            (b'{"checks":[],"checks":[],"id":"U-0001","schema":1}\n', "duplicate JSON key"),
            (
                (GATE.canonical_json(valid).replace(",", ", ") + "\n").encode(),
                "not canonical",
            ),
            ((GATE.canonical_json(dict(valid, checks=[])) + "\n").encode(), "nonempty"),
            (
                (GATE.canonical_json(dict(valid, id="U-0002")) + "\n").encode(),
                "does not match receipt id",
            ),
        ):
            cases.append((data, expected))
        unknown_check = {**valid, "checks": [{"kind": "python_unittest", "sha256": "2" * 64}]}
        cases.append(
            ((GATE.canonical_json(unknown_check) + "\n").encode(), "unknown case check kind")
        )
        duplicate_check = {**valid, "checks": [valid["checks"][0], valid["checks"][0]]}
        cases.append(
            ((GATE.canonical_json(duplicate_check) + "\n").encode(), "duplicate case check kind")
        )
        reverse_check = {**valid, "checks": [unit, valid["checks"][0]]}
        cases.append(
            ((GATE.canonical_json(reverse_check) + "\n").encode(), "sorted lexicographically")
        )
        duplicate_unit = {**valid, "checks": [unit, unit]}
        cases.append(
            ((GATE.canonical_json(duplicate_unit) + "\n").encode(), "duplicate case check kind")
        )
        for field, value in (
            ("path", "rust/src/persistence/debt_u_0001.rs"),
            ("module", "persistence::record"),
            ("selector", "forged"),
            ("command", "cargo"),
            ("argv", []),
            ("args", []),
            ("expected_output", "PASS"),
            ("harness", False),
        ):
            forged_check = {**unit, field: value}
            forged = {**valid, "checks": [forged_check]}
            cases.append(
                ((GATE.canonical_json(forged) + "\n").encode(), f"unknown={field}")
            )
        extra = {**valid, "command": ["true"]}
        cases.append(((GATE.canonical_json(extra) + "\n").encode(), "unknown=command"))
        for data, expected in cases:
            with self.subTest(expected=expected), self.assertRaisesRegex(
                GATE.DebtError, expected
            ):
                GATE.parse_case_manifest_bytes(data, "manifest", "U-0001")

        receipt = {
            "disposition": "implemented",
            "evidence": [
                {
                    "kind": "case_manifest",
                    "path": "tests/DebtClosures/U_0001.case.json",
                    "sha256": "2" * 64,
                }
            ],
            "id": "U-0001",
            "prior_entry_sha256": "0" * 64,
            "prior_marker_sha256": "1" * 64,
            "rationale": "Executable closure.",
            "schema": 1,
        }
        for field, value in (
            ("command", ["cargo", "test"]),
            ("expected_output", "PASS"),
        ):
            forged = dict(receipt)
            forged["evidence"] = [dict(receipt["evidence"][0], **{field: value})]
            with self.subTest(field=field), self.assertRaisesRegex(
                GATE.DebtError, f"unknown={field}"
            ):
                GATE.parse_receipt_bytes(
                    (GATE.canonical_json(forged) + "\n").encode(), "receipt"
                )

        for path, expected in (
            ("/tests/DebtClosures/U_0001.case.json", "traversal|noncanonical"),
            ("tests\\DebtClosures\\U_0001.case.json", "canonical repository-relative"),
            ("tests/DebtClosures/../U_0001.case.json", "traversal"),
            ("tests/DebtClosures/U_0001.case.json\0", "canonical repository-relative"),
            ("tests/DebtClosures/U_0002.case.json", "path must be exact"),
        ):
            with self.subTest(path=path), self.assertRaisesRegex(GATE.DebtError, expected):
                GATE.validate_evidence_shape(
                    "U-0001",
                    {"kind": "case_manifest", "path": path, "sha256": "2" * 64},
                    "evidence",
                )


class RunnerControlTests(unittest.TestCase):
    def test_sanitized_environment_keeps_only_validated_toolchain_paths(self) -> None:
        with tempfile.TemporaryDirectory(prefix="debt-job-tools-") as temporary:
            elan_home = Path(temporary) / "elan"
            elan_bin = elan_home / "bin"
            elan_bin.mkdir(parents=True)
            lake = elan_bin / "lake"
            lake.write_text("#!/bin/sh\nexit 0\n", encoding="utf-8")
            lake.chmod(0o755)
            with mock.patch.dict(
                os.environ,
                {
                    "PATH": str(elan_bin) + os.pathsep + "/usr/bin:/bin",
                    "ELAN_HOME": str(elan_home),
                    "RUSTUP_HOME": "/job/rustup",
                    "CARGO_HOME": "/job/cargo",
                    "RUSTUP_TOOLCHAIN": "1.89.0",
                    "HOSTILE_CASE_VALUE": "must-not-pass",
                },
                clear=False,
            ):
                resolved_lake = GATE._resolved_executable("lake", "fixture")
                environment = GATE._evidence_environment(
                    ["/job/cargo/bin/cargo", resolved_lake], SCRIPT.parent.parent
                )
            self.assertEqual(resolved_lake, str(lake))
            self.assertEqual(environment["ELAN_HOME"], str(elan_home))
            self.assertEqual(environment["RUSTUP_TOOLCHAIN"], "1.89.0")
            self.assertNotIn("HOSTILE_CASE_VALUE", environment)
            self.assertTrue(
                environment["PATH"].startswith(f"/job/cargo/bin:{elan_bin}:")
            )

        with mock.patch.dict(os.environ, {"ELAN_HOME": "relative"}, clear=False):
            with self.assertRaisesRegex(GATE.DebtError, "ELAN_HOME must be an absolute"):
                GATE._evidence_environment(["/bin/sh"], SCRIPT.parent.parent)

    def test_evidence_runner_uses_null_stdin_timeout_and_output_limit(self) -> None:
        root = SCRIPT.parent.parent
        with mock.patch.dict(os.environ, {"HOSTILE_CASE_VALUE": "must-not-pass"}):
            output = GATE._execute_evidence_command(
                root,
                [
                    "sh",
                    "-c",
                    'test -z "${HOSTILE_CASE_VALUE+x}" && ! read line && printf controlled',
                ],
                "/bin/sh",
                "fixture",
            )
        self.assertEqual(output, "controlled")

        with mock.patch.object(GATE, "EVIDENCE_OUTPUT_LIMIT", 32):
            with self.assertRaisesRegex(GATE.DebtError, "exceeded output limit"):
                GATE._execute_evidence_command(
                    root,
                    ["sh", "-c", "i=0; while [ $i -lt 100 ]; do printf x; i=$((i+1)); done"],
                    "/bin/sh",
                    "fixture",
                )
        with mock.patch.object(GATE, "EVIDENCE_TIMEOUT_SECONDS", 0.05):
            with self.assertRaisesRegex(GATE.DebtError, "timed out"):
                GATE._execute_evidence_command(
                    root, ["sleep", "5"], "/bin/sleep", "fixture"
                )


class PolicyProfileTests(RepoTestCase):
    def write_policy_base(self, specs):
        entries = []
        for debt_id, debt_class, severity in specs:
            label = {"premise": "PREMISE", "scope": "SCOPE"}.get(
                debt_class, "UNDONE"
            )
            path = f"Uwueave/Debt{debt_id[2:]}.lean"
            self.repo.write_source(debt_id, label=label, path=path)
            entry = self.repo.active_entry(
                debt_id, debt_class=debt_class, severity=severity
            )
            entries.append(entry)
        self.repo.write_active(entries)
        return entries, self.repo.commit("policy base")

    def test_development_allows_p0_but_v02_release_rejects_sorted_ids(self) -> None:
        entries, base = self.write_policy_base(
            [("U-0002", "obligation", "P0"), ("U-0001", "obligation", "P0")]
        )
        for entry in entries:
            entry["summary"] = "P3 and waived appear only as untrusted prose."
        self.repo.write_active(entries)
        base = self.repo.commit("canonical prose fixture")

        result = GATE.check(self.repo.root, base, "development-v0.2")
        self.assertEqual(result["policy_profile"], "development-v0.2")
        self.assertDebtError(
            r"policy release-v0\.2 forbids active severity P0: U-0001,U-0002",
            lambda: GATE.check(self.repo.root, base, "release-v0.2"),
        )
        self.assertDebtError(
            r"policy release-v0\.2 forbids active severity P0: U-0001,U-0002",
            lambda: GATE.check(self.repo.root, base, release_tag="v0.2.0"),
        )

    def test_v02_release_allows_p1_p2_p3_premise_and_scope(self) -> None:
        entries, base = self.write_policy_base(
            [
                ("U-0001", "obligation", "P1"),
                ("U-0002", "obligation", "P2"),
                ("U-0003", "obligation", "P3"),
                ("U-0004", "premise", None),
                ("U-0005", "scope", None),
            ]
        )
        entries[0]["summary"] = "P0 appears here but is not policy data."
        entries[0]["acceptance"] = "Close the named P0-looking prose fixture."
        self.repo.write_active(entries)
        base = self.repo.commit("prose is not severity")

        result = GATE.check(self.repo.root, base, "release-v0.2")
        self.assertEqual(result["policy_profile"], "release-v0.2")

    def test_v05_release_rejects_every_obligation_including_p1(self) -> None:
        _, base = self.write_policy_base(
            [
                ("U-0001", "obligation", "P0"),
                ("U-0002", "obligation", "P1"),
                ("U-0003", "obligation", "P2"),
                ("U-0004", "obligation", "P3"),
                ("U-0005", "premise", None),
            ]
        )
        self.assertDebtError(
            r"policy release-v0\.5 forbids active class obligation: "
            r"U-0001,U-0002,U-0003,U-0004",
            lambda: GATE.check(self.repo.root, base, release_tag="v0.5.0"),
        )

    def test_v05_release_accepts_only_premise_and_scope(self) -> None:
        _, base = self.write_policy_base(
            [("U-0001", "premise", None), ("U-0002", "scope", None)]
        )
        result = GATE.check(self.repo.root, base, release_tag="v0.5.0")
        self.assertEqual(result["policy_profile"], "release-v0.5")
        self.assertEqual(result["release_tag"], "v0.5.0")

    def test_closed_p0_and_reference_do_not_count_as_active(self) -> None:
        self.repo.write_source("U-0001")
        entry = self.repo.active_entry("U-0001", severity="P0")
        self.repo.write_active([entry])
        base = self.repo.commit("active P0 base")

        source = self.repo.root / "Uwueave/Debt.lean"
        source.write_text("-- ⟨DEBT-REF U-0001⟩\n", encoding="utf-8")
        self.repo.write_active([])
        evidence = self.repo.case_manifest("U-0001")
        self.repo.write_receipt(receipt_for(entry, "implemented", [evidence]))
        with self.repo.fake_rust_tools():
            result = GATE.check(self.repo.root, base, release_tag="v0.2.0")
        self.assertEqual(result["active"], 0)
        self.assertEqual(result["closed"], 1)
        self.assertEqual(result["refs"], 1)

    def test_unclassified_profiles_and_deprecated_alias(self) -> None:
        _, base = self.write_policy_base([("U-0001", "unclassified", None)])
        self.assertEqual(GATE.check(self.repo.root, base)["unclassified"], 1)
        for profile in ("development-v0.2", "release-v0.2", "release-v0.5", "v0.2"):
            with self.subTest(profile=profile):
                self.assertDebtError(
                    "forbids unclassified debt: U-0001",
                    lambda profile=profile: GATE.check(self.repo.root, base, profile),
                )

    def test_exact_tag_mapping_and_cli_mutual_exclusion_fail_closed(self) -> None:
        self.assertEqual(
            GATE.resolve_policy(None, "v0.2.0"), ("release-v0.2", "v0.2.0")
        )
        self.assertEqual(
            GATE.resolve_policy(None, "v0.5.0"), ("release-v0.5", "v0.5.0")
        )
        for tag in (
            "v0.2.1",
            "v0.2.0-rc.1",
            "v0.3.0",
            "v0.4.0",
            "v0.5.1",
            "v0.2.0\nrelease",
            "$(printf forged)",
            "",
        ):
            with self.subTest(tag=tag):
                self.assertDebtError(
                    "unsupported release tag",
                    lambda tag=tag: GATE.resolve_policy(None, tag),
                )
        self.assertDebtError(
            "mutually exclusive",
            lambda: GATE.resolve_policy("development-v0.2", "v0.2.0"),
        )
        self.assertDebtError(
            "unknown debt policy profile",
            lambda: GATE.resolve_policy("unknown", None),
        )
        parser = GATE.build_parser()
        with self.assertRaises(SystemExit):
            parser.parse_args(
                [
                    "check",
                    "--base",
                    "deadbeef",
                    "--profile",
                    "development-v0.2",
                    "--release-tag",
                    "v0.2.0",
                ]
            )
        with self.assertRaises(SystemExit):
            parser.parse_args(
                ["check", "--base", "deadbeef", "--profile", "unknown"]
            )

    def test_policy_wrapper_exposes_only_an_exact_release_tag_argument(self) -> None:
        wrapper = SCRIPT.with_name("v02-policy.sh")
        for arguments in (
            ["--profile", "release-v0.2"],
            ["--release-tag"],
            ["--release-tag", ""],
            ["--release-tag", "v0.2.0", "trailing"],
        ):
            with self.subTest(arguments=arguments):
                process = subprocess.run(
                    ["bash", wrapper, *arguments],
                    text=True,
                    capture_output=True,
                    check=False,
                )
                self.assertEqual(process.returncode, 2)
                self.assertEqual(
                    process.stderr,
                    "usage: scripts/v02-policy.sh [--release-tag EXACT_TAG]\n",
                )


class BootstrapTests(RepoTestCase):
    def test_guarded_bootstrap_is_base_exact_atomic_and_unclassified(self) -> None:
        self.repo.write_source("U-0001")
        base = self.repo.commit("mechanical marker-id migration")
        target = self.repo.root / "docs/debt/active.jsonl"

        self.assertDebtError(
            "requires --allow-bootstrap",
            lambda: GATE.bootstrap(
                self.repo.root, base, "docs/debt/active.jsonl", False
            ),
        )
        self.assertFalse(target.exists())

        self.repo.write_source("U-0001", detail="Changed during bootstrap.")
        self.assertDebtError(
            "marker set differs from base",
            lambda: GATE.bootstrap(
                self.repo.root, base, "docs/debt/active.jsonl", True
            ),
        )
        self.assertFalse(target.exists())

        run_git(self.repo.root, "checkout", "--", "Uwueave/Debt.lean")
        result = GATE.bootstrap(
            self.repo.root, base, "docs/debt/active.jsonl", True
        )
        self.assertEqual(result["status"], "bootstrapped")
        data = target.read_bytes()
        entries = GATE.parse_active_bytes(data, "bootstrap")
        self.assertEqual(entries[0]["class"], "unclassified")
        self.assertEqual(entries[0]["acceptance"], "")
        self.assertEqual(result["sha256"], GATE.sha256_bytes(data))

        self.assertDebtError(
            "refuses to overwrite",
            lambda: GATE.bootstrap(
                self.repo.root, base, "docs/debt/active.jsonl", True
            ),
        )

    def test_bootstrap_rejects_nonmarker_source_drift(self) -> None:
        self.repo.write_source("U-0001")
        base = self.repo.commit("mechanical marker-id migration")
        source = self.repo.root / "Uwueave/Debt.lean"
        source.write_text(source.read_text() + "def unrelated := 1\n", encoding="utf-8")
        self.assertDebtError(
            "Lean source tree differs",
            lambda: GATE.bootstrap(
                self.repo.root, base, "docs/debt/active.jsonl", True
            ),
        )

    def test_bootstrap_rejects_zero_markers_and_unrelated_base(self) -> None:
        source = self.repo.root / "Uwueave/Debt.lean"
        source.write_text("/- no debt marker -/\n", encoding="utf-8")
        base = self.repo.commit("empty migration")
        self.assertDebtError(
            "zero-marker migration",
            lambda: GATE.bootstrap(
                self.repo.root, base, "docs/debt/active.jsonl", True
            ),
        )
        tree = run_git(self.repo.root, "rev-parse", f"{base}^{{tree}}")
        unrelated = subprocess.run(
            ["git", "commit-tree", tree],
            cwd=self.repo.root,
            input="unrelated\n",
            text=True,
            check=True,
            capture_output=True,
        ).stdout.strip()
        self.assertDebtError(
            "not an ancestor",
            lambda: GATE.bootstrap(
                self.repo.root, unrelated, "docs/debt/active.jsonl", True
            ),
        )

    def test_bootstrap_sees_base_receipt_deleted_only_in_worktree(self) -> None:
        self.repo.write_source("U-0001")
        receipt = {
            "disposition": "superseded",
            "evidence": [],
            "id": "U-9999",
            "prior_entry_sha256": "1" * 64,
            "prior_marker_sha256": "2" * 64,
            "rationale": "Historical closure receipt.",
            "replacement_id": "U-0001",
            "schema": 1,
        }
        path = self.repo.write_receipt(receipt)
        base = self.repo.commit("receipt-bearing migration")
        path.unlink()
        self.assertDebtError(
            "base contains closure receipts",
            lambda: GATE.bootstrap(
                self.repo.root, base, "docs/debt/active.jsonl", True
            ),
        )

    def test_bootstrap_rejects_deleted_registry_history(self) -> None:
        self.repo.write_source("U-0001")
        self.repo.write_active([self.repo.active_entry("U-0001", debt_class="unclassified")])
        self.repo.commit("premature registry")
        run_git(self.repo.root, "rm", "docs/debt/active.jsonl")
        base = self.repo.commit("delete premature registry")
        self.assertDebtError(
            "no registry or receipt history",
            lambda: GATE.bootstrap(
                self.repo.root, base, "docs/debt/active.jsonl", True
            ),
        )

    def test_symlinked_registry_and_source_are_rejected(self) -> None:
        self.repo.write_source("U-0001")
        entry = self.repo.active_entry("U-0001")
        self.repo.write_active([entry])
        base = self.repo.commit()
        active = self.repo.root / "docs/debt/active.jsonl"
        alternate = self.repo.root / "docs/debt/alternate.jsonl"
        shutil.copyfile(active, alternate)
        active.unlink()
        active.symlink_to(alternate.name)
        self.assertDebtError("symlinks are forbidden", lambda: GATE.check(self.repo.root, base, None))

        active.unlink()
        shutil.copyfile(alternate, active)
        source = self.repo.root / "Uwueave/Debt.lean"
        other = self.repo.root / "Uwueave/Other.txt"
        shutil.copyfile(source, other)
        source.unlink()
        source.symlink_to(other.name)
        self.assertDebtError("symlinks are forbidden", lambda: GATE.check(self.repo.root, base, None))


if __name__ == "__main__":
    unittest.main()
