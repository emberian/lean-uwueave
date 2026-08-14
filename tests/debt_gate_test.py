#!/usr/bin/env python3
"""Isolated tests for scripts/debt-gate.py.

These fixtures create temporary Git repositories.  They do not inspect or
modify the production marker corpus, whose migration is intentionally a later
patch.
"""

from __future__ import annotations

import importlib.util
import hashlib
import os
from pathlib import Path
import shutil
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

    def aggregate_evidence(self, debt_id: str = "U-0001", passing: bool = True):
        path = self.root / "scripts/debt-closures.sh"
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(
            "#!/bin/bash\n"
            "set -eu\n"
            f"test \"$1\" = --debt-case && test \"$2\" = {debt_id}\n"
            f"printf '%s\\n' 'debt-evidence: {debt_id}: {'PASS' if passing else 'FAIL'}'\n",
            encoding="utf-8",
        )
        path.chmod(0o755)
        run_git(self.root, "add", "scripts/debt-closures.sh")
        return {
            "command": ["bash", "scripts/debt-closures.sh", "--debt-case", debt_id],
            "kind": "aggregate_case",
            "path": "scripts/debt-closures.sh",
            "sha256": digest(path),
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
            "command": ["lake", "env", "lean", relative],
            "declaration": declaration,
            "kind": "lean_decl",
            "path": relative,
            "sha256": digest(path),
        }

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
        first = GATE.check(self.repo.root, base, "v0.2")
        second = GATE.check(self.repo.root, base, "v0.2")
        self.assertEqual(first, second)
        self.assertEqual(first["status"], "ok")
        self.assertEqual(first["active"], 1)

        command = [
            sys.executable,
            str(SCRIPT),
            "--root",
            str(self.repo.root),
            "check",
            "--base",
            base,
            "--milestone",
            "v0.2",
        ]
        environment = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
        one = subprocess.run(command, check=True, capture_output=True, env=environment).stdout
        two = subprocess.run(command, check=True, capture_output=True, env=environment).stdout
        self.assertEqual(one, two)
        self.assertEqual(one, (GATE.canonical_json(first) + "\n").encode())

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
            evidence = [self.repo.aggregate_evidence()]
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
                        context = repo.fake_lake() if disposition == "proved" else mock.patch.dict(os.environ, {})
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

    def test_missing_or_unresolvable_evidence_fails(self) -> None:
        entry, base = self.make_base()
        (self.repo.root / "Uwueave/Debt.lean").write_text("/- closed -/\n")
        self.repo.write_active([])
        receipt = receipt_for(entry, "implemented", [])
        # Shape validation happens when the gate reads the canonical receipt.
        self.repo.write_receipt(receipt)
        self.assertDebtError(
            "implemented closure requires one aggregate case",
            lambda: GATE.check(self.repo.root, base, None),
        )

        item = self.repo.aggregate_evidence()
        (self.repo.root / item["path"]).unlink()
        receipt["evidence"] = [item]
        self.repo.write_receipt(receipt)
        self.assertDebtError(
            "path is missing|tracked stage-0",
            lambda: GATE.check(self.repo.root, base, None),
        )

        evidence_path = self.repo.root / item["path"]
        evidence_path.write_text("# a comment is not executable evidence\n")
        self.assertDebtError(
            "SHA-256 does not match",
            lambda: GATE.check(self.repo.root, base, None),
        )

    def test_evidence_hash_change_and_symlink_are_rejected(self) -> None:
        _, base, receipt = self.close_base("implemented")
        path = self.repo.root / receipt["evidence"][0]["path"]
        path.write_text("# changed after receipt\n", encoding="utf-8")
        self.assertDebtError(
            "SHA-256 does not match",
            lambda: GATE.check(self.repo.root, base, None),
        )
        other = path.with_name("other.sh")
        other.write_text("# target\n", encoding="utf-8")
        path.unlink()
        path.symlink_to(other.name)
        self.assertDebtError("symlinks are forbidden", lambda: GATE.check(self.repo.root, base, None))

    def test_runnable_evidence_must_actually_pass_exactly_one_test(self) -> None:
        entry, base = self.make_base()
        (self.repo.root / "Uwueave/Debt.lean").write_text("/- closed -/\n")
        self.repo.write_active([])
        evidence = self.repo.aggregate_evidence(passing=False)
        self.repo.write_receipt(receipt_for(entry, "implemented", [evidence]))
        self.assertDebtError(
            "aggregate dispatcher did not emit unique exact PASS",
            lambda: GATE.check(self.repo.root, base, None),
        )

    def make_base_with_old_receipt(self):
        self.repo.write_source("U-0002")
        active = self.repo.active_entry("U-0002")
        self.repo.write_active([active])
        evidence = self.repo.aggregate_evidence("U-0001")
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
        result = GATE.check(self.repo.root, base, None)
        self.assertEqual(result["refs"], 1)

    def test_closed_id_cannot_be_reused(self) -> None:
        _, _, base = self.make_base_with_old_receipt()
        self.repo.write_source("U-0001", path="Uwueave/Reused.lean")
        entries = [self.repo.active_entry("U-0001"), self.repo.active_entry("U-0002")]
        self.repo.write_active(entries)
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
                    "command": ["lake", "env", "lean", "tests/../escape.lean"],
                    "declaration": "debtClosure_U_0001",
                    "kind": "lean_decl",
                    "path": "tests/../escape.lean",
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
                "command": ["lake", "env", "lean", "tests/DebtClosures/U_0001.lean"],
                "declaration": "debtClosure_U_0001",
                "kind": "lean_decl",
                "path": "tests/DebtClosures/U_0001.lean",
                "sha256": "2" * 64,
            }
        ]
        receipt["extra"] = True
        with self.assertRaisesRegex(GATE.DebtError, "unknown=extra"):
            GATE.parse_receipt_bytes(
                (GATE.canonical_json(receipt) + "\n").encode(), "receipt"
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

    def test_milestone_rejects_unclassified_but_plain_check_allows_it(self) -> None:
        self.repo.write_source("U-0001")
        entry = self.repo.active_entry("U-0001", debt_class="unclassified")
        self.repo.write_active([entry])
        base = self.repo.commit()
        self.assertEqual(GATE.check(self.repo.root, base, None)["unclassified"], 1)
        self.assertDebtError(
            "milestone v0.2 forbids unclassified debt",
            lambda: GATE.check(self.repo.root, base, "v0.2"),
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
