#!/usr/bin/env python3
"""Fail-closed integrity gate for the execution-TCB (TRUST Ledger 2).

This gate checks registry lineage, source surfaces, documentation, and a
per-build native observation.  It deliberately does not prove any external
premise or semantic obligation named by the ledger.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import stat
import subprocess
import sys
from typing import Any


MANIFEST = Path("docs/trust/ledger2-v1.json")
HEX64 = re.compile(r"[0-9a-f]{64}\Z")
DEBT_ID = re.compile(r"U-[0-9]{4}\Z")
PRIMARY = re.compile(r"⟨(UNDONE|PREMISE|SCOPE) (U-[0-9]{4})(?:⟩|[^⟩]*⟩)")
REFERENCE = re.compile(r"⟨DEBT-REF (U-[0-9]{4})⟩")
CI_WORKFLOW_SHA256 = "b9ed3ee07e818d58eaf974a7f8f3d7f4a9839d2ff935b745fc6e76bd98b4fa0f"
POLICY_SCRIPT_SHA256 = "3a564d6299cd6aba6d9b0d2ec587db30aa09371537f8cfb8cc996f2456266f32"
PINNED_PRIOR_IDENTITIES = {
    "U-0027": ("2c9da39b5da6f64f19440f0926ec9e52934e049d4572ce595bd84ccc893a1c33",
               "60d1f4fc061543d58542c20d3aa16fdcd8ce3311998b31b815ae04b8b4c8d1f9"),
    "U-0056": ("60e6e1743618222ea8cf36a503086f22a74dd7e7be821ec97f37d2200bdcd606",
               "8a5c0f062f1ad8c476427036b321ee016edfb17a310bbf9eac7eb10e4ebb456e"),
    "U-0115": ("40e0ece08d23514ef7c5f3edad97164436f230950e1714b70c76c5e71f5aae11",
               "1448885fd96bd55fb5441404007d83f3884bddf73bb46a41b4e0369ef1da7e8a"),
    "U-0160": ("619601433939703340ae33324ca645223a5b2830eb1fb871e528b0c42526d8da",
               "8154d10738fb415b4624bba4a36b50f3727ade4a27cf495d995950bce147c79d"),
    "U-0170": ("f783cca16e43a3db1a3d21e27a9f58f56b8ef45722c4d9761750cc6afd7ba160",
               "26591cb5cb816ec7e0700206e493b2c508320f7b497521ec7b0672296c7dcb44"),
}


class GateError(Exception):
    pass


def canonical_json(value: Any) -> str:
    return json.dumps(value, ensure_ascii=False, allow_nan=False,
                      sort_keys=True, separators=(",", ":"))


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise GateError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def _reject_constant(value: str) -> None:
    raise GateError(f"non-finite JSON value {value!r}")


def parse_json_bytes(path: Path, canonical: bool = False) -> Any:
    try:
        raw = stable_file_bytes(path)
    except GateError:
        raise
    if raw.startswith(b"\xef\xbb\xbf") or b"\r" in raw or not raw.endswith(b"\n"):
        raise GateError(f"{path}: expected UTF-8, one final LF, no BOM/CR")
    try:
        text = raw.decode("utf-8")
        value = json.loads(text, object_pairs_hook=_unique_object,
                           parse_constant=_reject_constant)
    except (UnicodeError, json.JSONDecodeError) as exc:
        raise GateError(f"{path}: malformed JSON: {exc}") from None
    if canonical and raw != (canonical_json(value) + "\n").encode():
        raise GateError(f"{path}: JSON is not canonical")
    return value


def expect_keys(value: Any, keys: set[str], label: str) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != keys:
        actual = set(value) if isinstance(value, dict) else type(value).__name__
        raise GateError(f"{label}: expected keys {sorted(keys)}, got {actual}")
    return value


def regular_file(path: Path) -> None:
    try:
        mode = path.lstat().st_mode
    except OSError as exc:
        raise GateError(f"cannot inspect {path}: {exc}") from None
    if stat.S_ISLNK(mode) or not stat.S_ISREG(mode):
        raise GateError(f"expected non-symlink regular file: {path}")


def stable_file_bytes(path: Path) -> bytes:
    """Read one regular file through a no-follow descriptor and reject races."""
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise GateError(f"cannot open regular file {path}: {exc}") from None
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise GateError(f"expected regular file descriptor: {path}")
        with os.fdopen(os.dup(descriptor), "rb") as source:
            data = source.read()
        after = os.fstat(descriptor)
    except OSError as exc:
        raise GateError(f"cannot read regular file {path}: {exc}") from None
    finally:
        os.close(descriptor)
    identity = lambda value: (value.st_dev, value.st_ino, value.st_mode,
                              value.st_size, value.st_mtime_ns)
    if identity(before) != identity(after) or after.st_size != len(data):
        raise GateError(f"file changed while reading: {path}")
    return data


def stable_file_measure(path: Path, prefix_bytes: int = 0) -> tuple[int, str, bytes]:
    """Hash one no-follow file descriptor and optionally retain an exact prefix."""
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise GateError(f"cannot open regular file {path}: {exc}") from None
    digest = hashlib.sha256()
    prefix = bytearray()
    count = 0
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise GateError(f"expected regular file descriptor: {path}")
        while True:
            block = os.read(descriptor, 1024 * 1024)
            if not block:
                break
            digest.update(block)
            count += len(block)
            if len(prefix) < prefix_bytes:
                prefix.extend(block[:prefix_bytes - len(prefix)])
        after = os.fstat(descriptor)
    except OSError as exc:
        raise GateError(f"cannot hash regular file {path}: {exc}") from None
    finally:
        os.close(descriptor)
    identity = lambda value: (value.st_dev, value.st_ino, value.st_mode,
                              value.st_size, value.st_mtime_ns)
    if identity(before) != identity(after) or after.st_size != count:
        raise GateError(f"file changed while hashing: {path}")
    return count, digest.hexdigest(), bytes(prefix)


def read_text(root: Path, relative: str) -> str:
    path = root / relative
    try:
        return stable_file_bytes(path).decode("utf-8")
    except UnicodeError as exc:
        raise GateError(f"cannot read {relative}: {exc}") from None


def sha256_file(path: Path) -> str:
    return stable_file_measure(path)[1]


def load_manifest(root: Path) -> dict[str, Any]:
    value = parse_json_bytes(root / MANIFEST, canonical=True)
    manifest = expect_keys(value, {"documentation", "ledger", "native",
                                   "runtime_surface", "schema",
                                   "unsafe_inventory"}, "manifest")
    if manifest["schema"] != 1:
        raise GateError("manifest: unsupported schema")
    documentation = expect_keys(
        manifest["documentation"],
        {"historical_native_observations", "live_surfaces", "stale_fingerprints",
         "unstable_native_patterns"}, "manifest.documentation"
    )
    expected_live = {
        "README.md": "docs/trust/ledger2-v1.json",
        "RELEASE.md": "docs/trust/ledger2-v1.json",
        "docs/COHERENCE.md": "trust/ledger2-v1.json",
        "docs/MAP.md": "trust/ledger2-v1.json",
        "docs/RUNTIME.md": "trust/ledger2-v1.json",
        "docs/TRUST.md": "trust/ledger2-v1.json",
        "docs/index.html": "trust/ledger2-v1.json",
    }
    expected_stale = [
        "1,049,544",
        "1,249,984",
        "1b0deb1bcfcaa79f66ba7f880a340605a9055e655820888a2ebcb6110b528d8e",
        "15 Lake objects",
        "15 Lake-owned objects",
        "16 archive members",
        "14 textual unsafe occurrences",
        "ten rows: eight open execution obligations",
    ]
    expected_unstable = [
        r"\b[0-9][0-9,]*\s+Lake(?:-owned)? objects?\b",
        r"\b[0-9][0-9,]*\s+archive members?\b",
        r"(?is)(?:native[- ]closure|archive).{0,100}\b[0-9][0-9,]*\s*(?:bytes?|B)\b",
        r"(?is)(?:native[- ]closure|archive).{0,100}\bSHA-256\s+`?[0-9a-f]{64}",
    ]
    if documentation["live_surfaces"] != expected_live \
            or documentation["historical_native_observations"] != ["docs/PERFORMANCE.md"] \
            or documentation["stale_fingerprints"] != expected_stale \
            or documentation["unstable_native_patterns"] != expected_unstable:
        raise GateError("manifest.documentation: release/historical surface drift")
    native = expect_keys(manifest["native"], {"archive_rule", "ci_workflow", "nonclaims",
                                               "observation_schema", "policy_script", "targets",
                                               "toolchain_authority"}, "manifest.native")
    if native["observation_schema"] != 1 or native["toolchain_authority"] != "lean-toolchain":
        raise GateError("manifest.native: schema/toolchain authority drift")
    expected_nonclaims = [
        "observations do not prove Lean code generation",
        "observations do not prove compiler, archiver, or linker semantics",
        "observations do not prove the C shim, ABI, Rust unsafe, Lean runtime, storage, filesystem, or durability semantics",
    ]
    if native["archive_rule"] != (
        "one byte-identical member per Lake RuntimeInit-closure object plus exactly one compiled shim member"
    ) or native["nonclaims"] != expected_nonclaims:
        raise GateError("manifest.native: archive rule/nonclaims drift")
    if native["ci_workflow"] != ".github/workflows/ci.yml" \
            or native["policy_script"] != "scripts/v02-policy.sh":
        raise GateError("manifest.native: enforcement location drift")
    targets = native["targets"]
    if targets != [
        {"ci_runner": "macos-15", "rust_target": "aarch64-apple-darwin"},
        {"ci_runner": "ubuntu-24.04", "rust_target": "x86_64-unknown-linux-gnu"},
    ]:
        raise GateError("manifest.native: supported target matrix drift")
    surface = expect_keys(manifest["runtime_surface"], {"direct_imports", "lean_exports",
                                                         "root", "rust_auxiliary_bindings",
                                                         "rust_primary_binding", "shim_source",
                                                         "shim_support_symbols"},
                          "manifest.runtime_surface")
    if surface["root"] != "Uwueave.RuntimeInit" or surface["shim_source"] != "rust/shim.c" \
            or surface["rust_primary_binding"] != "rust/src/ffi.rs":
        raise GateError("manifest.runtime_surface: authority paths drift")
    inventory = expect_keys(manifest["unsafe_inventory"], {"files", "roots", "semantics",
                                                            "zero_elsewhere"},
                            "manifest.unsafe_inventory")
    if inventory["roots"] != ["rust/src", "rust/examples", "rust/benches"] \
            or inventory["zero_elsewhere"] is not True \
            or inventory["semantics"] != (
                "comment-and-literal-aware Rust source-token inventory; "
                "not expanded HIR or a semantic proof"
            ):
        raise GateError("manifest.unsafe_inventory: scan roots/scope drift")
    return manifest


def load_active(root: Path) -> dict[str, dict[str, Any]]:
    path = root / "docs/debt/active.jsonl"
    try:
        text = stable_file_bytes(path).decode("utf-8")
    except UnicodeError as exc:
        raise GateError(f"{path}: active registry is not UTF-8: {exc}") from None
    result: dict[str, dict[str, Any]] = {}
    for number, line in enumerate(text.splitlines(), 1):
        try:
            entry = json.loads(line, object_pairs_hook=_unique_object,
                               parse_constant=_reject_constant)
        except (json.JSONDecodeError, GateError) as exc:
            raise GateError(f"{path}:{number}: invalid JSON: {exc}") from None
        debt_id = entry.get("id") if isinstance(entry, dict) else None
        if not isinstance(debt_id, str) or not DEBT_ID.fullmatch(debt_id):
            raise GateError(f"{path}:{number}: invalid debt id")
        if debt_id in result:
            raise GateError(f"{path}:{number}: duplicate {debt_id}")
        result[debt_id] = entry
    return result


def load_receipts(root: Path) -> dict[str, dict[str, Any]]:
    result: dict[str, dict[str, Any]] = {}
    directory = root / "docs/debt/closed"
    if not directory.is_dir():
        raise GateError("docs/debt/closed is absent")
    for path in sorted(directory.glob("U-[0-9][0-9][0-9][0-9].json")):
        receipt = parse_json_bytes(path, canonical=True)
        if not isinstance(receipt, dict) or receipt.get("id") != path.stem:
            raise GateError(f"{path}: receipt identity mismatch")
        result[path.stem] = receipt
    return result


def git_bytes(root: Path, arguments: list[str], label: str,
              allow_failure: bool = False) -> bytes | None:
    try:
        process = subprocess.run(["git", *arguments], cwd=root, check=False,
                                 capture_output=True, timeout=30)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise GateError(f"ledger: cannot query {label}: {exc}") from None
    if process.returncode:
        if allow_failure:
            return None
        detail = process.stderr.decode("utf-8", errors="replace").strip()
        raise GateError(f"ledger: {label} failed: {detail}")
    return process.stdout


def validate_receipt_prior_history(root: Path, debt_id: str,
                                   receipt: dict[str, Any]) -> None:
    observed = (receipt["prior_entry_sha256"], receipt["prior_marker_sha256"])
    pinned = PINNED_PRIOR_IDENTITIES.get(debt_id)
    if pinned is not None:
        if observed != pinned:
            raise GateError(f"ledger: prior active identity drift in receipt {debt_id}")
        return
    if git_bytes(root, ["rev-parse", "--is-inside-work-tree"], "repository identity",
                 allow_failure=True) is None:
        raise GateError(f"ledger: unpinned receipt {debt_id} has no auditable Git history")
    relative = f"docs/debt/closed/{debt_id}.json"
    head_blob = git_bytes(root, ["show", f"HEAD:{relative}"], f"HEAD receipt {debt_id}",
                          allow_failure=True)
    if head_blob is None:
        prior_revision = "HEAD"
    else:
        if head_blob != stable_file_bytes(root / relative):
            raise GateError(f"ledger: committed receipt {debt_id} is not immutable")
        history = git_bytes(
            root,
            ["log", "--diff-filter=A", "--format=%H%x00%P", "--", relative],
            f"addition history for {debt_id}",
        )
        records = [record for record in (history or b"").splitlines() if record]
        if not records or b"\0" not in records[0]:
            raise GateError(f"ledger: receipt {debt_id} lacks one addition history")
        _, parents = records[0].split(b"\0", 1)
        parent_ids = parents.decode("ascii").split()
        if len(parent_ids) != 1:
            raise GateError(f"ledger: receipt {debt_id} addition lacks one auditable parent")
        prior_revision = parent_ids[0]
    active_bytes = git_bytes(
        root,
        ["show", f"{prior_revision}:docs/debt/active.jsonl"],
        f"prior active registry for {debt_id}",
    )
    prior_entry: dict[str, Any] | None = None
    try:
        for line in (active_bytes or b"").decode("utf-8").splitlines():
            entry = json.loads(line, object_pairs_hook=_unique_object,
                               parse_constant=_reject_constant)
            if isinstance(entry, dict) and entry.get("id") == debt_id:
                if prior_entry is not None:
                    raise GateError(f"ledger: duplicate prior active row for {debt_id}")
                prior_entry = entry
    except (UnicodeError, json.JSONDecodeError) as exc:
        raise GateError(f"ledger: malformed prior active registry for {debt_id}: {exc}") from None
    if prior_entry is None:
        raise GateError(f"ledger: prior active row is absent for receipt {debt_id}")
    expected = (hashlib.sha256(canonical_json(prior_entry).encode()).hexdigest(),
                prior_entry.get("marker_sha256"))
    if observed != expected:
        raise GateError(f"ledger: receipt {debt_id} does not bind its prior active row")


def validate_used_receipt(root: Path, debt_id: str, receipt: dict[str, Any]) -> None:
    disposition = receipt.get("disposition")
    expected = {"disposition", "evidence", "id", "prior_entry_sha256",
                "prior_marker_sha256", "rationale", "schema"}
    if disposition == "superseded":
        expected.add("replacement_id")
    expect_keys(receipt, expected, f"receipt.{debt_id}")
    if type(receipt["schema"]) is not int or receipt["schema"] != 1 \
            or receipt["id"] != debt_id:
        raise GateError(f"ledger: malformed receipt identity/schema for {debt_id}")
    if disposition not in {"proved", "implemented", "obsolete", "superseded"}:
        raise GateError(f"ledger: unsupported receipt disposition for {debt_id}")
    for field in ("prior_entry_sha256", "prior_marker_sha256"):
        if not isinstance(receipt[field], str) or not HEX64.fullmatch(receipt[field]):
            raise GateError(f"ledger: malformed {field} in receipt {debt_id}")
    validate_receipt_prior_history(root, debt_id, receipt)
    rationale = receipt["rationale"]
    if not isinstance(rationale, str) or not rationale or rationale != rationale.strip() \
            or any(ord(character) < 32 or ord(character) == 127 for character in rationale):
        raise GateError(f"ledger: malformed rationale in receipt {debt_id}")
    evidence = receipt["evidence"]
    if not isinstance(evidence, list):
        raise GateError(f"ledger: malformed evidence in receipt {debt_id}")
    required_kind = {"proved": "lean_decl", "implemented": "case_manifest"}.get(disposition)
    if disposition == "superseded":
        replacement = receipt.get("replacement_id")
        if not isinstance(replacement, str) or not DEBT_ID.fullmatch(replacement) \
                or replacement == debt_id or evidence:
            raise GateError(f"ledger: malformed supersession receipt for {debt_id}")
        return
    if disposition == "obsolete":
        required_kind = None
    if len(evidence) != 1:
        raise GateError(f"ledger: paid/obsolete receipt {debt_id} needs one evidence item")
    item = expect_keys(evidence[0], {"kind", "path", "sha256"},
                       f"receipt.{debt_id}.evidence")
    kind = item["kind"]
    if required_kind is not None and kind != required_kind:
        raise GateError(f"ledger: receipt {debt_id} has the wrong evidence kind")
    if kind not in {"lean_decl", "case_manifest"}:
        raise GateError(f"ledger: receipt {debt_id} has an unknown evidence kind")
    stem = debt_id.replace("-", "_")
    suffix = ".lean" if kind == "lean_decl" else ".case.json"
    expected_path = f"tests/DebtClosures/{stem}{suffix}"
    if item["path"] != expected_path or not isinstance(item["sha256"], str) \
            or not HEX64.fullmatch(item["sha256"]):
        raise GateError(f"ledger: receipt {debt_id} evidence identity is malformed")
    evidence_path = root / expected_path
    if sha256_file(evidence_path) != item["sha256"]:
        raise GateError(f"ledger: receipt {debt_id} evidence hash mismatch")
    if kind == "case_manifest":
        case = parse_json_bytes(evidence_path, canonical=True)
        case = expect_keys(case, {"checks", "id", "schema"},
                           f"receipt.{debt_id}.case_manifest")
        if type(case["schema"]) is not int or case["schema"] != 1 or case["id"] != debt_id:
            raise GateError(f"ledger: receipt {debt_id} case manifest identity/schema drift")
        checks = case["checks"]
        if not isinstance(checks, list) or not checks:
            raise GateError(f"ledger: receipt {debt_id} case manifest needs checks")
        kinds: list[str] = []
        for index, check in enumerate(checks):
            check = expect_keys(check, {"kind", "sha256"},
                                f"receipt.{debt_id}.case_manifest.check[{index}]")
            check_kind = check["kind"]
            if check_kind not in {"rust_test", "rust_unit"} \
                    or not isinstance(check["sha256"], str) \
                    or not HEX64.fullmatch(check["sha256"]):
                raise GateError(f"ledger: receipt {debt_id} has malformed case check")
            kinds.append(check_kind)
            stem_lower = debt_id.replace("-", "_").lower()
            artifact_relative = (f"rust/tests/debt_{stem_lower}.rs" if check_kind == "rust_test"
                                 else f"rust/src/persistence/debt_{stem_lower}.rs")
            artifact = root / artifact_relative
            if sha256_file(artifact) != check["sha256"]:
                raise GateError(
                    f"ledger: receipt {debt_id} case artifact identity mismatch for {check_kind}"
                )
        if kinds != sorted(set(kinds)):
            raise GateError(f"ledger: receipt {debt_id} case checks must be sorted/unique")


def validate_ledger(root: Path, manifest: dict[str, Any]) -> None:
    ledger = expect_keys(manifest["ledger"], {"paid_controls", "predecessors",
                                              "resolution_policy", "rows", "umbrella"},
                         "ledger")
    policy = expect_keys(ledger["resolution_policy"], {"allowed", "forbidden",
                                                        "premises_never_paid"},
                         "ledger.resolution_policy")
    if policy != {"allowed": ["active", "proved", "implemented", "superseded-lineage"],
                  "forbidden": ["obsolete"], "premises_never_paid": True}:
        raise GateError("ledger: resolution policy drift")
    rows = ledger["rows"]
    expected_rows = [
        {"class": "obligation", "id": "U-0161", "marker": "UNDONE", "severity": "P1", "source": "Uwueave/Gated.lean"},
        {"class": "premise", "id": "U-0162", "marker": "PREMISE", "severity": None, "source": "Uwueave/Gated.lean"},
        {"class": "premise", "id": "U-0163", "marker": "PREMISE", "severity": None, "source": "Uwueave/Gated.lean"},
        {"class": "obligation", "id": "U-0164", "marker": "UNDONE", "severity": "P1", "source": "Uwueave/Gated.lean"},
        {"class": "obligation", "id": "U-0165", "marker": "UNDONE", "severity": "P1", "source": "Uwueave/Gated.lean"},
        {"class": "obligation", "id": "U-0166", "marker": "UNDONE", "severity": "P1", "source": "Uwueave/Gated.lean"},
        {"class": "obligation", "id": "U-0167", "marker": "UNDONE", "severity": "P1", "source": "Uwueave/Gated.lean"},
        {"class": "premise", "id": "U-0168", "marker": "PREMISE", "severity": None, "source": "Uwueave/Durable.lean"},
        {"class": "scope", "id": "U-0169", "marker": "SCOPE", "severity": "P3", "source": "Uwueave/Durable.lean"},
        {"class": "obligation", "id": "U-0170", "marker": "UNDONE", "severity": "P0", "source": "Uwueave/Durable.lean"},
    ]
    if rows != expected_rows:
        raise GateError("ledger: exact successor identities U-0161..U-0170 drifted")
    for row in rows:
        expect_keys(row, {"class", "id", "marker", "severity", "source"},
                    f"ledger.{row.get('id', '?')}")
        marker_class = {"UNDONE": "obligation", "PREMISE": "premise", "SCOPE": "scope"}
        if marker_class.get(row["marker"]) != row["class"]:
            raise GateError(f"ledger: marker/class mismatch for {row['id']}")
    umbrella = ledger["umbrella"]
    expect_keys(umbrella, {"class", "id", "marker", "primary_refs", "severity", "source"},
                "ledger.umbrella")
    expected_refs = [f"U-{number:04d}" for number in range(161, 171)]
    expected_umbrella = {
        "class": "obligation", "id": "U-0160", "marker": "UNDONE",
        "primary_refs": expected_refs, "severity": "P0", "source": "Uwueave/Gated.lean",
    }
    if umbrella != expected_umbrella:
        raise GateError("ledger: umbrella mapping drift")
    controls = ledger["paid_controls"]
    expected_controls = [
        {"id": "lean-owned-request-encoding", "kind": "mechanized-control",
         "source": "Uwueave/Exec.lean", "witness": "Uwueave.Exec.encodeRequestKernel_eq"},
        {"id": "native-closure-freshness", "kind": "mechanized-control",
         "source": "rust/build.rs",
         "witness": "exact Lake setup closure, byte snapshots, archive membership, and TOCTOU rechecks"},
    ]
    if controls != expected_controls:
        raise GateError("ledger: paid controls must remain exactly two non-debt controls")
    exec_source = strip_lean(read_text(root, "Uwueave/Exec.lean"))
    if not re.search(r"\btheorem\s+encodeRequestKernel_eq\b", exec_source):
        raise GateError("ledger: lean-owned request-encoding witness is absent")

    active = load_active(root)
    receipts = load_receipts(root)
    overlap = sorted(set(active) & set(receipts))
    if overlap:
        raise GateError(f"ledger: ids cannot be both active and closed: {overlap}")
    expected_predecessors = [
        {"id": "U-0027", "replacement_id": "U-0170"},
        {"id": "U-0056", "replacement_id": "U-0160"},
        {"id": "U-0115", "replacement_id": "U-0170"},
    ]
    if ledger["predecessors"] != expected_predecessors:
        raise GateError("ledger: decomposition predecessor mapping drift")
    for predecessor in expected_predecessors:
        receipt = receipts.get(predecessor["id"])
        if receipt is not None:
            validate_used_receipt(root, predecessor["id"], receipt)
        if receipt is None or receipt.get("disposition") != "superseded" \
                or receipt.get("replacement_id") != predecessor["replacement_id"] \
                or receipt.get("evidence") != []:
            raise GateError(f"ledger: immutable decomposition receipt drift for {predecessor['id']}")
    manifest_rows = [umbrella, *rows]
    by_id = {row["id"]: row for row in manifest_rows}
    if len(by_id) != 11:
        raise GateError("ledger: duplicate manifest debt id")

    def resolve(debt_id: str, expected: dict[str, Any], trail: tuple[str, ...] = ()) -> str:
        if debt_id in trail:
            raise GateError(f"ledger: supersession cycle {' -> '.join((*trail, debt_id))}")
        if debt_id in active:
            entry = active[debt_id]
            fields = ["class", "severity"] + (["source"] if "source" in expected else [])
            for field in fields:
                if entry.get(field) != expected.get(field):
                    raise GateError(f"ledger: active {debt_id} {field} drift")
            return "active"
        receipt = receipts.get(debt_id)
        if receipt is None:
            raise GateError(f"ledger: {debt_id} is neither active nor closed")
        validate_used_receipt(root, debt_id, receipt)
        disposition = receipt.get("disposition")
        if disposition == "obsolete":
            raise GateError(f"ledger: {debt_id} cannot resolve as obsolete")
        if disposition in {"proved", "implemented"}:
            if expected.get("class") != "obligation":
                raise GateError(f"ledger: {expected.get('class')} {debt_id} cannot become paid")
            return disposition
        if disposition != "superseded":
            raise GateError(f"ledger: unsupported disposition for {debt_id}: {disposition!r}")
        replacement = receipt.get("replacement_id")
        if not isinstance(replacement, str) or not DEBT_ID.fullmatch(replacement):
            raise GateError(f"ledger: {debt_id} has malformed supersession lineage")
        target = by_id.get(replacement, {
            "class": expected.get("class"), "severity": expected.get("severity")
        })
        if replacement in by_id and (
            target.get("class") != expected.get("class")
            or target.get("severity") != expected.get("severity")
        ):
            raise GateError(f"ledger: {debt_id} supersession changes class/severity")
        resolve(replacement, target, (*trail, debt_id))
        return "superseded-lineage"

    states = {row["id"]: resolve(row["id"], row) for row in manifest_rows}
    # The umbrella source prose must retain exactly the declared successor
    # references after closure as well as while active. The receipt removes
    # only the primary marker; it does not erase the decomposed mapping.
    source = read_text(root, umbrella["source"])
    markers = list(PRIMARY.finditer(source))
    if states["U-0160"] == "active":
        index = next((index for index, marker in enumerate(markers)
                      if marker.group(2) == "U-0160"), None)
        if index is None or markers[index].group(1) != "UNDONE":
            raise GateError("ledger: active U-0160 primary marker is absent")
        umbrella_start = markers[index].start()
    else:
        if source.count("The former umbrella") != 1:
            raise GateError("ledger: closed U-0160 source anchor drifted")
        umbrella_start = source.index("The former umbrella")
    umbrella_end = next((marker.start() for marker in markers
                         if marker.start() > umbrella_start), len(source))
    refs = REFERENCE.findall(source[umbrella_start:umbrella_end])
    if refs != expected_refs:
        raise GateError(f"ledger: U-0160 references drifted: {refs}")
    for row in rows:
        if states[row["id"]] == "active":
            source = read_text(root, row["source"])
            if (row["marker"], row["id"]) not in PRIMARY.findall(source):
                raise GateError(f"ledger: active primary marker absent for {row['id']}")


def strip_c_like(text: str, rust: bool = False) -> str:
    """Blank comments and literals while preserving line/byte positions."""
    out = list(text)
    i = 0
    n = len(text)
    while i < n:
        if text.startswith("//", i):
            end = text.find("\n", i + 2)
            end = n if end < 0 else end
            for j in range(i, end): out[j] = " "
            i = end
        elif text.startswith("/*", i):
            depth = 1
            j = i + 2
            while j < n and depth:
                if rust and text.startswith("/*", j): depth += 1; j += 2
                elif text.startswith("*/", j): depth -= 1; j += 2
                else: j += 1
            if depth: raise GateError("unterminated block comment")
            for k in range(i, j):
                if out[k] != "\n": out[k] = " "
            i = j
        elif rust and text[i] == "r":
            match = re.match(r'r(#{0,255})"', text[i:])
            if not match: i += 1; continue
            hashes = match.group(1)
            end_token = '"' + hashes
            end = text.find(end_token, i + len(match.group(0)))
            if end < 0: raise GateError("unterminated Rust raw string")
            end += len(end_token)
            for k in range(i, end):
                if out[k] != "\n": out[k] = " "
            i = end
        elif text[i] == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\": j += 2
                elif text[j] == '"': j += 1; break
                else: j += 1
            else: raise GateError("unterminated string")
            for k in range(i, min(j, n)):
                if out[k] != "\n": out[k] = " "
            i = j
        elif rust and text[i] == "'" and i + 2 < n and (
            text[i + 2] == "'" or (text[i + 1] == "\\" and i + 3 < n and text[i + 3] == "'")
        ):
            j = i + (4 if text[i + 1] == "\\" else 3)
            for k in range(i, j): out[k] = " "
            i = j
        else:
            i += 1
    return "".join(out)


def strip_lean(text: str) -> str:
    out = list(text)
    i = 0
    n = len(text)
    while i < n:
        if text.startswith("--", i):
            end = text.find("\n", i + 2); end = n if end < 0 else end
            for j in range(i, end): out[j] = " "
            i = end
        elif text.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith("/-", j): depth += 1; j += 2
                elif text.startswith("-/", j): depth -= 1; j += 2
                else: j += 1
            if depth: raise GateError("unterminated Lean block comment")
            for k in range(i, j):
                if out[k] != "\n": out[k] = " "
            i = j
        elif text[i] == '"':
            j = i + 1
            while j < n:
                if text[j] == "\\": j += 2
                elif text[j] == '"': j += 1; break
                else: j += 1
            else: raise GateError("unterminated Lean string")
            for k in range(i, min(j, n)):
                if out[k] != "\n": out[k] = " "
            i = j
        else: i += 1
    return "".join(out)


def validate_runtime_surface(root: Path, manifest: dict[str, Any]) -> None:
    surface = manifest["runtime_surface"]
    root_source = root / (surface["root"].replace(".", "/") + ".lean")
    try:
        lean = strip_lean(stable_file_bytes(root_source).decode("utf-8"))
    except UnicodeError as exc:
        raise GateError(f"runtime surface: RuntimeInit is not UTF-8: {exc}") from None
    imports, residue = [], []
    for line in lean.splitlines():
        stripped = line.strip()
        if not stripped: continue
        match = re.fullmatch(r"import\s+([A-Za-z0-9_.]+)", stripped)
        if match: imports.append(match.group(1))
        else: residue.append(stripped)
    if sorted(imports) != surface["direct_imports"] or residue:
        raise GateError(f"runtime surface: RuntimeInit drift; imports={imports}, code={residue}")

    actual_exports: set[tuple[str, str]] = set()
    for path in sorted((root / "Uwueave").rglob("*.lean")):
        try:
            masked = strip_lean(stable_file_bytes(path).decode("utf-8"))
        except UnicodeError as exc:
            raise GateError(f"runtime surface: non-UTF-8 Lean source {path}: {exc}") from None
        relative = path.relative_to(root).as_posix()
        for symbol in re.findall(r"@\[export\s+([A-Za-z_][A-Za-z0-9_]*)\s*\]", masked):
            actual_exports.add((relative, symbol))
    expected_exports = {(e["source"], e["symbol"]) for e in surface["lean_exports"]}
    if actual_exports != expected_exports:
        raise GateError(f"runtime surface: Lean export drift: {sorted(actual_exports ^ expected_exports)}")

    shim = strip_c_like(read_text(root, surface["shim_source"]))
    shim_defs = set(re.findall(
        r"(?m)^\s*(?:void|uint8_t)\s*\*?\s*(shim_uweave_[A-Za-z0-9_]+)\s*\(", shim))
    expected_shim = {e["shim_symbol"] for e in surface["lean_exports"]} | set(surface["shim_support_symbols"])
    if shim_defs != expected_shim:
        raise GateError(f"runtime surface: shim definitions drift: {sorted(shim_defs ^ expected_shim)}")
    lean_calls = set(re.findall(r"(?<!shim_)\b(uwueave_[A-Za-z0-9_]+)\s*\(", shim))
    if lean_calls != {e["symbol"] for e in surface["lean_exports"]}:
        raise GateError(f"runtime surface: shim-to-Lean calls drift: {sorted(lean_calls)}")

    primary = strip_c_like(read_text(root, surface["rust_primary_binding"]), rust=True)
    primary_bindings = set(re.findall(r"\bfn\s+(shim_uweave_[A-Za-z0-9_]+)\s*\(", primary))
    if primary_bindings != expected_shim:
        raise GateError(f"runtime surface: Rust primary bindings drift: {sorted(primary_bindings ^ expected_shim)}")
    for relative, expected in surface["rust_auxiliary_bindings"].items():
        auxiliary = strip_c_like(read_text(root, relative), rust=True)
        actual = set(re.findall(r"\bfn\s+(shim_uweave_[A-Za-z0-9_]+)\s*\(", auxiliary))
        if actual != set(expected):
            raise GateError(f"runtime surface: auxiliary bindings drift in {relative}")


def validate_unsafe(root: Path, manifest: dict[str, Any]) -> None:
    inventory = manifest["unsafe_inventory"]
    expected = inventory["files"]
    seen: dict[str, dict[str, int]] = {}
    for relative_root in inventory["roots"]:
        directory = root / relative_root
        if not directory.exists():
            continue
        for path in sorted(directory.rglob("*.rs")):
            relative = path.relative_to(root).as_posix()
            try:
                masked = strip_c_like(stable_file_bytes(path).decode("utf-8"), rust=True)
            except UnicodeError as exc:
                raise GateError(f"unsafe inventory: non-UTF-8 Rust source {path}: {exc}") from None
            counts = {
                "blocks": len(re.findall(r"\bunsafe\s*\{", masked)),
                "functions": len(re.findall(r"\bunsafe\s+fn\b", masked)),
                "impls": len(re.findall(r"\bunsafe\s+impl\b", masked)),
                "traits": len(re.findall(r"\bunsafe\s+trait\b", masked)),
            }
            if any(counts.values()): seen[relative] = counts
    if seen != expected:
        raise GateError(f"unsafe inventory drift: expected {expected}, got {seen}")


def validate_docs(root: Path, manifest: dict[str, Any]) -> None:
    docs = manifest["documentation"]
    inventory = manifest["unsafe_inventory"]["files"]
    total_unsafe = sum(value["blocks"] for value in inventory.values())
    ffi_unsafe = inventory["rust/src/ffi.rs"]["blocks"]
    benchmark_unsafe = inventory["rust/examples/bench_kernels.rs"]["blocks"]
    legacy_surface_phrases = [
        "five native-kernel modules",
        "Its five imports",
        "are now **eight** Lean exports",
        "All eight have C callers",
        "eight exports in one exact RuntimeInit closure",
        "# 8 exports across the five RuntimeInit kernel modules",
        "Five kernel modules, one exact native closure",
        "Four runtime-kernel modules are authored in Lean",
        "Those modules expose eight functions in total",
        "selects five kernel modules",
        "exact five-module RuntimeInit kernel closure",
    ]
    for relative, link in docs["live_surfaces"].items():
        text = read_text(root, relative)
        if link not in text:
            raise GateError(f"documentation: {relative} does not link {link}")
        for fingerprint in docs["stale_fingerprints"]:
            if fingerprint in text:
                raise GateError(f"documentation: stale live fingerprint {fingerprint!r} in {relative}")
        for phrase in legacy_surface_phrases:
            if phrase in text:
                raise GateError(f"documentation: stale runtime-surface phrase {phrase!r} in {relative}")
        for pattern in docs["unstable_native_patterns"]:
            if re.search(pattern, text):
                raise GateError(f"documentation: unstable native fingerprint pattern in {relative}")
        plain = re.sub(r"<[^>]*>|[`*_]", "", text)
        for value in re.findall(r"\b(\d+)\s+(?:source\s+)?unsafe\s+(?:blocks|occurrences)\b", plain):
            if int(value) != total_unsafe:
                raise GateError(f"documentation: stale total unsafe count in {relative}")
        for value in re.findall(r"\b(\d+)\s+in\s+(?:rust/src/)?ffi\.rs\b", plain):
            if int(value) != ffi_unsafe:
                raise GateError(f"documentation: stale ffi.rs unsafe count in {relative}")
        for value in re.findall(r"\b(\d+)\s+in\s+(?:the\s+)?(?:direct-shim\s+|kernel\s+)?benchmark\b", plain):
            if int(value) != benchmark_unsafe:
                raise GateError(f"documentation: stale benchmark unsafe count in {relative}")
    required_fragments = {
        "README.md": ["six native-kernel modules"],
        "docs/MAP.md": ["Uwueave/RuntimeAuthV4AdmissionTraceKernel.lean", "Its six imports"],
        "docs/COHERENCE.md": ["RuntimeAuthV4AdmissionTraceKernel", "**nine** Lean exports"],
        "docs/index.html": ["Six kernel modules, one exact native closure",
                            "uwueave_runtime_auth_v4_check_admission_trace",
                            "nine exports in one exact RuntimeInit closure"],
    }
    for relative, fragments in required_fragments.items():
        text = read_text(root, relative)
        for fragment in fragments:
            if fragment not in text:
                raise GateError(f"documentation: required runtime-surface fragment absent in {relative}: {fragment!r}")
    for relative in docs["historical_native_observations"]:
        path = root / relative
        if not path.exists():
            continue
        text = read_text(root, relative)
        for fingerprint in docs["stale_fingerprints"][:3]:
            if fingerprint in text and not re.search(r"(?i)\b(dated|historical|checkpoint|observed)\b", text):
                raise GateError(f"documentation: undated historical fingerprint in {relative}")


def validate_policy_integration(root: Path, manifest: dict[str, Any]) -> None:
    native = manifest["native"]
    workflow = read_text(root, native["ci_workflow"])
    required_workflow_fragments = [
        "- os: ubuntu-24.04\n            target: x86_64-unknown-linux-gnu\n"
        "            linker_env: CARGO_TARGET_X86_64_UNKNOWN_LINUX_GNU_LINKER",
        "- os: macos-15\n            target: aarch64-apple-darwin\n"
        "            linker_env: CARGO_TARGET_AARCH64_APPLE_DARWIN_LINKER",
        "UWUEAVE_LEDGER2_OBSERVATION_OUT",
        "printf 'CC=%s\\nAR=%s\\n' \"$compiler\" \"$archiver\"",
        "python3 scripts/ledger2-gate.py observation",
        "--expect-target \"$UWUEAVE_NATIVE_TARGET\"",
    ]
    for fragment in required_workflow_fragments:
        if fragment not in workflow:
            raise GateError(f"policy integration: native workflow fragment absent: {fragment!r}")
    match = re.search(r"(?ms)^  native:\n(?P<body>.*?)(?=^  [A-Za-z0-9_-]+:\n|\Z)", workflow)
    if match is None:
        raise GateError("policy integration: native job is absent")
    native_job = match.group("body")
    if re.search(r"(?m)^\s*(?:if|continue-on-error)\s*:", native_job):
        raise GateError("policy integration: native job/step may not be conditional or soft-failing")
    if re.search(r"(?m)^\s*(?:exit\s+0|return(?:\s|$)|set\s+\+e|exec(?:\s|$))",
                 native_job) or re.search(r"\|\|\s*true(?:\s|$)", native_job):
        raise GateError("policy integration: native job contains an early-success bypass")
    active_workflow_lines = [
        line.strip() for line in native_job.splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]
    required_workflow_lines = [
        "run: cargo test --manifest-path rust/Cargo.toml --frozen --all-targets",
        'UWUEAVE_LEDGER2_OBSERVATION_OUT="$UWUEAVE_LEDGER2_OBSERVATION_PATH" \\',
        "cargo test --manifest-path rust/Cargo.toml --frozen \\",
        "--test runtime_build_closure",
        "python3 scripts/ledger2-gate.py observation \\",
        '--expect-target "$UWUEAVE_NATIVE_TARGET" \\',
        '"$UWUEAVE_LEDGER2_OBSERVATION_PATH"',
    ]
    position = -1
    for line in required_workflow_lines:
        try:
            position = active_workflow_lines.index(line, position + 1)
        except ValueError:
            raise GateError(
                f"policy integration: executable native command absent/out of order: {line!r}"
            ) from None
    policy = read_text(root, native["policy_script"])
    if re.search(r"(?m)^\s*(?:exit\s+0|return(?:\s|$)|set\s+\+e|exec(?:\s|$))", policy) \
            or re.search(r"\|\|\s*true(?:\s|$)", policy):
        raise GateError("policy integration: policy script contains an early-success bypass")
    active_policy_lines = [
        line.strip() for line in policy.splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    ]
    required_policy_lines = [
        "set -euo pipefail",
        "python3 tests/debt_gate_test.py",
        "python3 tests/ledger2_gate_test.py",
        'scripts/debt-gate.py check --base "$debt_registry_base" "${debt_policy_args[@]}"',
        "python3 scripts/ledger2-gate.py check",
        "LC_ALL=C scripts/undone-census.sh --check",
    ]
    position = -1
    for line in required_policy_lines:
        try:
            position = active_policy_lines.index(line, position + 1)
        except ValueError:
            raise GateError(f"policy integration: policy fragment absent/out of order: {line!r}") \
                from None
    if sha256_file(root / native["ci_workflow"]) != CI_WORKFLOW_SHA256 \
            or sha256_file(root / native["policy_script"]) != POLICY_SCRIPT_SHA256:
        raise GateError("policy integration: exact executable enforcement bytes drifted")


def source_snapshot(root: Path) -> tuple[list[dict[str, Any]], str]:
    paths = [root / name for name in [
        "Uwueave.lean", "lakefile.toml", "lake-manifest.json", "lean-toolchain",
        "rust/shim.c", "rust/build.rs", "rust/Cargo.toml", "rust/Cargo.lock",
        MANIFEST.as_posix(),
    ]]
    paths.extend((root / "Uwueave").rglob("*.lean"))
    relative_paths = sorted(
        {path.relative_to(root).as_posix(): path for path in paths}.items(),
        key=lambda item: Path(item[0]).parts,
    )
    digest = hashlib.sha256(b"uwueave.ledger2.source-snapshot.v1\0")
    entries: list[dict[str, Any]] = []
    for relative, path in relative_paths:
        name = relative.encode()
        data = stable_file_bytes(path)
        entries.append({"bytes": len(data), "path": relative,
                        "sha256": hashlib.sha256(data).hexdigest()})
        digest.update(len(name).to_bytes(8, "big")); digest.update(name)
        digest.update(len(data).to_bytes(8, "big")); digest.update(data)
    return entries, digest.hexdigest()


def source_snapshot_sha256(root: Path) -> str:
    return source_snapshot(root)[1]


def absolute_observed_path(text: Any, label: str) -> Path:
    if not isinstance(text, str): raise GateError(f"observation: {label} path is not text")
    path = Path(text)
    if not path.is_absolute(): raise GateError(f"observation: {label} path is not absolute")
    regular_file(path)
    if path.resolve() != path: raise GateError(f"observation: {label} path is not canonical")
    return path


def validate_identity(identity: Any, label: str) -> Path:
    item = expect_keys(identity, {"argv", "path", "sha256", "version"}, f"observation.{label}")
    path = absolute_observed_path(item["path"], label)
    argv = item["argv"]
    if not isinstance(argv, list) or not all(isinstance(x, str) for x in argv) \
            or sum(len(x) for x in argv) > 64 * 1024 \
            or any(not x or len(x) > 4096 or any(c in x for c in "\0\r\n") or x.startswith("@")
                   for x in argv):
        raise GateError(f"observation: {label} argv is malformed")
    if label != "tools.compiler" and argv:
        raise GateError(f"observation: {label} must have an exact empty argv")
    if not isinstance(item["version"], str) or not item["version"].strip():
        raise GateError(f"observation: {label} version is empty")
    if item["sha256"] != sha256_file(path):
        raise GateError(f"observation: {label} executable hash mismatch")
    return path


def selected_invocation(value: str, label: str) -> Path:
    candidate = Path(value)
    if not candidate.is_absolute():
        located = shutil.which(value)
        if located is None:
            raise GateError(f"observation: selected {label} invocation is absent")
        candidate = Path(located)
    try:
        canonical = candidate.resolve(strict=True)
    except OSError as exc:
        raise GateError(f"observation: cannot resolve selected {label} invocation: {exc}") from None
    regular_file(canonical)
    return candidate


def run_ar(archiver: Path, args: list[str]) -> bytes:
    try:
        output = subprocess.run([archiver, *args], check=False, capture_output=True,
                                timeout=30)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise GateError(f"observation: cannot run archiver: {exc}") from None
    if output.returncode:
        raise GateError(f"observation: archiver failed with {output.returncode}")
    return output.stdout


def live_tool_version(path: Path) -> str:
    try:
        output = subprocess.run([path, "--version"], check=False, capture_output=True,
                                timeout=30)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise GateError(f"observation: cannot query tool version: {exc}") from None
    value = (f"exit={output.returncode}\n".encode() + output.stdout + output.stderr)
    if len(value) > 64 * 1024 or b"\0" in value:
        raise GateError("observation: tool version output is malformed/unbounded")
    return value.decode("utf-8", errors="replace")


def resolved_command(value: str, label: str) -> Path:
    candidate = Path(value)
    if not candidate.is_absolute():
        located = shutil.which(value)
        if located is None:
            raise GateError(f"observation: authoritative {label} command is absent")
        candidate = Path(located)
    try:
        canonical = candidate.resolve(strict=True)
    except OSError as exc:
        raise GateError(f"observation: cannot resolve authoritative {label}: {exc}") from None
    regular_file(canonical)
    return canonical


def native_authorities(root: Path, target: str) -> dict[str, Path]:
    launcher = resolved_command("lean", "Lean launcher")
    try:
        output = subprocess.run([launcher, "--print-prefix"], cwd=root, check=False,
                                capture_output=True, text=True, timeout=30)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise GateError(f"observation: cannot query Lean prefix: {exc}") from None
    if output.returncode or not output.stdout.strip() or "\n" in output.stdout.strip():
        raise GateError("observation: Lean launcher returned no exact toolchain prefix")
    try:
        prefix = Path(output.stdout.strip()).resolve(strict=True)
    except OSError as exc:
        raise GateError(f"observation: invalid Lean prefix: {exc}") from None
    extension = "dylib" if target == "aarch64-apple-darwin" else "so"
    linker_key = "CARGO_TARGET_" + target.replace("-", "_").upper() + "_LINKER"
    selected = {
        "archiver": os.environ.get("AR", "ar"),
        "compiler": os.environ.get("CC", "cc"),
        "lake": str(prefix / "bin/lake"),
        "lean": str(prefix / "bin/lean"),
        "linker": os.environ.get(linker_key, ""),
        "verifier_archiver": str(prefix / "bin/llvm-ar"),
        "runtime": str(prefix / f"lib/lean/libleanshared.{extension}"),
    }
    if not selected["linker"]:
        raise GateError(f"observation: authoritative Cargo linker {linker_key} is absent")
    return {name: resolved_command(value, name) if name != "runtime"
            else Path(value).resolve(strict=True) for name, value in selected.items()}


def query_runtime_setup(root: Path, manifest: dict[str, Any],
                        target: str) -> tuple[list[str], str]:
    authorities = native_authorities(root, target)
    lake = authorities["lake"]
    query = "+" + manifest["runtime_surface"]["root"] + ":c"
    try:
        output = subprocess.run([lake, "--no-build", "--quiet", "--json", "query", query],
                                cwd=root, check=False, capture_output=True, timeout=60)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise GateError(f"observation: cannot query RuntimeInit setup: {exc}") from None
    if output.returncode:
        raise GateError(f"observation: no-build RuntimeInit query failed with {output.returncode}")
    try:
        root_c_text = json.loads(output.stdout, object_pairs_hook=_unique_object,
                                 parse_constant=_reject_constant)
    except (json.JSONDecodeError, UnicodeError) as exc:
        raise GateError(f"observation: malformed RuntimeInit query: {exc}") from None
    if not isinstance(root_c_text, str):
        raise GateError("observation: RuntimeInit query did not return one path")
    root_c = absolute_observed_path(root_c_text, "RuntimeInit C")
    module_suffix = Path(*manifest["runtime_surface"]["root"].split(".")).with_suffix(".c")
    if not root_c.is_relative_to(root) or not root_c.is_relative_to(root / ".lake") \
            or not root_c.as_posix().endswith(module_suffix.as_posix()):
        raise GateError("observation: RuntimeInit C escaped the current Lake build tree")
    setup_path = root_c.with_suffix(".setup.json")
    setup_bytes = stable_file_bytes(setup_path)
    try:
        setup = json.loads(setup_bytes, object_pairs_hook=_unique_object,
                           parse_constant=_reject_constant)
    except (json.JSONDecodeError, UnicodeError) as exc:
        raise GateError(f"observation: malformed RuntimeInit setup JSON: {exc}") from None
    expected_keys = {"plugins", "package", "options", "name", "isModule",
                     "importArts", "dynlibs"}
    setup = expect_keys(setup, expected_keys, "observation.RuntimeInit.setup")
    if setup["package"] != "uwueave" or setup["name"] != manifest["runtime_surface"]["root"] \
            or setup["isModule"] is not False or not isinstance(setup["options"], dict) \
            or setup["plugins"] != [] or setup["dynlibs"] != [] \
            or not isinstance(setup["importArts"], dict):
        raise GateError("observation: RuntimeInit setup schema/value drift")
    modules = {manifest["runtime_surface"]["root"]}
    artifact_root: Path | None = None
    for module, artifacts in setup["importArts"].items():
        if not isinstance(module, str) or not re.fullmatch(r"Uwueave(?:\.[A-Za-z0-9_]+)+", module) \
                or not isinstance(artifacts, list) or len(artifacts) != 1 \
                or not isinstance(artifacts[0], str):
            raise GateError("observation: malformed RuntimeInit import artifact")
        artifact = absolute_observed_path(artifacts[0], f"RuntimeInit import {module}")
        suffix = Path(*module.split(".")).with_suffix(".olean")
        if not artifact.is_relative_to(root) or not artifact.is_relative_to(root / ".lake") \
                or not artifact.as_posix().endswith(suffix.as_posix()):
            raise GateError("observation: RuntimeInit import artifact escaped/mismatched")
        root_parts = artifact.parts[:-len(suffix.parts)]
        current_root = Path(*root_parts)
        if artifact_root is None:
            artifact_root = current_root
        elif artifact_root != current_root:
            raise GateError("observation: RuntimeInit import artifacts have mixed roots")
        modules.add(module)
    return sorted(modules), hashlib.sha256(setup_bytes).hexdigest()


def object_target(data: bytes) -> str | None:
    if len(data) >= 20 and data[:4] == b"\x7fELF" and data[4:6] == b"\x02\x01" \
            and int.from_bytes(data[18:20], "little") == 62:
        return "x86_64-unknown-linux-gnu"
    if len(data) >= 12 and data[:4] == b"\xcf\xfa\xed\xfe" \
            and int.from_bytes(data[4:8], "little") == 0x0100000c:
        return "aarch64-apple-darwin"
    return None


def validate_tool_authorities(root: Path, target: str,
                              tools: dict[str, Any]) -> tuple[dict[str, Path], dict[str, Path]]:
    paths = {name: validate_identity(value, f"tools.{name}") for name, value in tools.items()}
    authorities = native_authorities(root, target)
    compiler_argv = tools["compiler"]["argv"]
    prefix_include = str(authorities["lean"].parent.parent / "include")
    if compiler_argv.count("-I") != 1 \
            or compiler_argv[compiler_argv.index("-I") + 1:] == [] \
            or compiler_argv[compiler_argv.index("-I") + 1] != prefix_include \
            or "-O2" not in compiler_argv or "-w" not in compiler_argv \
            or any(argument in {"-c", "-o", "--version"} for argument in compiler_argv):
        raise GateError("observation: compiler argv is not the exact bounded build configuration")
    for role in ("archiver", "compiler", "lake", "lean", "linker", "verifier_archiver"):
        if paths[role] != authorities[role]:
            raise GateError(f"observation: {role} is not the authoritative selected tool")
        version_paths = [paths[role]]
        if role == "compiler":
            invocation = selected_invocation(os.environ.get("CC", "cc"), role)
            if invocation.resolve() != paths[role]:
                raise GateError("observation: compiler invocation resolves to the wrong tool")
            version_paths.append(invocation)
        elif role == "archiver":
            invocation = selected_invocation(os.environ.get("AR", "ar"), role)
            if invocation.resolve() != paths[role]:
                raise GateError("observation: archiver invocation resolves to the wrong tool")
            version_paths.append(invocation)
        if tools[role]["version"] not in {live_tool_version(candidate)
                                           for candidate in version_paths}:
            raise GateError(f"observation: tools.{role} version output mismatch")
    return paths, authorities


def validate_observation(root: Path, manifest: dict[str, Any], path: Path,
                         expect_target: str) -> None:
    observation = parse_json_bytes(path, canonical=True)
    item = expect_keys(observation, {"archive", "closure", "manifest_sha256", "runtime",
                                     "schema", "target", "tools"}, "observation")
    if item["schema"] != manifest["native"]["observation_schema"]:
        raise GateError("observation: schema mismatch")
    allowed = {entry["rust_target"] for entry in manifest["native"]["targets"]}
    if expect_target not in allowed or item["target"] != expect_target:
        raise GateError(f"observation: expected actual supported target {expect_target}")
    if item["manifest_sha256"] != sha256_file(root / MANIFEST):
        raise GateError("observation: manifest hash mismatch")
    closure = expect_keys(item["closure"], {"modules", "setup_sha256", "source_files",
                                            "source_snapshot_sha256"}, "observation.closure")
    modules = closure["modules"]
    if not isinstance(modules, list) or not modules or modules != sorted(set(modules)):
        raise GateError("observation: closure modules must be nonempty, sorted, unique")
    exact_modules, exact_setup_hash = query_runtime_setup(root, manifest, expect_target)
    if modules != exact_modules:
        raise GateError("observation: closure differs from live RuntimeInit setup")
    for field in ("setup_sha256", "source_snapshot_sha256"):
        if not isinstance(closure[field], str) or not HEX64.fullmatch(closure[field]):
            raise GateError(f"observation: malformed {field}")
    if closure["setup_sha256"] != exact_setup_hash:
        raise GateError("observation: RuntimeInit setup identity mismatch")
    expected_source_files, expected_source_hash = source_snapshot(root)
    if closure["source_files"] != expected_source_files:
        raise GateError("observation: source file identity list mismatch")
    if closure["source_snapshot_sha256"] != expected_source_hash:
        raise GateError("observation: source snapshot mismatch")

    tools = expect_keys(item["tools"], {"archiver", "compiler", "lake", "lean", "linker",
                                        "verifier_archiver"}, "observation.tools")
    paths, authorities = validate_tool_authorities(root, expect_target, tools)
    runtime = expect_keys(item["runtime"], {"bytes", "lean_toolchain", "path", "sha256"},
                          "observation.runtime")
    runtime_path = absolute_observed_path(runtime["path"], "runtime")
    if runtime_path != authorities["runtime"]:
        raise GateError("observation: Lean runtime is outside the authoritative toolchain prefix")
    runtime_bytes, runtime_hash, runtime_prefix = stable_file_measure(runtime_path, 64)
    if runtime["bytes"] != runtime_bytes or runtime["sha256"] != runtime_hash:
        raise GateError("observation: Lean runtime identity mismatch")
    toolchain = read_text(root, manifest["native"]["toolchain_authority"]).strip()
    if runtime["lean_toolchain"] != toolchain:
        raise GateError("observation: lean-toolchain identity mismatch")
    if object_target(runtime_prefix) != expect_target:
        raise GateError("observation: Lean runtime architecture does not match target")

    archive = expect_keys(item["archive"], {"bytes", "members", "path", "sha256"},
                          "observation.archive")
    archive_path = absolute_observed_path(archive["path"], "archive")
    archive_bytes, archive_hash, _ = stable_file_measure(archive_path)
    if archive["bytes"] != archive_bytes or archive["sha256"] != archive_hash:
        raise GateError("observation: archive identity mismatch")
    members = archive["members"]
    if not isinstance(members, list) or len(members) != len(modules) + 1:
        raise GateError("observation: archive is not exact closure plus shim")
    names: set[str] = set(); observed_modules: set[str] = set(); shim_count = 0
    listed = run_ar(paths["verifier_archiver"], ["t", str(archive_path)]).decode("utf-8").splitlines()
    if listed != [member.get("name") for member in members]:
        raise GateError(
            f"observation: live archive member order/list differs: listed={listed!r}, "
            f"recorded={[member.get('name') for member in members]!r}"
        )
    for member in members:
        member = expect_keys(member, {"bytes", "kind", "module", "name", "sha256"},
                             "observation.archive.member")
        name = member["name"]
        if not isinstance(name, str) or not name or name in names or "/" in name or "\\" in name:
            raise GateError("observation: invalid/duplicate archive member name")
        names.add(name)
        data = run_ar(paths["verifier_archiver"], ["p", str(archive_path), name])
        if member["bytes"] != len(data) or member["sha256"] != hashlib.sha256(data).hexdigest():
            raise GateError(f"observation: member identity mismatch for {name}")
        if object_target(data[:64]) != expect_target:
            raise GateError(f"observation: archive member architecture mismatch for {name}")
        if member["kind"] == "lake":
            if member["module"] not in modules or member["module"] in observed_modules:
                raise GateError("observation: Lake member/module mapping mismatch")
            observed_modules.add(member["module"])
        elif member["kind"] == "shim" and member["module"] is None and name.endswith("shim.o"):
            shim_count += 1
        else:
            raise GateError("observation: unexpected non-Lake archive member")
    if observed_modules != set(modules) or shim_count != 1:
        raise GateError("observation: archive lacks exact closure plus one shim")
    final_source_files, final_source_hash = source_snapshot(root)
    if final_source_files != expected_source_files or final_source_hash != expected_source_hash:
        raise GateError("observation: source generation changed during validation")
    final_modules, final_setup_hash = query_runtime_setup(root, manifest, expect_target)
    if final_modules != exact_modules or final_setup_hash != exact_setup_hash:
        raise GateError("observation: RuntimeInit setup changed during validation")
    final_paths, final_authorities = validate_tool_authorities(root, expect_target, tools)
    if final_paths != paths or final_authorities != authorities:
        raise GateError("observation: selected tool authorities changed during validation")
    final_runtime_path = final_authorities["runtime"]
    final_runtime_bytes, final_runtime_hash, final_runtime_prefix = stable_file_measure(
        final_runtime_path, 64
    )
    if final_runtime_path != runtime_path or final_runtime_bytes != runtime_bytes \
            or final_runtime_hash != runtime_hash \
            or object_target(final_runtime_prefix) != expect_target:
        raise GateError("observation: Lean runtime changed during validation")
    final_archive_bytes, final_archive_hash, _ = stable_file_measure(archive_path)
    if archive["bytes"] != final_archive_bytes \
            or archive["sha256"] != final_archive_hash \
            or listed != run_ar(paths["verifier_archiver"], ["t", str(archive_path)]).decode(
                "utf-8").splitlines():
        raise GateError("observation: archive changed during validation")


def check(root: Path) -> dict[str, Any]:
    root = root.resolve()
    manifest = load_manifest(root)
    validate_ledger(root, manifest)
    validate_runtime_surface(root, manifest)
    validate_unsafe(root, manifest)
    validate_docs(root, manifest)
    validate_policy_integration(root, manifest)
    return manifest


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    sub = parser.add_subparsers(dest="command", required=True)
    check_parser = sub.add_parser("check")
    check_parser.add_argument("--root", type=Path, default=Path.cwd())
    observation_parser = sub.add_parser("observation")
    observation_parser.add_argument("--root", type=Path, default=Path.cwd())
    observation_parser.add_argument("--expect-target", required=True)
    observation_parser.add_argument("path", type=Path)
    args = parser.parse_args(argv)
    try:
        manifest = check(args.root)
        if args.command == "observation":
            validate_observation(args.root.resolve(), manifest, args.path.resolve(),
                                 args.expect_target)
    except GateError as exc:
        print(f"ledger2-gate: FAIL: {exc}", file=sys.stderr)
        return 1
    print("ledger2-gate: OK" + (f" ({args.expect_target})" if args.command == "observation" else ""))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
