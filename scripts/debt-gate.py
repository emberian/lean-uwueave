#!/usr/bin/env python3
"""Validate Uwueave's stable-ID debt registry and immutable closure receipts.

The production registry is active from immutable baseline commit
6331af269f80c25c26775299b4678c29b45716cc.  ``check`` validates the current
tree and every committed descendant on the ancestry path from that baseline;
the baseline must therefore remain an exact ancestor and must never be
squashed, rebased, amended, or cherry-picked under a different identity.
``audit`` remains a diagnostic report, while ``bootstrap`` is deliberately
guarded and cannot be rerun over existing registry history.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import selectors
import shutil
import signal
import stat
import subprocess
import sys
import tempfile
import time
import tomllib
from dataclasses import dataclass
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple


SCHEMA = 1
ID_RE = re.compile(r"U-[0-9]{4}\Z")
HEX_RE = re.compile(r"[0-9a-f]{64}\Z")
BASE_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9._/@{}^~+\-]*\Z")

# Release policy is structured data over canonical registry fields.  It never
# searches summaries, acceptance text, marker prose, or release documentation.
POLICY_PROFILES = {
    "development-v0.2": {
        "forbid_unclassified": True,
        "forbidden_classes": frozenset(),
        "forbidden_severities": frozenset(),
    },
    "release-v0.2": {
        "forbid_unclassified": True,
        "forbidden_classes": frozenset(),
        "forbidden_severities": frozenset({"P0"}),
    },
    "release-v0.5": {
        "forbid_unclassified": True,
        "forbidden_classes": frozenset({"obligation"}),
        "forbidden_severities": frozenset(),
    },
}
RELEASE_TAG_PROFILES = {
    "v0.2.0": "release-v0.2",
    "v0.5.0": "release-v0.5",
}
DEPRECATED_MILESTONE_PROFILES = {"v0.2": "development-v0.2"}

ACTIVE_KEYS = {
    "acceptance",
    "class",
    "id",
    "marker_sha256",
    "schema",
    "severity",
    "source",
    "summary",
}
RECEIPT_KEYS = {
    "disposition",
    "evidence",
    "id",
    "prior_entry_sha256",
    "prior_marker_sha256",
    "rationale",
    "schema",
}
CLASSES = {"obligation", "premise", "scope", "unclassified"}
SEVERITIES = {"P0", "P1", "P2", "P3"}
DISPOSITIONS = {"proved", "implemented", "obsolete", "superseded"}
TERMINAL_SUPERSESSION_DISPOSITIONS = {"proved", "implemented", "obsolete"}
EVIDENCE_KINDS = {"lean_decl", "case_manifest"}
# Runnable implementation evidence is deliberately Rust-only in schema v1.
# A Python fixture can terminate its own interpreter with ``os._exit(0)`` before
# a trusted in-process unittest wrapper verifies that one test completed.  Rust
# libtest is instead checked out of process by a list pass and an exact result
# transcript below.  More runner kinds require an equally strong supervisor.
CASE_CHECK_KINDS = {"rust_test", "rust_unit"}
EVIDENCE_TIMEOUT_SECONDS = 300
EVIDENCE_OUTPUT_LIMIT = 1024 * 1024
RUST_RELEASE = "1.89.0"
RUSTC_COMMIT = "29483883eed69d5fb4db01964cdf2af4d86e9cb2"
CARGO_COMMIT = "c24e1064277fe51ab72011e2612e556ac56addf7"
LEAN_INSPECTOR_SOURCE = r'''import Lean

open Lean

def debtNameFromString (text : String) : Name :=
  text.splitOn "." |>.foldl (fun name part => name.str part) .anonymous

def debtDeclarationModule? (env : Environment) (declaration : Name) : Option Name := do
  let index ← env.getModuleIdxFor? declaration
  env.header.moduleNames[index.toNat]?

def main (args : List String) : IO UInt32 := do
  let [moduleText, declarationText, oleanText] := args
    | IO.eprintln "debt-inspector: expected module, declaration, and olean"; return 2
  let moduleName := debtNameFromString moduleText
  let declarationName := debtNameFromString declarationText
  let artifacts : NameMap ImportArtifacts :=
    ({} : NameMap ImportArtifacts).insert moduleName
      (.ofArray #[System.FilePath.mk oleanText])
  let env ← importModules #[{ module := moduleName }] {} 0 (arts := artifacts)
  if env.find? declarationName |>.isNone then
    IO.eprintln "debt-inspector: declaration is absent"
    return 3
  if debtDeclarationModule? env declarationName != some moduleName then
    IO.eprintln "debt-inspector: declaration is not owned by the evidence module"
    return 4
  let context : Lean.Core.Context := {
    fileName := "<uwueave-debt-inspector>"
    fileMap := FileMap.ofString ""
  }
  let state : Lean.Core.State := { env := env }
  let axioms : Array Name ← Lean.Core.CoreM.toIO'
    (Lean.collectAxioms declarationName) context state
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let unexpected : Array Name := axioms.filter fun ax => !(allowed.contains ax)
  if unexpected.size != 0 then
    IO.eprintln s!"debt-inspector: unapproved axioms: {unexpected.toList}"
    return 5
  IO.println "debt-inspector: OK"
  return 0
'''
MARKER_CLASS = {
    "UNDONE": {"obligation", "unclassified"},
    "PREMISE": {"premise"},
    "SCOPE": {"scope"},
}
MARKER_DOMAIN = b"uwueave.debt-marker.v1\0"

PRIMARY_RE = re.compile(
    r"⟨(UNDONE|PREMISE|SCOPE) (U-[0-9]{4})(?:⟩|([, \t\n\-–—][^⟩]*)⟩)"
)
REF_RE = re.compile(r"⟨DEBT-REF (U-[0-9]{4})⟩")
DEBT_STEM_RE = re.compile(r"⟨(?:UNDONE|PREMISE|SCOPE|DEBT-REF)\b")
LEGACY_UNDONE_RE = re.compile(r"⟨UNDONE(?=⟩|,|\s|-|–|—)")
UNDONE_WORD_RE = re.compile(r"(?<![A-Za-z0-9_])UNDONE(?![A-Za-z0-9_])")
RAW_STRING_START_RE = re.compile(r'r(#+)"')


class DebtError(Exception):
    """A deterministic, user-facing gate failure."""


@dataclass(frozen=True)
class Marker:
    debt_id: str
    label: str
    source: str
    line: int
    block: str
    marker_sha256: str


@dataclass(frozen=True)
class SourceScan:
    markers: Mapping[str, Marker]
    refs: Tuple[Tuple[str, str, int], ...]
    lean_files: int


def canonical_json(value: Any) -> str:
    return json.dumps(
        value, ensure_ascii=False, allow_nan=False, sort_keys=True, separators=(",", ":")
    )


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def entry_sha256(entry: Mapping[str, Any]) -> str:
    return sha256_bytes(canonical_json(entry).encode("utf-8"))


def _reject_constant(value: str) -> None:
    raise DebtError("non-finite JSON number is forbidden: " + value)


def _unique_object(pairs: Sequence[Tuple[str, Any]]) -> Dict[str, Any]:
    result: Dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise DebtError("duplicate JSON key: " + key)
        result[key] = value
    return result


def parse_json(raw: str, label: str) -> Any:
    try:
        return json.loads(
            raw, object_pairs_hook=_unique_object, parse_constant=_reject_constant
        )
    except DebtError:
        raise
    except (json.JSONDecodeError, UnicodeError) as exc:
        raise DebtError(f"{label}: malformed JSON: {exc}") from None


def decode_canonical_bytes(data: bytes, label: str, allow_empty: bool = False) -> str:
    if data.startswith(b"\xef\xbb\xbf"):
        raise DebtError(f"{label}: UTF-8 BOM is forbidden")
    if b"\r" in data:
        raise DebtError(f"{label}: canonical files use LF, not CR or CRLF")
    if not data and allow_empty:
        return ""
    if not data.endswith(b"\n"):
        raise DebtError(f"{label}: canonical file must end with one LF")
    try:
        return data.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise DebtError(f"{label}: invalid UTF-8: {exc}") from None


def parse_active_bytes(data: bytes, label: str) -> List[Dict[str, Any]]:
    text = decode_canonical_bytes(data, label, allow_empty=True)
    if not text:
        return []
    entries: List[Dict[str, Any]] = []
    for number, line in enumerate(text[:-1].split("\n"), 1):
        if not line:
            raise DebtError(f"{label}:{number}: blank JSONL lines are forbidden")
        value = parse_json(line, f"{label}:{number}")
        if not isinstance(value, dict):
            raise DebtError(f"{label}:{number}: each JSONL row must be an object")
        if canonical_json(value) != line:
            raise DebtError(f"{label}:{number}: row is not canonical compact sorted JSON")
        validate_active_entry(value, f"{label}:{number}")
        entries.append(value)
    ids = [entry["id"] for entry in entries]
    if ids != sorted(ids):
        raise DebtError(f"{label}: rows must be sorted lexicographically by id")
    if len(ids) != len(set(ids)):
        raise DebtError(f"{label}: duplicate active id")
    return entries


def parse_receipt_bytes(data: bytes, label: str) -> Dict[str, Any]:
    text = decode_canonical_bytes(data, label)
    body = text[:-1]
    if "\n" in body:
        raise DebtError(f"{label}: receipt must be one compact JSON line")
    value = parse_json(body, label)
    if not isinstance(value, dict):
        raise DebtError(f"{label}: receipt must be a JSON object")
    if canonical_json(value) != body:
        raise DebtError(f"{label}: receipt is not canonical compact sorted JSON")
    validate_receipt_shape(value, label)
    return value


def parse_case_manifest_bytes(
    data: bytes, label: str, expected_id: Optional[str] = None
) -> Dict[str, Any]:
    text = decode_canonical_bytes(data, label)
    body = text[:-1]
    if "\n" in body:
        raise DebtError(f"{label}: case manifest must be one compact JSON line")
    value = parse_json(body, label)
    if not isinstance(value, dict):
        raise DebtError(f"{label}: case manifest must be a JSON object")
    if canonical_json(value) != body:
        raise DebtError(f"{label}: case manifest is not canonical compact sorted JSON")
    _require_exact_keys(value, {"checks", "id", "schema"}, label)
    _require_schema(value["schema"], label + ".schema")
    debt_id = _require_id(value["id"], label + ".id")
    if expected_id is not None and debt_id != expected_id:
        raise DebtError(f"{label}: manifest id does not match receipt id")
    checks = value["checks"]
    if not isinstance(checks, list) or not checks:
        raise DebtError(f"{label}.checks: expected a nonempty list")
    kinds: List[str] = []
    for index, check in enumerate(checks):
        check_label = f"{label}.checks[{index}]"
        if not isinstance(check, dict):
            raise DebtError(f"{check_label}: check must be an object")
        _require_exact_keys(check, {"kind", "sha256"}, check_label)
        kind = check["kind"]
        if kind not in CASE_CHECK_KINDS:
            raise DebtError(f"{check_label}.kind: unknown case check kind")
        digest = check["sha256"]
        if not isinstance(digest, str) or not HEX_RE.fullmatch(digest):
            raise DebtError(f"{check_label}.sha256: expected lowercase SHA-256 hex")
        kinds.append(kind)
    if kinds != sorted(kinds):
        raise DebtError(f"{label}.checks: checks must be sorted lexicographically by kind")
    if len(kinds) != len(set(kinds)):
        raise DebtError(f"{label}.checks: duplicate case check kind")
    return value


def case_artifact_relative(debt_id: str, kind: str) -> str:
    """Derive the only source path admitted for one case-manifest check."""
    stem = debt_id.replace("-", "_").lower()
    if kind == "rust_test":
        return f"rust/tests/debt_{stem}.rs"
    if kind == "rust_unit":
        return f"rust/src/persistence/debt_{stem}.rs"
    raise DebtError(f"unknown case check kind: {kind}")


def rust_unit_case_binding(debt_id: str) -> Tuple[str, str, str, str]:
    """Derive private module, prefix, selector, and the canonical source hook."""
    stem = debt_id.replace("-", "_").lower()
    module = f"debt_{stem}"
    prefix = f"persistence::record::{module}::"
    selector = prefix + f"debt_closure_{stem}_fault_paths"
    hook = f'#[cfg(test)]\n#[path = "{module}.rs"]\nmod {module};'
    return module, prefix, selector, hook


def _require_exact_keys(value: Mapping[str, Any], keys: Iterable[str], label: str) -> None:
    expected = set(keys)
    actual = set(value)
    missing = sorted(expected - actual)
    unknown = sorted(actual - expected)
    if missing or unknown:
        details: List[str] = []
        if missing:
            details.append("missing=" + ",".join(missing))
        if unknown:
            details.append("unknown=" + ",".join(unknown))
        raise DebtError(f"{label}: wrong key set ({'; '.join(details)})")


def _require_schema(value: Any, label: str) -> None:
    if type(value) is not int or value != SCHEMA:
        raise DebtError(f"{label}: schema must be integer {SCHEMA}")


def _require_id(value: Any, label: str) -> str:
    if not isinstance(value, str) or not ID_RE.fullmatch(value):
        raise DebtError(f"{label}: id must have canonical form U-####")
    return value


def _require_clean_text(value: Any, label: str, allow_empty: bool = False) -> str:
    if not isinstance(value, str):
        raise DebtError(f"{label}: expected a string")
    if "\r" in value or value != value.strip():
        raise DebtError(f"{label}: text must be trimmed and contain no CR")
    if not allow_empty and not value:
        raise DebtError(f"{label}: text must be nonempty")
    return value


def canonical_repo_path(value: Any, label: str, prefixes: Sequence[str], suffix: str) -> str:
    if not isinstance(value, str) or not value or "\\" in value or "\0" in value:
        raise DebtError(f"{label}: expected a canonical repository-relative path")
    path = PurePosixPath(value)
    if path.is_absolute() or any(part in {"", ".", ".."} for part in path.parts):
        raise DebtError(f"{label}: path traversal or noncanonical path is forbidden")
    if str(path) != value or not value.endswith(suffix):
        raise DebtError(f"{label}: expected suffix {suffix} on a canonical path")
    if not any(value.startswith(prefix) for prefix in prefixes):
        raise DebtError(f"{label}: path is outside its allowlisted root")
    return value


def validate_active_entry(value: Mapping[str, Any], label: str) -> None:
    _require_exact_keys(value, ACTIVE_KEYS, label)
    _require_schema(value["schema"], label + ".schema")
    _require_id(value["id"], label + ".id")
    debt_class = value["class"]
    if debt_class not in CLASSES:
        raise DebtError(f"{label}.class: unknown debt class")
    severity = value["severity"]
    if severity is not None and severity not in SEVERITIES:
        raise DebtError(f"{label}.severity: expected P0, P1, P2, P3, or null")
    if debt_class == "obligation":
        if severity not in SEVERITIES:
            raise DebtError(f"{label}: obligation requires a severity")
    canonical_repo_path(value["source"], label + ".source", ("Uwueave/",), ".lean")
    if not isinstance(value["marker_sha256"], str) or not HEX_RE.fullmatch(
        value["marker_sha256"]
    ):
        raise DebtError(f"{label}.marker_sha256: expected lowercase SHA-256 hex")
    _require_clean_text(value["summary"], label + ".summary")
    acceptance = _require_clean_text(
        value["acceptance"], label + ".acceptance", allow_empty=True
    )
    if debt_class == "obligation" and not acceptance:
        raise DebtError(f"{label}: obligation requires nonempty acceptance text")
    if debt_class == "unclassified" and acceptance:
        raise DebtError(f"{label}: unclassified debt must have empty acceptance text")
    if debt_class == "unclassified" and severity is not None:
        raise DebtError(f"{label}: unclassified debt must have null severity")


def validate_receipt_shape(value: Mapping[str, Any], label: str) -> None:
    disposition = value.get("disposition")
    keys = set(RECEIPT_KEYS)
    if disposition == "superseded":
        keys.add("replacement_id")
    _require_exact_keys(value, keys, label)
    _require_schema(value["schema"], label + ".schema")
    debt_id = _require_id(value["id"], label + ".id")
    if disposition not in DISPOSITIONS:
        raise DebtError(f"{label}.disposition: unknown closure disposition")
    for key in ("prior_entry_sha256", "prior_marker_sha256"):
        if not isinstance(value[key], str) or not HEX_RE.fullmatch(value[key]):
            raise DebtError(f"{label}.{key}: expected lowercase SHA-256 hex")
    _require_clean_text(value["rationale"], label + ".rationale")
    evidence = value["evidence"]
    if not isinstance(evidence, list):
        raise DebtError(f"{label}.evidence: expected a list")
    seen: set[str] = set()
    kinds: List[str] = []
    for index, item in enumerate(evidence):
        item_label = f"{label}.evidence[{index}]"
        if not isinstance(item, dict):
            raise DebtError(f"{item_label}: evidence must be an object")
        encoded = canonical_json(item)
        if encoded in seen:
            raise DebtError(f"{label}.evidence: duplicate evidence object")
        seen.add(encoded)
        kind = validate_evidence_shape(debt_id, item, item_label)
        kinds.append(kind)
    if disposition == "proved":
        if kinds != ["lean_decl"]:
            raise DebtError(f"{label}: proved closure requires exactly one Lean declaration")
    elif disposition == "implemented":
        if kinds != ["case_manifest"]:
            raise DebtError(f"{label}: implemented closure requires one case manifest")
    elif disposition == "obsolete":
        if kinds not in (["lean_decl"], ["case_manifest"]):
            raise DebtError(
                f"{label}: obsolete closure requires exactly one executable evidence item"
            )
    elif disposition == "superseded":
        replacement = _require_id(value["replacement_id"], label + ".replacement_id")
        if replacement == debt_id:
            raise DebtError(f"{label}: an item cannot supersede itself")
        if evidence:
            raise DebtError(f"{label}: superseded closure uses replacement_id, not evidence")


def validate_evidence_shape(debt_id: str, item: Mapping[str, Any], label: str) -> str:
    kind = item.get("kind")
    if kind not in EVIDENCE_KINDS:
        raise DebtError(f"{label}.kind: unknown evidence kind")
    _require_exact_keys(item, {"kind", "path", "sha256"}, label)
    path = canonical_repo_path(item["path"], label + ".path", ("scripts/", "tests/"), "")
    digest = item["sha256"]
    if not isinstance(digest, str) or not HEX_RE.fullmatch(digest):
        raise DebtError(f"{label}.sha256: expected lowercase SHA-256 hex")
    stem = debt_id.replace("-", "_")
    if kind == "lean_decl":
        expected_path = f"tests/DebtClosures/{stem}.lean"
        if path != expected_path:
            raise DebtError(f"{label}: Lean declaration path must be exact")
    else:
        expected_path = f"tests/DebtClosures/{stem}.case.json"
        if path != expected_path:
            raise DebtError(f"{label}: case manifest path must be exact")
    return kind


def marker_digest(source: str, debt_id: str, block: str) -> str:
    preimage = (
        MARKER_DOMAIN
        + source.encode("utf-8")
        + b"\0"
        + debt_id.encode("ascii")
        + b"\0"
        + block.encode("utf-8")
    )
    return sha256_bytes(preimage)


def _comment_ranges(text: str, label: str) -> List[Tuple[int, int]]:
    ranges: List[Tuple[int, int]] = []
    index = 0
    length = len(text)
    in_string = False
    escaped = False
    while index < length:
        if in_string:
            char = text[index]
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            index += 1
            continue
        raw_start = RAW_STRING_START_RE.match(text, index)
        if raw_start is not None:
            delimiter = '"' + raw_start.group(1)
            end = text.find(delimiter, raw_start.end())
            if end < 0:
                raise DebtError(f"{label}: unclosed Lean raw string")
            index = end + len(delimiter)
            continue
        if text.startswith("--", index):
            end = text.find("\n", index)
            if end < 0:
                end = length
            ranges.append((index, end))
            index = end
            continue
        if text.startswith("/-", index):
            start = index
            depth = 1
            index += 2
            while index < length and depth:
                if text.startswith("/-", index):
                    depth += 1
                    index += 2
                elif text.startswith("-/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            if depth:
                raise DebtError(f"{label}: unclosed Lean block comment")
            ranges.append((start, index))
            continue
        if text[index] == '"':
            in_string = True
        index += 1
    return ranges


def _inside_comment(start: int, end: int, ranges: Sequence[Tuple[int, int]]) -> bool:
    for comment_start, comment_end in ranges:
        if comment_start <= start and end <= comment_end:
            return True
        if comment_start > start:
            return False
    return False


def _marker_block(text: str, marker_start: int) -> str:
    lines = text.split("\n")
    start_line = text.count("\n", 0, marker_start)
    selected = [lines[start_line].rstrip(" \t")]
    if "-/" in lines[start_line]:
        return selected[0] + "\n"
    for line in lines[start_line + 1 :]:
        if (
            re.match(r"^[ \t]*$", line)
            or re.match(r"^[ \t]*\*[ \t]", line)
            or re.match(r"^[ \t]*#+[ \t]", line)
            or re.match(r"^[ \t]*-/[ \t]*$", line)
        ):
            break
        selected.append(line.rstrip(" \t"))
        if "-/" in line:
            break
    return "\n".join(selected) + "\n"


def _safe_relative(root: Path, path: Path, label: str) -> str:
    lexical_root = Path(os.path.abspath(root))
    lexical_path = Path(os.path.abspath(path))
    try:
        relative = lexical_path.relative_to(lexical_root)
    except ValueError:
        raise DebtError(f"{label}: path escapes the repository root") from None
    try:
        resolved_root = root.resolve(strict=True)
    except FileNotFoundError:
        raise DebtError(f"{label}: repository root is missing") from None
    cursor = resolved_root
    for part in relative.parts:
        cursor = cursor / part
        if cursor.is_symlink():
            raise DebtError(f"{label}: symlinks are forbidden")
    try:
        resolved = (resolved_root / relative).resolve(strict=True)
        resolved.relative_to(resolved_root)
    except (FileNotFoundError, ValueError):
        raise DebtError(f"{label}: path is missing or escapes the repository root") from None
    return relative.as_posix()


def safe_regular_file(root: Path, path: Path, label: str) -> str:
    relative = _safe_relative(root, path, label)
    if not path.is_file():
        raise DebtError(f"{label}: expected a regular file")
    return relative


def safe_directory(root: Path, path: Path, label: str) -> str:
    relative = _safe_relative(root, path, label)
    if not path.is_dir():
        raise DebtError(f"{label}: expected a directory")
    return relative


def _decode_lean(data: bytes, label: str) -> str:
    if data.startswith(b"\xef\xbb\xbf"):
        raise DebtError(f"{label}: UTF-8 BOM is forbidden")
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise DebtError(f"{label}: invalid UTF-8: {exc}") from None
    return text.replace("\r\n", "\n").replace("\r", "\n")


def _scan_documents(documents: Mapping[str, str]) -> SourceScan:
    if not documents:
        raise DebtError("no Lean sources found below Uwueave/")
    markers: Dict[str, Marker] = {}
    refs: List[Tuple[str, str, int]] = []
    for source in sorted(documents):
        text = documents[source]
        comments = _comment_ranges(text, source)
        canonical_undone_spans: set[Tuple[int, int]] = set()
        covered_until = -1
        for stem in DEBT_STEM_RE.finditer(text):
            if stem.start() < covered_until:
                raise DebtError(f"{source}: mixed or nested debt markers are forbidden")
            primary = PRIMARY_RE.match(text, stem.start())
            reference = REF_RE.match(text, stem.start())
            match = primary or reference
            line = text.count("\n", 0, stem.start()) + 1
            if match is None:
                raise DebtError(f"{source}:{line}: legacy or malformed debt marker")
            covered_until = match.end()
            if not _inside_comment(match.start(), match.end(), comments):
                raise DebtError(f"{source}:{line}: debt marker must be inside a Lean comment")
            if reference is not None:
                refs.append((reference.group(1), source, line))
                continue
            assert primary is not None
            label_name, debt_id = primary.group(1), primary.group(2)
            if label_name == "UNDONE":
                canonical_undone_spans.add(primary.span(1))
            if debt_id in markers:
                prior = markers[debt_id]
                raise DebtError(
                    f"{source}:{line}: duplicate primary {debt_id}; first at "
                    f"{prior.source}:{prior.line}"
                )
            block = _marker_block(text, primary.start())
            markers[debt_id] = Marker(
                debt_id=debt_id,
                label=label_name,
                source=source,
                line=line,
                block=block,
                marker_sha256=marker_digest(source, debt_id, block),
            )
        for occurrence in UNDONE_WORD_RE.finditer(text):
            if occurrence.span() not in canonical_undone_spans:
                line = text.count("\n", 0, occurrence.start()) + 1
                raise DebtError(f"{source}:{line}: legacy or mixed raw UNDONE occurrence")
    return SourceScan(markers=markers, refs=tuple(refs), lean_files=len(documents))


def worktree_lean_paths(root: Path) -> List[Path]:
    source_root = root / "Uwueave"
    safe_directory(root, source_root, "Uwueave/")
    paths: List[Path] = []
    for path in sorted(source_root.rglob("*")):
        if path.is_symlink():
            raise DebtError(f"{path}: symlinks are forbidden below Uwueave/")
        if path.is_file() and path.suffix == ".lean":
            paths.append(path)
    return paths


def scan_sources(root: Path) -> SourceScan:
    paths = worktree_lean_paths(root)
    documents: Dict[str, str] = {}
    for path in paths:
        source = safe_regular_file(root, path, path.relative_to(root).as_posix())
        documents[source] = _decode_lean(path.read_bytes(), source)
    return _scan_documents(documents)


def audit_sources(root: Path) -> Dict[str, Any]:
    paths = worktree_lean_paths(root)
    if not paths:
        raise DebtError("no Lean sources found below Uwueave/")
    canonical = 0
    refs = 0
    debt_stems = 0
    legacy_undone = 0
    raw_undone = 0
    for path in paths:
        source = safe_regular_file(root, path, path.relative_to(root).as_posix())
        text = _decode_lean(path.read_bytes(), source)
        canonical += len(list(PRIMARY_RE.finditer(text)))
        refs += len(list(REF_RE.finditer(text)))
        debt_stems += len(list(DEBT_STEM_RE.finditer(text)))
        legacy_undone += len(list(LEGACY_UNDONE_RE.finditer(text)))
        raw_undone += len(list(UNDONE_WORD_RE.finditer(text)))
    active_path = root / "docs/debt/active.jsonl"
    closed_dir = root / "docs/debt/closed"
    receipt_count = len(list(closed_dir.glob("U-*.json"))) if closed_dir.is_dir() else 0
    return {
        "active_registry": active_path.is_file(),
        "canonical_primary": canonical,
        "closed_receipts": receipt_count,
        "debt_refs": refs,
        "debt_stems": debt_stems,
        "lean_files": len(paths),
        "legacy_or_malformed": debt_stems - canonical - refs,
        "undone_family_occurrences": legacy_undone,
        "mode": "audit-only",
        "normal_check_enabled": False,
        "raw_undone_words": raw_undone,
        "schema": SCHEMA,
    }


def read_active(root: Path) -> Tuple[bytes, List[Dict[str, Any]]]:
    path = root / "docs/debt/active.jsonl"
    if path.is_symlink():
        raise DebtError("docs/debt/active.jsonl: symlinks are forbidden")
    if not path.is_file():
        raise DebtError("docs/debt/active.jsonl is absent; normal check awaits migration")
    safe_regular_file(root, path, "docs/debt/active.jsonl")
    data = path.read_bytes()
    return data, parse_active_bytes(data, "docs/debt/active.jsonl")


def read_receipts(root: Path) -> Tuple[Dict[str, bytes], Dict[str, Dict[str, Any]]]:
    directory = root / "docs/debt/closed"
    raw: Dict[str, bytes] = {}
    parsed: Dict[str, Dict[str, Any]] = {}
    if directory.is_symlink():
        raise DebtError("docs/debt/closed: symlinks are forbidden")
    if not directory.exists():
        return raw, parsed
    safe_directory(root, directory, "docs/debt/closed")
    for path in sorted(directory.iterdir()):
        if not path.is_file() or not re.fullmatch(r"U-[0-9]{4}\.json", path.name):
            raise DebtError(f"docs/debt/closed/{path.name}: unexpected receipt path")
        safe_regular_file(root, path, f"docs/debt/closed/{path.name}")
        data = path.read_bytes()
        receipt = parse_receipt_bytes(data, f"docs/debt/closed/{path.name}")
        debt_id = path.stem
        if receipt["id"] != debt_id:
            raise DebtError(f"docs/debt/closed/{path.name}: filename/id mismatch")
        raw[debt_id] = data
        parsed[debt_id] = receipt
    return raw, parsed


def _run_git(root: Path, args: Sequence[str]) -> bytes:
    process = subprocess.run(
        ["git", *args], cwd=root, stdout=subprocess.PIPE, stderr=subprocess.PIPE
    )
    if process.returncode == 0:
        return process.stdout
    detail = process.stderr.decode("utf-8", errors="replace").strip()
    raise DebtError(f"git {' '.join(args)} failed: {detail}")


def ensure_repository_root(root: Path) -> None:
    output = _run_git(root, ["rev-parse", "--show-toplevel"])
    try:
        actual = Path(output.decode("utf-8").strip()).resolve(strict=True)
    except (UnicodeDecodeError, FileNotFoundError):
        raise DebtError("git returned an invalid repository root") from None
    if actual != root.resolve(strict=True):
        raise DebtError("--root must be the exact Git repository top level")


def resolve_base(root: Path, base: str) -> str:
    ensure_repository_root(root)
    if not BASE_RE.fullmatch(base):
        raise DebtError("--base contains unsupported revision syntax")
    output = _run_git(root, ["rev-parse", "--verify", f"{base}^{{commit}}"])
    return output.decode("ascii").strip()


def ensure_base_ancestor(root: Path, base: str) -> None:
    process = subprocess.run(
        ["git", "merge-base", "--is-ancestor", base, "HEAD"],
        cwd=root,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    if process.returncode == 0:
        return
    if process.returncode == 1:
        raise DebtError("comparison base is not an ancestor of HEAD")
    detail = process.stderr.decode("utf-8", errors="replace").strip()
    raise DebtError(f"git merge-base --is-ancestor failed: {detail}")


def git_path_entry(root: Path, base: str, path: str) -> Optional[Tuple[str, str, str]]:
    output = _run_git(root, ["ls-tree", "-z", base, "--", path])
    if not output:
        return None
    records = [record for record in output.split(b"\0") if record]
    if len(records) != 1:
        raise DebtError(f"{base}:{path}: ambiguous Git tree entry")
    try:
        metadata, recorded = records[0].split(b"\t", 1)
        mode, kind, object_id = metadata.decode("ascii").split(" ")
        recorded_path = recorded.decode("utf-8")
    except (ValueError, UnicodeDecodeError):
        raise DebtError(f"{base}:{path}: malformed Git tree entry") from None
    if recorded_path != path:
        raise DebtError(f"{base}:{path}: Git tree returned a different path")
    return mode, kind, object_id


def git_file(root: Path, base: str, path: str) -> Optional[bytes]:
    result = git_regular_blob(root, base, path)
    return None if result is None else result[1]


def git_regular_blob(
    root: Path, base: str, path: str
) -> Optional[Tuple[str, bytes]]:
    entry = git_path_entry(root, base, path)
    if entry is None:
        return None
    mode, kind, object_id = entry
    if kind != "blob" or mode not in {"100644", "100755"}:
        raise DebtError(f"{base}:{path}: expected a regular tracked blob, found {mode} {kind}")
    return mode, _run_git(root, ["cat-file", "blob", object_id])


def read_base_receipts(
    root: Path, base: str
) -> Tuple[Dict[str, bytes], Dict[str, Dict[str, Any]]]:
    listing = _run_git(
        root, ["ls-tree", "-r", "-z", "--name-only", base, "--", "docs/debt/closed"]
    )
    receipt_raw: Dict[str, bytes] = {}
    receipts: Dict[str, Dict[str, Any]] = {}
    try:
        paths = [item.decode("utf-8") for item in listing.split(b"\0") if item]
    except UnicodeDecodeError:
        raise DebtError(f"{base}:docs/debt/closed: non-UTF-8 path") from None
    for path in paths:
        match = re.fullmatch(r"docs/debt/closed/(U-[0-9]{4})\.json", path)
        if match is None:
            raise DebtError(f"{base}:{path}: unexpected base receipt path")
        data = git_file(root, base, path)
        if data is None:
            raise DebtError(f"{base}:{path}: listed receipt blob disappeared")
        receipt = parse_receipt_bytes(data, f"{base}:{path}")
        debt_id = match.group(1)
        if receipt["id"] != debt_id:
            raise DebtError(f"{base}:{path}: filename/id mismatch")
        receipt_raw[debt_id] = data
        receipts[debt_id] = receipt
    return receipt_raw, receipts


def read_base_state(
    root: Path, base: str
) -> Tuple[List[Dict[str, Any]], Dict[str, bytes], Dict[str, Dict[str, Any]]]:
    active_raw = git_file(root, base, "docs/debt/active.jsonl")
    if active_raw is None:
        raise DebtError("base has no debt registry; use guarded bootstrap for initial migration")
    active = parse_active_bytes(active_raw, f"{base}:docs/debt/active.jsonl")
    receipt_raw, receipts = read_base_receipts(root, base)
    return active, receipt_raw, receipts


def scan_base_sources(root: Path, base: str) -> SourceScan:
    listing = _run_git(root, ["ls-tree", "-r", "-z", "--name-only", base, "--", "Uwueave"])
    documents: Dict[str, str] = {}
    try:
        paths = [item.decode("utf-8") for item in listing.split(b"\0") if item]
    except UnicodeDecodeError:
        raise DebtError(f"{base}:Uwueave: non-UTF-8 path") from None
    for path in paths:
        if not re.fullmatch(r"Uwueave/(?:[^/]+/)*[^/]+\.lean", path):
            continue
        data = git_file(root, base, path)
        if data is None:
            raise DebtError(f"{base}:{path}: listed Lean blob disappeared")
        documents[path] = _decode_lean(data, f"{base}:{path}")
    return _scan_documents(documents)


def worktree_lean_snapshot(root: Path) -> Dict[str, str]:
    result: Dict[str, str] = {}
    for path in worktree_lean_paths(root):
        relative = safe_regular_file(root, path, "Lean source snapshot")
        result[relative] = sha256_bytes(path.read_bytes())
    return result


def base_lean_snapshot(root: Path, base: str) -> Dict[str, str]:
    listing = _run_git(root, ["ls-tree", "-r", "-z", "--name-only", base, "--", "Uwueave"])
    try:
        paths = [item.decode("utf-8") for item in listing.split(b"\0") if item]
    except UnicodeDecodeError:
        raise DebtError(f"{base}:Uwueave: non-UTF-8 path") from None
    result: Dict[str, str] = {}
    for path in paths:
        if not re.fullmatch(r"Uwueave/(?:[^/]+/)*[^/]+\.lean", path):
            continue
        data = git_file(root, base, path)
        if data is None:
            raise DebtError(f"{base}:{path}: listed Lean blob disappeared")
        result[path] = sha256_bytes(data)
    return result


def ensure_tracked_regular(root: Path, relative: str, label: str) -> Path:
    path = root / relative
    safe_regular_file(root, path, label)
    output = _run_git(root, ["ls-files", "--stage", "-z", "--", relative])
    records = [record for record in output.split(b"\0") if record]
    if len(records) != 1:
        raise DebtError(f"{label}: evidence must be one tracked stage-0 file")
    try:
        metadata, recorded = records[0].split(b"\t", 1)
        mode, object_id, stage = metadata.decode("ascii").split(" ")
        recorded_path = recorded.decode("utf-8")
    except (ValueError, UnicodeDecodeError):
        raise DebtError(f"{label}: malformed Git index entry") from None
    if mode not in {"100644", "100755"} or stage != "0" or recorded_path != relative:
        raise DebtError(f"{label}: evidence must be one tracked regular stage-0 file")
    index_content = _run_git(root, ["cat-file", "blob", object_id])
    if index_content != path.read_bytes():
        raise DebtError(f"{label}: evidence bytes must exactly match the Git index")
    worktree_executable = bool(path.stat().st_mode & stat.S_IXUSR)
    if worktree_executable != (mode == "100755"):
        raise DebtError(f"{label}: evidence executable mode must match the Git index")
    return path


def _evidence_environment(executables: Sequence[str], root: Path) -> Dict[str, str]:
    path_parts = [str(Path(item).absolute().parent) for item in executables]
    path_parts.extend(["/usr/local/bin", "/usr/bin", "/bin"])
    environment = {
        "CARGO_BUILD_JOBS": "1",
        "CARGO_TERM_COLOR": "never",
        "HOME": os.environ.get("HOME", str(root)),
        "LANG": "C",
        "LC_ALL": "C",
        "NO_COLOR": "1",
        "PATH": os.pathsep.join(dict.fromkeys(path_parts)),
        "PYTHONDONTWRITEBYTECODE": "1",
        "TMPDIR": tempfile.gettempdir(),
    }
    # CI installs elan below a job-private ELAN_HOME, while rustup installations
    # may similarly use job-private homes or an explicit exact toolchain.  Keep
    # only these narrowly validated selectors; do not inherit the ambient PATH.
    for key in ("ELAN_HOME", "RUSTUP_HOME", "CARGO_HOME"):
        value = os.environ.get(key)
        if value is None:
            continue
        if not os.path.isabs(value) or any(char in value for char in "\0\r\n"):
            raise DebtError(f"evidence environment: {key} must be an absolute clean path")
        environment[key] = value
    toolchain = os.environ.get("RUSTUP_TOOLCHAIN")
    if toolchain is not None:
        if not re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]*", toolchain):
            raise DebtError(
                "evidence environment: RUSTUP_TOOLCHAIN must be a simple exact name"
            )
        environment["RUSTUP_TOOLCHAIN"] = toolchain
    return environment


def _execute_evidence_command(
    root: Path,
    argv: Sequence[str],
    executable: str,
    label: str,
    path_executables: Sequence[str] = (),
) -> str:
    actual_argv = [executable, *argv[1:]]
    process = subprocess.Popen(
        actual_argv,
        cwd=root,
        env=_evidence_environment([executable, *path_executables], root),
        stdin=subprocess.DEVNULL,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        start_new_session=True,
    )
    assert process.stdout is not None
    output = bytearray()
    deadline = time.monotonic() + EVIDENCE_TIMEOUT_SECONDS
    selector = selectors.DefaultSelector()
    selector.register(process.stdout, selectors.EVENT_READ)
    exceeded = False

    def stop_process() -> None:
        if process.poll() is not None:
            return
        try:
            os.killpg(process.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        except PermissionError:
            # Some hosts deny process-group signals despite start_new_session;
            # still reap the direct runner and fail the gate closed.
            try:
                process.kill()
            except ProcessLookupError:
                pass
        process.wait()

    try:
        while selector.get_map():
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                stop_process()
                raise DebtError(
                    f"{label}: evidence command timed out after {EVIDENCE_TIMEOUT_SECONDS}s"
                )
            for key, _ in selector.select(timeout=min(remaining, 0.25)):
                chunk = os.read(key.fd, 65536)
                if not chunk:
                    selector.unregister(key.fileobj)
                    continue
                output.extend(chunk)
                if len(output) > EVIDENCE_OUTPUT_LIMIT:
                    exceeded = True
                    stop_process()
                    selector.unregister(key.fileobj)
                    break
        if exceeded:
            raise DebtError(f"{label}: evidence command exceeded output limit")
        returncode = process.wait(timeout=max(0.0, deadline - time.monotonic()))
    except subprocess.TimeoutExpired:
        stop_process()
        raise DebtError(
            f"{label}: evidence command timed out after {EVIDENCE_TIMEOUT_SECONDS}s"
        ) from None
    finally:
        selector.close()
        process.stdout.close()
    text = bytes(output).decode("utf-8", errors="replace")
    if returncode != 0:
        detail = text[-4000:].strip()
        raise DebtError(f"{label}: evidence command failed ({returncode}): {detail}")
    return text


def _resolved_executable(candidate: str, label: str) -> str:
    resolved = shutil.which(candidate)
    if resolved is None:
        raise DebtError(f"{label}: required evidence runner {candidate} is unavailable")
    # Preserve a multicall symlink's basename (for example cargo -> rustup).
    return str(Path(resolved).absolute())


def _version_fields(output: str) -> Dict[str, str]:
    fields: Dict[str, str] = {}
    for line in output.splitlines():
        key, separator, value = line.partition(":")
        if separator and key and value.startswith(" "):
            fields[key] = value[1:]
    return fields


def validate_rust_toolchain(
    root: Path, cargo: str, rustc: str, lake: str, label: str
) -> None:
    path_executables = [rustc, lake]
    rustc_output = _execute_evidence_command(
        root,
        ["rustc", "--version", "--verbose"],
        rustc,
        label + ".rustc-version",
        [cargo, lake],
    )
    rustc_fields = _version_fields(rustc_output)
    if (
        rustc_fields.get("release") != RUST_RELEASE
        or rustc_fields.get("commit-hash") != RUSTC_COMMIT
    ):
        raise DebtError(
            f"{label}: Rust evidence requires official rustc {RUST_RELEASE} ({RUSTC_COMMIT})"
        )
    cargo_output = _execute_evidence_command(
        root,
        ["cargo", "--version", "--verbose"],
        cargo,
        label + ".cargo-version",
        path_executables,
    )
    cargo_fields = _version_fields(cargo_output)
    if (
        cargo_fields.get("release") != RUST_RELEASE
        or cargo_fields.get("commit-hash") != CARGO_COMMIT
    ):
        raise DebtError(
            f"{label}: Rust evidence requires official cargo {RUST_RELEASE} ({CARGO_COMMIT})"
        )


def validate_lean_declaration(
    root: Path,
    debt_id: str,
    content: bytes,
    declaration: str,
    executable: str,
    label: str,
) -> None:
    temporary = Path(tempfile.mkdtemp(prefix="DebtGateEvidence_", dir=root))
    try:
        module_leaf = debt_id.replace("-", "_")
        source = temporary / f"{module_leaf}.lean"
        olean = temporary / f"{module_leaf}.olean"
        inspector = temporary / "Inspector.lean"
        source.write_bytes(content)
        inspector.write_text(LEAN_INSPECTOR_SOURCE, encoding="utf-8")
        source_relative = source.relative_to(root).as_posix()
        olean_relative = olean.relative_to(root).as_posix()
        inspector_relative = inspector.relative_to(root).as_posix()
        _execute_evidence_command(
            root,
            ["lake", "env", "lean", "-o", olean_relative, source_relative],
            executable,
            label + ".compile",
        )
        module_name = f"{temporary.name}.{module_leaf}"
        output = _execute_evidence_command(
            root,
            [
                "lake",
                "env",
                "lean",
                "--run",
                inspector_relative,
                module_name,
                declaration,
                str(olean),
            ],
            executable,
            label + ".inspect",
        )
        if output.strip() != "debt-inspector: OK":
            raise DebtError(f"{label}: trusted Lean inspector did not emit exact OK")
    finally:
        shutil.rmtree(temporary)


def _decode_rust_source(data: bytes, label: str) -> str:
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as exc:
        raise DebtError(f"{label}: Rust source is not UTF-8: {exc}") from None
    if "\0" in text or "\r" in text:
        raise DebtError(f"{label}: Rust source contains NUL or CR")
    return text


def _rust_without_comments(text: str, label: str) -> str:
    """Mask Rust comments while preserving lines and string literals.

    This is intentionally a small lexical check, not a Rust parser.  It knows
    nested block comments plus ordinary/raw string and character literals so a
    commented or quoted module hook cannot satisfy the evidence binding.
    """
    result = list(text)
    index = 0
    length = len(text)

    def mask(start: int, stop: int) -> None:
        for position in range(start, stop):
            if result[position] != "\n":
                result[position] = " "

    while index < length:
        if text.startswith("//", index):
            stop = text.find("\n", index + 2)
            if stop < 0:
                stop = length
            mask(index, stop)
            index = stop
            continue
        if text.startswith("/*", index):
            start = index
            depth = 1
            index += 2
            while index < length and depth:
                if text.startswith("/*", index):
                    depth += 1
                    index += 2
                elif text.startswith("*/", index):
                    depth -= 1
                    index += 2
                else:
                    index += 1
            if depth:
                raise DebtError(f"{label}: unterminated Rust block comment")
            mask(start, index)
            continue

        raw_start = index
        if text.startswith("br", index):
            raw_start = index + 1
        if text.startswith("r", raw_start):
            cursor = raw_start + 1
            while cursor < length and text[cursor] == "#":
                cursor += 1
            if cursor < length and text[cursor] == '"':
                hashes = cursor - raw_start - 1
                terminator = '"' + ("#" * hashes)
                stop = text.find(terminator, cursor + 1)
                if stop < 0:
                    raise DebtError(f"{label}: unterminated Rust raw string")
                index = stop + len(terminator)
                continue

        quote_index = index + 1 if text.startswith(('b"', "b'"), index) else index
        if quote_index < length and text[quote_index] in {'"', "'"}:
            quote = text[quote_index]
            # Apostrophes beginning lifetimes are not character literals.
            if quote == "'" and re.match(r"[A-Za-z_]", text[quote_index + 1 : quote_index + 2]):
                close = text.find("'", quote_index + 2)
                if close < 0 or "\n" in text[quote_index + 1 : close]:
                    index = quote_index + 1
                    continue
            cursor = quote_index + 1
            escaped = False
            while cursor < length:
                char = text[cursor]
                if char == "\n" and quote == '"':
                    raise DebtError(f"{label}: unterminated Rust string literal")
                if not escaped and char == quote:
                    index = cursor + 1
                    break
                if not escaped and char == "\\":
                    escaped = True
                else:
                    escaped = False
                cursor += 1
            else:
                raise DebtError(f"{label}: unterminated Rust literal")
            continue
        index += 1
    return "".join(result)


def _require_plain_module_line(
    data: bytes, expected_line: str, module_name: str, label: str
) -> None:
    source = _rust_without_comments(_decode_rust_source(data, label), label)
    significant = [line.strip() for line in source.splitlines() if line.strip()]
    if significant.count(expected_line) != 1:
        raise DebtError(f"{label}: missing or duplicate exact module declaration {expected_line}")
    index = significant.index(expected_line)
    if index > 0 and significant[index - 1].startswith("#["):
        raise DebtError(f"{label}: module {module_name} must not be redirected or cfg-gated")


def _require_exact_test_module_block(
    data: bytes, expected_block: str, module_name: str, label: str
) -> None:
    source = _rust_without_comments(_decode_rust_source(data, label), label)
    significant = [line.strip() for line in source.splitlines() if line.strip()]
    expected = [line.strip() for line in expected_block.splitlines() if line.strip()]
    starts = [
        index
        for index in range(len(significant) - len(expected) + 1)
        if significant[index : index + len(expected)] == expected
    ]
    if len(starts) != 1:
        raise DebtError(f"{label}: missing or duplicate exact module declaration block")
    index = starts[0]
    if significant.count(f"mod {module_name};") != 1:
        raise DebtError(f"{label}: missing or duplicate exact module declaration")
    if index > 0 and significant[index - 1].startswith("#["):
        raise DebtError(f"{label}: module {module_name} has an unapproved attribute")


def _validate_rust_unit_chain_bytes(
    debt_id: str,
    cargo_bytes: bytes,
    lib_bytes: bytes,
    persistence_bytes: bytes,
    record_bytes: bytes,
    label: str,
) -> Tuple[str, str]:
    try:
        cargo_text = cargo_bytes.decode("utf-8")
        cargo_data = tomllib.loads(cargo_text)
    except (UnicodeError, tomllib.TOMLDecodeError) as exc:
        raise DebtError(f"{label}: rust/Cargo.toml is not valid UTF-8 TOML: {exc}") from None
    package = cargo_data.get("package")
    if not isinstance(package, dict) or not isinstance(package.get("name"), str):
        raise DebtError(f"{label}: Cargo package must have one string name")
    library = cargo_data.get("lib", {})
    if not isinstance(library, dict):
        raise DebtError(f"{label}: Cargo [lib] must be a table")
    if library.get("path", "src/lib.rs") != "src/lib.rs":
        raise DebtError(f"{label}: Cargo redirects the standard library source")
    if library.get("harness", True) is not True:
        raise DebtError(f"{label}: Rust debt unit must use the standard library harness")
    if library.get("test", True) is not True:
        raise DebtError(f"{label}: Rust debt unit library tests must remain enabled")
    if library.get("crate-type", ["lib"]) != ["lib"]:
        raise DebtError(f"{label}: Rust debt unit requires the standard lib crate type")

    _require_plain_module_line(
        lib_bytes, "pub mod persistence;", "persistence", label + ".lib-source"
    )
    _require_plain_module_line(
        persistence_bytes, "mod record;", "record", label + ".persistence-source"
    )
    module, _, _, hook = rust_unit_case_binding(debt_id)
    _require_exact_test_module_block(record_bytes, hook, module, label + ".record-source")
    library_name = library.get("name", package["name"].replace("-", "_"))
    if not isinstance(library_name, str) or not library_name:
        raise DebtError(f"{label}: Cargo library must have one string name")
    return package["name"], library_name


def _reject_repository_cargo_config(root: Path, label: str) -> None:
    for relative in (
        ".cargo/config",
        ".cargo/config.toml",
        "rust/.cargo/config",
        "rust/.cargo/config.toml",
    ):
        if (root / relative).exists() or (root / relative).is_symlink():
            raise DebtError(
                f"{label}: repository Cargo config is forbidden for immutable evidence"
            )


def _reject_committed_cargo_config(root: Path, commit: str, label: str) -> None:
    for relative in (
        ".cargo/config",
        ".cargo/config.toml",
        "rust/.cargo/config",
        "rust/.cargo/config.toml",
    ):
        if git_path_entry(root, commit, relative) is not None:
            raise DebtError(
                f"{label}: committed repository Cargo config is forbidden for immutable evidence"
            )


def validate_rust_target_binding(
    root: Path,
    debt_id: str,
    cargo: str,
    rustc: str,
    lake: str,
    label: str,
) -> None:
    _reject_repository_cargo_config(root, label)
    stem = debt_id.replace("-", "_").lower()
    target_name = f"debt_{stem}"
    relative = f"rust/tests/{target_name}.rs"
    expected_source = (root / relative).resolve(strict=True)
    cargo_toml = ensure_tracked_regular(root, "rust/Cargo.toml", label + ".cargo-toml")
    try:
        cargo_data = tomllib.loads(cargo_toml.read_text(encoding="utf-8"))
    except (OSError, UnicodeError, tomllib.TOMLDecodeError) as exc:
        raise DebtError(f"{label}: rust/Cargo.toml is not valid UTF-8 TOML: {exc}") from None
    explicit = [
        item
        for item in cargo_data.get("test", [])
        if isinstance(item, dict) and item.get("name") == target_name
    ]
    if len(explicit) > 1:
        raise DebtError(f"{label}: Cargo declares the exact debt test target more than once")
    if explicit:
        item = explicit[0]
        if item.get("harness", True) is not True:
            raise DebtError(f"{label}: Rust debt test target must use the standard harness")
        if item.get("path", f"tests/{target_name}.rs") != f"tests/{target_name}.rs":
            raise DebtError(f"{label}: Cargo redirects the exact debt test target path")
    metadata_output = _execute_evidence_command(
        root,
        [
            "cargo",
            "metadata",
            "--quiet",
            "--manifest-path",
            "rust/Cargo.toml",
            "--frozen",
            "--no-deps",
            "--format-version",
            "1",
        ],
        cargo,
        label + ".metadata",
        [rustc, lake],
    )
    metadata = parse_json(metadata_output.strip(), label + ".metadata")
    if not isinstance(metadata, dict) or not isinstance(metadata.get("packages"), list):
        raise DebtError(f"{label}: Cargo metadata has an unexpected shape")
    targets: List[Mapping[str, Any]] = []
    for package in metadata["packages"]:
        if not isinstance(package, dict):
            continue
        manifest_path = package.get("manifest_path")
        if not isinstance(manifest_path, str):
            continue
        try:
            manifest = Path(manifest_path).resolve(strict=True)
        except (OSError, RuntimeError):
            continue
        if manifest != cargo_toml.resolve(strict=True):
            continue
        for target in package.get("targets", []):
            if isinstance(target, dict) and target.get("name") == target_name:
                targets.append(target)
    if len(targets) != 1:
        raise DebtError(f"{label}: Cargo metadata must expose one exact debt test target")
    target = targets[0]
    try:
        source = Path(target["src_path"]).resolve(strict=True)
    except (KeyError, OSError, RuntimeError, TypeError):
        raise DebtError(f"{label}: Cargo metadata returned an invalid debt target path") from None
    if source != expected_source or target.get("kind") != ["test"] or target.get("test") is not True:
        raise DebtError(f"{label}: Cargo metadata did not bind the exact standard test source")


def validate_rust_unit_target_binding(
    root: Path,
    debt_id: str,
    cargo: str,
    rustc: str,
    lake: str,
    label: str,
) -> None:
    _reject_repository_cargo_config(root, label)
    cargo_toml = ensure_tracked_regular(root, "rust/Cargo.toml", label + ".cargo-toml")
    lib_source = ensure_tracked_regular(root, "rust/src/lib.rs", label + ".lib-source")
    persistence_source = ensure_tracked_regular(
        root, "rust/src/persistence/mod.rs", label + ".persistence-source"
    )
    record_source = ensure_tracked_regular(
        root, "rust/src/persistence/record.rs", label + ".record-source"
    )
    package_name, library_name = _validate_rust_unit_chain_bytes(
        debt_id,
        cargo_toml.read_bytes(),
        lib_source.read_bytes(),
        persistence_source.read_bytes(),
        record_source.read_bytes(),
        label,
    )
    expected_source = lib_source.resolve(strict=True)
    metadata_output = _execute_evidence_command(
        root,
        [
            "cargo",
            "metadata",
            "--quiet",
            "--manifest-path",
            "rust/Cargo.toml",
            "--frozen",
            "--no-deps",
            "--format-version",
            "1",
        ],
        cargo,
        label + ".metadata",
        [rustc, lake],
    )
    metadata = parse_json(metadata_output.strip(), label + ".metadata")
    if not isinstance(metadata, dict) or not isinstance(metadata.get("packages"), list):
        raise DebtError(f"{label}: Cargo metadata has an unexpected shape")
    targets: List[Mapping[str, Any]] = []
    for package in metadata["packages"]:
        if not isinstance(package, dict) or package.get("name") != package_name:
            continue
        manifest_path = package.get("manifest_path")
        if not isinstance(manifest_path, str):
            continue
        try:
            manifest = Path(manifest_path).resolve(strict=True)
        except (OSError, RuntimeError):
            continue
        if manifest != cargo_toml.resolve(strict=True):
            continue
        for target in package.get("targets", []):
            if isinstance(target, dict) and target.get("name") == library_name:
                targets.append(target)
    if len(targets) != 1:
        raise DebtError(f"{label}: Cargo metadata must expose one exact library test target")
    target = targets[0]
    try:
        source = Path(target["src_path"]).resolve(strict=True)
    except (KeyError, OSError, RuntimeError, TypeError):
        raise DebtError(f"{label}: Cargo metadata returned an invalid library path") from None
    if (
        source != expected_source
        or target.get("kind") != ["lib"]
        or target.get("crate_types") != ["lib"]
        or target.get("test") is not True
    ):
        raise DebtError(f"{label}: Cargo metadata did not bind the exact standard library harness")


def validate_rust_case(root: Path, debt_id: str, label: str) -> None:
    stem = debt_id.replace("-", "_").lower()
    target = f"debt_{stem}"
    test_name = f"debt_closure_{stem}"
    cargo = _resolved_executable("cargo", label)
    rustc = _resolved_executable("rustc", label)
    lake = _resolved_executable("lake", label)
    validate_rust_toolchain(root, cargo, rustc, lake, label)
    validate_rust_target_binding(root, debt_id, cargo, rustc, lake, label)
    shared = [
        "cargo",
        "test",
        "--manifest-path",
        "rust/Cargo.toml",
        "--frozen",
        "--color",
        "never",
        "--test",
        target,
    ]
    path_executables = [rustc, lake]
    listing = _execute_evidence_command(
        root,
        [*shared, "--", "--list", "--format", "terse"],
        cargo,
        label + ".list",
        path_executables,
    )
    listed = [
        line.strip()
        for line in listing.splitlines()
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_:]*: (?:test|benchmark)", line.strip())
    ]
    expected_listing = f"{test_name}: test"
    if listed != [expected_listing]:
        raise DebtError(
            f"{label}: Rust case must list exactly one owned test {expected_listing}"
        )
    output = _execute_evidence_command(
        root,
        [
            *shared,
            test_name,
            "--",
            "--exact",
            "--include-ignored",
            "--test-threads",
            "1",
        ],
        cargo,
        label + ".run",
        path_executables,
    )
    ok_line = f"test {test_name} ... ok"
    ok_count = sum(line.strip() == ok_line for line in output.splitlines())
    summary_re = re.compile(
        r"test result: ok\. 1 passed; 0 failed; 0 ignored; 0 measured; "
        r"0 filtered out; finished in .+"
    )
    summary_count = sum(
        summary_re.fullmatch(line.strip()) is not None for line in output.splitlines()
    )
    if ok_count != 1 or summary_count != 1:
        raise DebtError(
            f"{label}: Rust harness did not report one exact completed passing test"
        )


def validate_rust_unit_case(root: Path, debt_id: str, label: str) -> None:
    _, module_prefix, test_name, _ = rust_unit_case_binding(debt_id)
    cargo = _resolved_executable("cargo", label)
    rustc = _resolved_executable("rustc", label)
    lake = _resolved_executable("lake", label)
    validate_rust_toolchain(root, cargo, rustc, lake, label)
    validate_rust_unit_target_binding(root, debt_id, cargo, rustc, lake, label)
    shared = [
        "cargo",
        "test",
        "--manifest-path",
        "rust/Cargo.toml",
        "--frozen",
        "--color",
        "never",
        "--lib",
    ]
    path_executables = [rustc, lake]
    listing = _execute_evidence_command(
        root,
        [*shared, module_prefix, "--", "--list", "--format", "terse"],
        cargo,
        label + ".list",
        path_executables,
    )
    listed = [
        line.strip()
        for line in listing.splitlines()
        if re.fullmatch(r"[A-Za-z_][A-Za-z0-9_:]*: (?:test|benchmark)", line.strip())
    ]
    expected_listing = f"{test_name}: test"
    if listed != [expected_listing]:
        raise DebtError(
            f"{label}: Rust unit must list exactly one owned test {expected_listing}"
        )
    output = _execute_evidence_command(
        root,
        [
            *shared,
            test_name,
            "--",
            "--exact",
            "--include-ignored",
            "--test-threads",
            "1",
        ],
        cargo,
        label + ".run",
        path_executables,
    )
    ok_line = f"test {test_name} ... ok"
    ok_count = sum(line.strip() == ok_line for line in output.splitlines())
    # A private unit runs inside the crate's standard library harness. The
    # exact selector must therefore filter every unrelated library test; only
    # the owned listing and the one completed passing test are invariant.
    summary_re = re.compile(
        r"test result: ok\. 1 passed; 0 failed; 0 ignored; 0 measured; "
        r"[0-9]+ filtered out; finished in .+"
    )
    summary_count = sum(
        summary_re.fullmatch(line.strip()) is not None for line in output.splitlines()
    )
    if ok_count != 1 or summary_count != 1:
        raise DebtError(
            f"{label}: Rust unit harness did not report one exact completed passing test"
        )


def validate_case_manifest(
    root: Path, debt_id: str, content: bytes, label: str
) -> None:
    manifest = parse_case_manifest_bytes(content, label, debt_id)
    for index, check in enumerate(manifest["checks"]):
        check_label = f"{label}.checks[{index}]"
        kind = check["kind"]
        relative = case_artifact_relative(debt_id, kind)
        path = ensure_tracked_regular(root, relative, check_label)
        artifact = path.read_bytes()
        if not artifact:
            raise DebtError(f"{check_label}: case artifact must be nonempty")
        if sha256_bytes(artifact) != check["sha256"]:
            raise DebtError(f"{check_label}: case artifact SHA-256 does not match exact bytes")
        if kind == "rust_test":
            validate_rust_case(root, debt_id, check_label)
        elif kind == "rust_unit":
            validate_rust_unit_case(root, debt_id, check_label)
        else:  # Manifest shape validation makes this unreachable.
            raise DebtError(f"{check_label}.kind: unsupported case check kind")


def validate_receipt_evidence(root: Path, receipt: Mapping[str, Any]) -> None:
    debt_id = receipt["id"]
    receipt_label = f"docs/debt/closed/{debt_id}.json"
    for index, item in enumerate(receipt["evidence"]):
        label = f"{receipt_label}.evidence[{index}]"
        path = ensure_tracked_regular(root, item["path"], label)
        content = path.read_bytes()
        if not content:
            raise DebtError(f"{label}: evidence file must be nonempty")
        if sha256_bytes(content) != item["sha256"]:
            raise DebtError(f"{label}: evidence SHA-256 does not match exact file bytes")
        kind = item["kind"]
        if kind == "lean_decl":
            executable = _resolved_executable("lake", label)
            declaration = "debtClosure_" + debt_id.replace("-", "_")
            validate_lean_declaration(
                root, debt_id, content, declaration, executable, label
            )
        else:
            validate_case_manifest(root, debt_id, content, label)


def validate_supersession_chains(
    active_ids: Iterable[str],
    receipts: Mapping[str, Mapping[str, Any]],
    label: str = "",
) -> None:
    """Require every immutable supersession edge to reach live or paid debt.

    Direct class/severity compatibility is checked when an edge is introduced;
    this graph check deliberately permits that once-active replacement to close
    later without rewriting the older receipt.
    """
    active = set(active_ids)
    prefix = f"{label}: " if label else ""
    for origin in sorted(receipts):
        receipt = receipts[origin]
        if receipt["disposition"] != "superseded":
            continue
        seen = {origin}
        target = receipt["replacement_id"]
        while True:
            if target in active:
                break
            replacement = receipts.get(target)
            if replacement is None:
                raise DebtError(
                    f"{prefix}supersession chain from {origin} names unknown target {target}"
                )
            if target in seen:
                raise DebtError(
                    f"{prefix}supersession cycle from {origin} reaches {target}"
                )
            seen.add(target)
            disposition = replacement["disposition"]
            if disposition in TERMINAL_SUPERSESSION_DISPOSITIONS:
                break
            if disposition != "superseded":  # Shape validation makes this unreachable.
                raise DebtError(
                    f"{prefix}supersession chain from {origin} ends in invalid disposition"
                )
            target = replacement["replacement_id"]


def validate_head(
    root: Path,
    active: Sequence[Mapping[str, Any]],
    receipts: Mapping[str, Mapping[str, Any]],
    scan: SourceScan,
    policy_profile: Optional[str],
) -> None:
    active_by_id = {entry["id"]: entry for entry in active}
    active_ids = set(active_by_id)
    receipt_ids = set(receipts)
    overlap = sorted(active_ids & receipt_ids)
    if overlap:
        raise DebtError("ids cannot be both active and closed: " + ",".join(overlap))
    marker_ids = set(scan.markers)
    missing_rows = sorted(marker_ids - active_ids)
    missing_markers = sorted(active_ids - marker_ids)
    if missing_rows:
        raise DebtError("canonical markers without active rows: " + ",".join(missing_rows))
    if missing_markers:
        raise DebtError("active rows without canonical markers: " + ",".join(missing_markers))
    for debt_id in sorted(active_ids):
        entry = active_by_id[debt_id]
        marker = scan.markers[debt_id]
        if entry["class"] not in MARKER_CLASS[marker.label]:
            raise DebtError(
                f"{debt_id}: marker {marker.label} is incompatible with class {entry['class']}"
            )
        if entry["source"] != marker.source:
            raise DebtError(f"{debt_id}: active source does not match canonical marker path")
        if entry["marker_sha256"] != marker.marker_sha256:
            raise DebtError(f"{debt_id}: marker_sha256 does not match exact source block")
    known_ids = active_ids | receipt_ids
    for debt_id, source, line in scan.refs:
        if debt_id not in known_ids:
            raise DebtError(f"{source}:{line}: DEBT-REF names unknown id {debt_id}")
    validate_supersession_chains(active_ids, receipts)
    if policy_profile is not None:
        policy = POLICY_PROFILES.get(policy_profile)
        if policy is None:
            raise DebtError(f"unknown debt policy profile: {policy_profile}")
        unclassified = sorted(
            entry["id"] for entry in active if entry["class"] == "unclassified"
        )
        if policy["forbid_unclassified"] and unclassified:
            raise DebtError(
                f"policy {policy_profile} forbids unclassified debt: "
                + ",".join(unclassified)
            )
        forbidden_severities = sorted(
            entry["id"]
            for entry in active
            if entry["severity"] in policy["forbidden_severities"]
        )
        if forbidden_severities:
            labels = ",".join(sorted(policy["forbidden_severities"]))
            raise DebtError(
                f"policy {policy_profile} forbids active severity {labels}: "
                + ",".join(forbidden_severities)
            )
        forbidden_classes = sorted(
            entry["id"]
            for entry in active
            if entry["class"] in policy["forbidden_classes"]
        )
        if forbidden_classes:
            labels = ",".join(sorted(policy["forbidden_classes"]))
            raise DebtError(
                f"policy {policy_profile} forbids active class {labels}: "
                + ",".join(forbidden_classes)
            )


def validate_against_base(
    current_active: Sequence[Mapping[str, Any]],
    current_receipt_raw: Mapping[str, bytes],
    current_receipts: Mapping[str, Mapping[str, Any]],
    base_active: Sequence[Mapping[str, Any]],
    base_receipt_raw: Mapping[str, bytes],
    base_receipts: Mapping[str, Mapping[str, Any]],
) -> None:
    current_by_id = {entry["id"]: entry for entry in current_active}
    base_by_id = {entry["id"]: entry for entry in base_active}
    for debt_id in sorted(base_receipt_raw):
        if debt_id not in current_receipt_raw:
            raise DebtError(f"immutable receipt deleted: {debt_id}")
        if current_receipt_raw[debt_id] != base_receipt_raw[debt_id]:
            raise DebtError(f"immutable receipt modified: {debt_id}")
    for debt_id in sorted(set(base_by_id) & set(current_by_id)):
        if canonical_json(base_by_id[debt_id]) != canonical_json(current_by_id[debt_id]):
            raise DebtError(
                f"active entry is immutable for {debt_id}; close it and allocate a new id"
            )
    for debt_id in sorted(set(base_by_id) - set(current_by_id)):
        receipt = current_receipts.get(debt_id)
        if receipt is None or debt_id in base_receipts:
            raise DebtError(f"base active item removed without a new closure receipt: {debt_id}")
        expected_entry_hash = entry_sha256(base_by_id[debt_id])
        if receipt["prior_entry_sha256"] != expected_entry_hash:
            raise DebtError(f"{debt_id}: receipt prior_entry_sha256 does not match base")
        if receipt["prior_marker_sha256"] != base_by_id[debt_id]["marker_sha256"]:
            raise DebtError(f"{debt_id}: receipt prior_marker_sha256 does not match base")
        if receipt["disposition"] == "superseded":
            replacement = current_by_id.get(receipt["replacement_id"])
            if replacement is None:
                raise DebtError(
                    f"{debt_id}: new superseding receipt replacement must be active "
                    "for class/severity validation"
                )
            prior = base_by_id[debt_id]
            if replacement["class"] != prior["class"]:
                raise DebtError(f"{debt_id}: superseding item must preserve debt class")
            if prior["class"] == "obligation":
                rank = {"P0": 0, "P1": 1, "P2": 2, "P3": 3}
                if rank[replacement["severity"]] > rank[prior["severity"]]:
                    raise DebtError(
                        f"{debt_id}: superseding obligation cannot weaken severity"
                    )
    for debt_id in sorted(set(current_receipts) - set(base_receipts)):
        if debt_id not in base_by_id or debt_id in current_by_id:
            raise DebtError(f"new receipt does not close one base-active item: {debt_id}")
    historical_ids = set(base_by_id) | set(base_receipts)
    max_ever = max((int(item[2:]) for item in historical_ids), default=0)
    new_ids = sorted(set(current_by_id) - set(base_by_id))
    for debt_id in new_ids:
        if debt_id in base_receipts:
            raise DebtError(f"closed debt id reused: {debt_id}")
        if int(debt_id[2:]) <= max_ever:
            raise DebtError(
                f"new id {debt_id} is not above historical maximum U-{max_ever:04d}"
            )


def validate_committed_evidence_blobs(
    root: Path,
    commit: str,
    receipts: Mapping[str, Mapping[str, Any]],
    versions: Dict[Tuple[str, str], Tuple[str, bytes]],
) -> None:
    for debt_id in sorted(receipts):
        receipt = receipts[debt_id]
        for index, item in enumerate(receipt["evidence"]):
            label = f"{commit}:docs/debt/closed/{debt_id}.json.evidence[{index}]"
            blob = git_regular_blob(root, commit, item["path"])
            if blob is None:
                raise DebtError(f"{label}: committed evidence blob is missing")
            mode, data = blob
            if not data:
                raise DebtError(f"{label}: committed evidence blob is empty")
            if sha256_bytes(data) != item["sha256"]:
                raise DebtError(f"{label}: committed evidence SHA-256 does not match")
            version_key = (debt_id, item["path"])
            prior = versions.get(version_key)
            if prior is not None and prior != (mode, data):
                raise DebtError(f"{label}: committed evidence mode or bytes changed")
            versions[version_key] = (mode, data)
            if item["kind"] != "case_manifest":
                continue
            manifest = parse_case_manifest_bytes(data, label, debt_id)
            for check_index, check in enumerate(manifest["checks"]):
                check_label = f"{label}.checks[{check_index}]"
                kind = check["kind"]
                relative = case_artifact_relative(debt_id, kind)
                artifact_blob = git_regular_blob(root, commit, relative)
                if artifact_blob is None:
                    raise DebtError(f"{check_label}: committed case artifact is missing")
                artifact_mode, artifact = artifact_blob
                if not artifact:
                    raise DebtError(f"{check_label}: committed case artifact is empty")
                if sha256_bytes(artifact) != check["sha256"]:
                    raise DebtError(
                        f"{check_label}: committed case artifact SHA-256 does not match"
                    )
                artifact_key = (debt_id, relative)
                prior_artifact = versions.get(artifact_key)
                if prior_artifact is not None and prior_artifact != (
                    artifact_mode,
                    artifact,
                ):
                    raise DebtError(
                        f"{check_label}: committed case artifact mode or bytes changed"
                    )
                versions[artifact_key] = (artifact_mode, artifact)
                if kind != "rust_unit":
                    continue
                _reject_committed_cargo_config(root, commit, check_label)
                chain_paths = (
                    "rust/Cargo.toml",
                    "rust/src/lib.rs",
                    "rust/src/persistence/mod.rs",
                    "rust/src/persistence/record.rs",
                )
                chain_blobs: List[bytes] = []
                for chain_path in chain_paths:
                    chain_blob = git_regular_blob(root, commit, chain_path)
                    if chain_blob is None:
                        raise DebtError(
                            f"{check_label}: committed Rust unit module chain is missing {chain_path}"
                        )
                    chain_blobs.append(chain_blob[1])
                _validate_rust_unit_chain_bytes(
                    debt_id,
                    chain_blobs[0],
                    chain_blobs[1],
                    chain_blobs[2],
                    chain_blobs[3],
                    check_label,
                )


def validate_committed_history(root: Path, base: str) -> None:
    listing = _run_git(
        root,
        ["rev-list", "--reverse", "--topo-order", "--ancestry-path", f"{base}..HEAD"],
    )
    commits = [base]
    commits.extend(line for line in listing.decode("ascii").splitlines() if line)
    states: Dict[
        str,
        Tuple[
            Dict[str, Mapping[str, Any]],
            Dict[str, bytes],
            Dict[str, Mapping[str, Any]],
        ],
    ] = {}
    max_through: Dict[str, int] = {}
    active_versions: Dict[str, str] = {}
    receipt_versions: Dict[str, bytes] = {}
    evidence_versions: Dict[Tuple[str, str], Tuple[str, bytes]] = {}
    for commit in commits:
        active, receipt_raw, receipts = read_base_state(root, commit)
        validate_committed_evidence_blobs(root, commit, receipts, evidence_versions)
        active_by_id = {entry["id"]: entry for entry in active}
        overlap = sorted(set(active_by_id) & set(receipts))
        if overlap:
            raise DebtError(
                f"{commit}: ids cannot be both active and closed: {','.join(overlap)}"
            )
        validate_supersession_chains(active_by_id, receipts, commit)
        for debt_id, entry in active_by_id.items():
            encoded = canonical_json(entry)
            prior = active_versions.get(debt_id)
            if prior is not None and prior != encoded:
                raise DebtError(f"{commit}: committed active id was repurposed: {debt_id}")
            if debt_id in receipt_versions:
                raise DebtError(f"{commit}: committed closed id was reused: {debt_id}")
            active_versions[debt_id] = encoded
        for debt_id, raw in receipt_raw.items():
            prior = receipt_versions.get(debt_id)
            if prior is not None and prior != raw:
                raise DebtError(f"{commit}: committed receipt was modified: {debt_id}")
            receipt_versions[debt_id] = raw

        parents_line = _run_git(root, ["rev-list", "--parents", "-n", "1", commit])
        parent_ids = parents_line.decode("ascii").strip().split()[1:]
        parents = [states[parent] for parent in parent_ids if parent in states]
        parent_commits = [parent for parent in parent_ids if parent in states]
        prior_max = max((max_through[parent] for parent in parent_commits), default=0)
        if commit != base:
            for parent_active, parent_raw, _parent_receipts in parents:
                for debt_id, entry in parent_active.items():
                    if debt_id in active_by_id:
                        if canonical_json(entry) != canonical_json(active_by_id[debt_id]):
                            raise DebtError(
                                f"{commit}: committed active entry changed: {debt_id}"
                            )
                    elif debt_id in receipts:
                        receipt = receipts[debt_id]
                        if receipt["prior_entry_sha256"] != entry_sha256(entry):
                            raise DebtError(
                                f"{commit}: committed receipt has wrong prior entry: {debt_id}"
                            )
                        if receipt["prior_marker_sha256"] != entry["marker_sha256"]:
                            raise DebtError(
                                f"{commit}: committed receipt has wrong prior marker: {debt_id}"
                            )
                        if receipt["disposition"] == "superseded":
                            replacement = active_by_id.get(receipt["replacement_id"])
                            if replacement is None:
                                raise DebtError(
                                    f"{commit}: superseding receipt replacement is not active"
                                )
                            if replacement["class"] != entry["class"]:
                                raise DebtError(
                                    f"{commit}: superseding item changed debt class: {debt_id}"
                                )
                            if entry["class"] == "obligation":
                                rank = {"P0": 0, "P1": 1, "P2": 2, "P3": 3}
                                if rank[replacement["severity"]] > rank[entry["severity"]]:
                                    raise DebtError(
                                        f"{commit}: superseding obligation weakened severity"
                                    )
                    else:
                        raise DebtError(f"{commit}: committed debt id disappeared: {debt_id}")
                for debt_id, raw in parent_raw.items():
                    if receipt_raw.get(debt_id) != raw:
                        raise DebtError(
                            f"{commit}: committed immutable receipt disappeared or changed: {debt_id}"
                        )
            parent_known = set().union(
                *(set(active) | set(raw) for active, raw, _ in parents)
            ) if parents else set()
            parent_receipts = set().union(
                *(set(raw) for _active, raw, _ in parents)
            ) if parents else set()
            for debt_id in set(receipt_raw) - parent_receipts:
                closing = [parent_active[debt_id] for parent_active, _, _ in parents
                           if debt_id in parent_active]
                if not closing:
                    raise DebtError(
                        f"{commit}: committed receipt closes no parent-active id: {debt_id}"
                    )
            for debt_id in set(active_by_id) - parent_known:
                if int(debt_id[2:]) <= prior_max:
                    raise DebtError(
                        f"{commit}: committed id {debt_id} reused historical sequence"
                    )
        own_max = max(
            (int(item[2:]) for item in set(active_by_id) | set(receipt_raw)),
            default=0,
        )
        max_through[commit] = max(prior_max, own_max)
        states[commit] = (active_by_id, receipt_raw, receipts)


def resolve_policy(
    policy_profile: Optional[str], release_tag: Optional[str]
) -> Tuple[Optional[str], Optional[str]]:
    if policy_profile is not None and release_tag is not None:
        raise DebtError("--profile and --release-tag are mutually exclusive")
    if release_tag is not None:
        resolved = RELEASE_TAG_PROFILES.get(release_tag)
        if resolved is None:
            raise DebtError(f"unsupported release tag: {release_tag}")
        return resolved, release_tag
    if policy_profile in DEPRECATED_MILESTONE_PROFILES:
        policy_profile = DEPRECATED_MILESTONE_PROFILES[policy_profile]
    if policy_profile is not None and policy_profile not in POLICY_PROFILES:
        raise DebtError(f"unknown debt policy profile: {policy_profile}")
    return policy_profile, None


def check(
    root: Path,
    base_name: str,
    policy_profile: Optional[str] = None,
    release_tag: Optional[str] = None,
) -> Dict[str, Any]:
    policy_profile, release_tag = resolve_policy(policy_profile, release_tag)
    base = resolve_base(root, base_name)
    ensure_base_ancestor(root, base)
    _, active = read_active(root)
    receipt_raw, receipts = read_receipts(root)
    scan = scan_sources(root)
    validate_head(root, active, receipts, scan, policy_profile)
    validate_committed_history(root, base)
    head = _run_git(root, ["rev-parse", "--verify", "HEAD^{commit}"]).decode("ascii").strip()
    head_active, head_receipt_raw, head_receipts = read_base_state(root, head)
    validate_against_base(
        active, receipt_raw, receipts, head_active, head_receipt_raw, head_receipts
    )
    for debt_id in sorted(receipts):
        validate_receipt_evidence(root, receipts[debt_id])
    return {
        "active": len(active),
        "base": base,
        "closed": len(receipts),
        "policy_profile": policy_profile,
        "release_tag": release_tag,
        "refs": len(scan.refs),
        "schema": SCHEMA,
        "status": "ok",
        "unclassified": sum(entry["class"] == "unclassified" for entry in active),
    }


def _atomic_write(path: Path, data: bytes) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    descriptor, temporary = tempfile.mkstemp(prefix=path.name + ".", dir=path.parent)
    try:
        with os.fdopen(descriptor, "wb") as handle:
            handle.write(data)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary, path)
    except Exception:
        try:
            os.unlink(temporary)
        except FileNotFoundError:
            pass
        raise


def bootstrap(
    root: Path,
    base_name: str,
    target: str,
    allowed: bool,
) -> Dict[str, Any]:
    if not allowed:
        raise DebtError("bootstrap requires --allow-bootstrap")
    if target != "docs/debt/active.jsonl":
        raise DebtError("bootstrap --write target must be docs/debt/active.jsonl")
    base = resolve_base(root, base_name)
    ensure_base_ancestor(root, base)
    head = _run_git(root, ["rev-parse", "--verify", "HEAD^{commit}"]).decode("ascii").strip()
    if base != head:
        raise DebtError("bootstrap base must be the checked-out HEAD commit")
    shallow = _run_git(root, ["rev-parse", "--is-shallow-repository"]).decode("ascii").strip()
    if shallow != "false":
        raise DebtError("bootstrap refuses a shallow repository")
    if git_file(root, base, "docs/debt/active.jsonl") is not None:
        raise DebtError("bootstrap base already contains an active registry")
    base_receipt_raw, _ = read_base_receipts(root, base)
    if base_receipt_raw:
        raise DebtError("bootstrap base contains closure receipts")
    history = _run_git(
        root,
        [
            "log",
            "--format=%H",
            base,
            "--",
            "docs/debt/active.jsonl",
            "docs/debt/closed",
        ],
    )
    if history.strip():
        raise DebtError("bootstrap requires no registry or receipt history")
    active_path = root / target
    if active_path.is_symlink():
        raise DebtError("bootstrap refuses a symlinked active registry target")
    if active_path.exists():
        raise DebtError("bootstrap refuses to overwrite docs/debt/active.jsonl")
    safe_directory(root, active_path.parent, "docs/debt/")
    _, receipts = read_receipts(root)
    if receipts:
        raise DebtError("bootstrap requires an empty closure-receipt history")
    scan = scan_sources(root)
    if not scan.markers:
        raise DebtError("bootstrap refuses a zero-marker migration")
    base_scan = scan_base_sources(root, base)
    head_set = {
        (marker.debt_id, marker.label, marker.source, marker.marker_sha256)
        for marker in scan.markers.values()
    }
    base_set = {
        (marker.debt_id, marker.label, marker.source, marker.marker_sha256)
        for marker in base_scan.markers.values()
    }
    if head_set != base_set:
        raise DebtError(
            "bootstrap marker set differs from base; review marker migration separately"
        )
    if worktree_lean_snapshot(root) != base_lean_snapshot(root, base):
        raise DebtError("bootstrap Lean source tree differs from checked-out base")
    expected_ids = sorted(scan.markers)
    entries: List[Dict[str, Any]] = []
    for debt_id in expected_ids:
        marker = scan.markers[debt_id]
        debt_class = {
            "UNDONE": "unclassified",
            "PREMISE": "premise",
            "SCOPE": "scope",
        }[marker.label]
        entries.append(
            {
                "acceptance": "",
                "class": debt_class,
                "id": debt_id,
                "marker_sha256": marker.marker_sha256,
                "schema": SCHEMA,
                "severity": None,
                "source": marker.source,
                "summary": f"Bootstrap classification pending for {debt_id}",
            }
        )
    data = ("".join(canonical_json(entry) + "\n" for entry in entries)).encode("utf-8")
    _atomic_write(active_path, data)
    return {
        "base": base,
        "canonical_primary": len(entries),
        "output": target,
        "schema": SCHEMA,
        "sha256": sha256_bytes(data),
        "status": "bootstrapped",
    }


def repository_root(argument: Optional[str]) -> Path:
    if argument is None:
        return Path(__file__).resolve().parent.parent
    return Path(argument).resolve()


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", help="repository root (test-only override)")
    subparsers = parser.add_subparsers(dest="command", required=True)

    subparsers.add_parser("audit", help="report lexical registry state without gating")

    check_parser = subparsers.add_parser("check", help="run the post-migration gate")
    check_parser.add_argument("--base", required=True, help="trusted comparison commit")
    policy_group = check_parser.add_mutually_exclusive_group()
    policy_group.add_argument(
        "--profile",
        choices=sorted(POLICY_PROFILES),
        help="explicit development or release debt policy",
    )
    policy_group.add_argument(
        "--release-tag",
        help="exact registered release tag; unknown tags fail closed",
    )
    policy_group.add_argument(
        "--milestone",
        choices=sorted(DEPRECATED_MILESTONE_PROFILES),
        help=argparse.SUPPRESS,
    )

    bootstrap_parser = subparsers.add_parser(
        "bootstrap", help="guarded initial-registry construction after marker migration"
    )
    bootstrap_parser.add_argument("--base", required=True, help="pre-registry base commit")
    bootstrap_parser.add_argument("--write", required=True, metavar="PATH")
    bootstrap_parser.add_argument("--allow-bootstrap", action="store_true")
    return parser


def main(argv: Optional[Sequence[str]] = None) -> int:
    parser = build_parser()
    arguments = parser.parse_args(argv)
    root = repository_root(arguments.root)
    try:
        if arguments.command == "audit":
            result = audit_sources(root)
        elif arguments.command == "check":
            selected_profile = arguments.profile or arguments.milestone
            result = check(root, arguments.base, selected_profile, arguments.release_tag)
        else:
            result = bootstrap(
                root,
                arguments.base,
                arguments.write,
                arguments.allow_bootstrap,
            )
    except (DebtError, OSError) as exc:
        print(f"debt-gate: error: {exc}", file=sys.stderr)
        return 1
    print(canonical_json(result))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
