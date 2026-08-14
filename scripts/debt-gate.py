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
import subprocess
import sys
import tempfile
import time
from dataclasses import dataclass
from typing import Any, Dict, Iterable, List, Mapping, Optional, Sequence, Tuple


SCHEMA = 1
ID_RE = re.compile(r"U-[0-9]{4}\Z")
HEX_RE = re.compile(r"[0-9a-f]{64}\Z")
MILESTONE_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9._-]*\Z")
BASE_RE = re.compile(r"[A-Za-z0-9][A-Za-z0-9._/@{}^~+\-]*\Z")

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
EVIDENCE_KINDS = {"lean_decl", "aggregate_case"}
EVIDENCE_TIMEOUT_SECONDS = 300
EVIDENCE_OUTPUT_LIMIT = 1024 * 1024
AGGREGATE_EVIDENCE_RUNNER = "scripts/debt-closures.sh"
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
    if not isinstance(value, str) or not value or "\\" in value:
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
        kind = validate_evidence_command_shape(debt_id, item, item_label)
        kinds.append(kind)
    if disposition == "proved":
        if kinds != ["lean_decl"]:
            raise DebtError(f"{label}: proved closure requires exactly one Lean declaration")
    elif disposition == "implemented":
        if kinds != ["aggregate_case"]:
            raise DebtError(f"{label}: implemented closure requires one aggregate case")
    elif disposition == "obsolete":
        if not evidence:
            raise DebtError(f"{label}: obsolete closure still requires executable evidence")
    elif disposition == "superseded":
        replacement = _require_id(value["replacement_id"], label + ".replacement_id")
        if replacement == debt_id:
            raise DebtError(f"{label}: an item cannot supersede itself")
        if evidence:
            raise DebtError(f"{label}: superseded closure uses replacement_id, not evidence")


def _require_command(value: Any, label: str) -> List[str]:
    if not isinstance(value, list) or not value:
        raise DebtError(f"{label}: command must be a nonempty argv list")
    if any(not isinstance(arg, str) or not arg or "\0" in arg for arg in value):
        raise DebtError(f"{label}: command arguments must be nonempty strings")
    return value


def validate_evidence_command_shape(
    debt_id: str, item: Mapping[str, Any], label: str
) -> str:
    kind = item.get("kind")
    if kind not in EVIDENCE_KINDS:
        raise DebtError(f"{label}.kind: unknown evidence kind")
    keys = {"command", "kind", "path", "sha256"}
    if kind == "lean_decl":
        keys.add("declaration")
    _require_exact_keys(item, keys, label)
    path = canonical_repo_path(item["path"], label + ".path", ("scripts/", "tests/"), "")
    digest = item["sha256"]
    if not isinstance(digest, str) or not HEX_RE.fullmatch(digest):
        raise DebtError(f"{label}.sha256: expected lowercase SHA-256 hex")
    command = _require_command(item["command"], label + ".command")
    if kind == "lean_decl":
        expected_path = f"tests/DebtClosures/{debt_id.replace('-', '_')}.lean"
        declaration = item["declaration"]
        expected_declaration = "debtClosure_" + debt_id.replace("-", "_")
        expected = ["lake", "env", "lean", expected_path]
        if (
            path != expected_path
            or declaration != expected_declaration
            or command != expected
        ):
            raise DebtError(f"{label}: Lean declaration command/path/name must be exact")
    else:
        expected = ["bash", AGGREGATE_EVIDENCE_RUNNER, "--debt-case", debt_id]
        if path != AGGREGATE_EVIDENCE_RUNNER or command != expected:
            raise DebtError(f"{label}: aggregate evidence must use the reviewed dispatcher")
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
    entry = git_path_entry(root, base, path)
    if entry is None:
        return None
    mode, kind, object_id = entry
    if kind != "blob" or mode not in {"100644", "100755"}:
        raise DebtError(f"{base}:{path}: expected a regular tracked blob, found {mode} {kind}")
    return _run_git(root, ["cat-file", "blob", object_id])


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
        mode, _object_id, stage = metadata.decode("ascii").split(" ")
        recorded_path = recorded.decode("utf-8")
    except (ValueError, UnicodeDecodeError):
        raise DebtError(f"{label}: malformed Git index entry") from None
    if mode not in {"100644", "100755"} or stage != "0" or recorded_path != relative:
        raise DebtError(f"{label}: evidence must be one tracked regular stage-0 file")
    return path


def _evidence_environment(executable: str, root: Path) -> Dict[str, str]:
    executable_dir = str(Path(executable).absolute().parent)
    path_parts = [executable_dir, "/usr/local/bin", "/usr/bin", "/bin"]
    return {
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


def _execute_evidence_command(
    root: Path, argv: Sequence[str], executable: str, label: str
) -> str:
    actual_argv = [executable, *argv[1:]]
    process = subprocess.Popen(
        actual_argv,
        cwd=root,
        env=_evidence_environment(executable, root),
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
    try:
        while selector.get_map():
            remaining = deadline - time.monotonic()
            if remaining <= 0:
                os.killpg(process.pid, signal.SIGKILL)
                process.wait()
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
                    os.killpg(process.pid, signal.SIGKILL)
                    selector.unregister(key.fileobj)
                    break
        if exceeded:
            process.wait()
            raise DebtError(f"{label}: evidence command exceeded output limit")
        returncode = process.wait(timeout=max(0.0, deadline - time.monotonic()))
    except subprocess.TimeoutExpired:
        os.killpg(process.pid, signal.SIGKILL)
        process.wait()
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


def _resolved_executable(kind: str, label: str) -> str:
    if kind == "aggregate_case":
        candidate = "/bin/bash"
    else:
        candidate = "lake"
    resolved = shutil.which(candidate)
    if resolved is None:
        raise DebtError(f"{label}: required evidence runner {candidate} is unavailable")
    # Preserve a multicall symlink's basename (for example cargo -> rustup).
    return str(Path(resolved).absolute())


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
        executable = _resolved_executable(kind, label)
        if kind == "lean_decl":
            validate_lean_declaration(
                root, debt_id, content, item["declaration"], executable, label
            )
        else:
            output = _execute_evidence_command(
                root, list(item["command"]), executable, label
            )
            expected = f"debt-evidence: {debt_id}: PASS"
            if output.strip() != expected:
                raise DebtError(f"{label}: aggregate dispatcher did not emit unique exact PASS")


def validate_head(
    root: Path,
    active: Sequence[Mapping[str, Any]],
    receipts: Mapping[str, Mapping[str, Any]],
    scan: SourceScan,
    milestone: Optional[str],
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
    for debt_id in sorted(receipt_ids):
        receipt = receipts[debt_id]
        if receipt["disposition"] == "superseded":
            replacement = receipt["replacement_id"]
            if replacement not in active_ids:
                raise DebtError(
                    f"docs/debt/closed/{debt_id}.json: replacement_id must name an active item"
                )
    if milestone is not None:
        if not MILESTONE_RE.fullmatch(milestone):
            raise DebtError("--milestone must be a simple stable label")
        unclassified = sorted(
            entry["id"] for entry in active if entry["class"] == "unclassified"
        )
        if unclassified:
            raise DebtError(
                f"milestone {milestone} forbids unclassified debt: " + ",".join(unclassified)
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
            replacement = current_by_id[receipt["replacement_id"]]
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
    for commit in commits:
        active, receipt_raw, receipts = read_base_state(root, commit)
        active_by_id = {entry["id"]: entry for entry in active}
        overlap = sorted(set(active_by_id) & set(receipts))
        if overlap:
            raise DebtError(
                f"{commit}: ids cannot be both active and closed: {','.join(overlap)}"
            )
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


def check(root: Path, base_name: str, milestone: Optional[str]) -> Dict[str, Any]:
    base = resolve_base(root, base_name)
    ensure_base_ancestor(root, base)
    _, active = read_active(root)
    receipt_raw, receipts = read_receipts(root)
    scan = scan_sources(root)
    validate_head(root, active, receipts, scan, milestone)
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
        "milestone": milestone,
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

    subparsers.add_parser("audit", help="report pre-migration marker state without gating")

    check_parser = subparsers.add_parser("check", help="run the post-migration gate")
    check_parser.add_argument("--base", required=True, help="trusted comparison commit")
    check_parser.add_argument(
        "--milestone", help="release milestone; forbids unclassified active debt"
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
            result = check(root, arguments.base, arguments.milestone)
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
