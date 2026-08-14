#!/usr/bin/env python3
"""Mechanically check the complete source-only Rust/C/Lean ABI contract.

The canonical descriptor is a declaration/layout contract. It does not claim
that Lean's lowering, a C compiler, a linker, or libleanshared is semantically
correct; those remain the separately named execution premises.
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
import tempfile
from typing import Any


DESCRIPTOR = Path("rust/abi/uwueave-abi-v1.json")
LEDGER = Path("docs/trust/ledger2-v1.json")
SHIM_SOURCE_SHA256 = "abca5c87380db429884f76fd7f5bec89b8da0e8238f0896b7eb3525682fbcd45"


class AbiError(Exception):
    pass


def canonical_json(value: Any) -> bytes:
    return (json.dumps(value, ensure_ascii=False, allow_nan=False,
                       sort_keys=True, separators=(",", ":")) + "\n").encode()


def _unique_object(pairs: list[tuple[str, Any]]) -> dict[str, Any]:
    result: dict[str, Any] = {}
    for key, value in pairs:
        if key in result:
            raise AbiError(f"duplicate JSON key {key!r}")
        result[key] = value
    return result


def _reject_constant(value: str) -> None:
    raise AbiError(f"non-finite JSON value {value!r}")


def stable_bytes(path: Path) -> bytes:
    flags = os.O_RDONLY | getattr(os, "O_CLOEXEC", 0) | getattr(os, "O_NOFOLLOW", 0)
    try:
        descriptor = os.open(path, flags)
    except OSError as exc:
        raise AbiError(f"cannot open {path}: {exc}") from None
    try:
        before = os.fstat(descriptor)
        if not stat.S_ISREG(before.st_mode):
            raise AbiError(f"expected regular file: {path}")
        chunks = []
        while True:
            block = os.read(descriptor, 1024 * 1024)
            if not block:
                break
            chunks.append(block)
        after = os.fstat(descriptor)
    except OSError as exc:
        raise AbiError(f"cannot read {path}: {exc}") from None
    finally:
        os.close(descriptor)
    identity = lambda item: (item.st_dev, item.st_ino, item.st_mode, item.st_size,
                             item.st_mtime_ns, item.st_ctime_ns)
    data = b"".join(chunks)
    if identity(before) != identity(after) or len(data) != after.st_size:
        raise AbiError(f"file changed while reading: {path}")
    return data


def load_json(path: Path, canonical: bool = False) -> Any:
    raw = stable_bytes(path)
    if raw.startswith(b"\xef\xbb\xbf") or b"\r" in raw or not raw.endswith(b"\n"):
        raise AbiError(f"{path}: expected UTF-8 with one LF and no BOM/CR")
    try:
        value = json.loads(raw.decode(), object_pairs_hook=_unique_object,
                           parse_constant=_reject_constant)
    except (UnicodeError, json.JSONDecodeError) as exc:
        raise AbiError(f"{path}: malformed JSON: {exc}") from None
    if canonical and raw != canonical_json(value):
        raise AbiError(f"{path}: JSON is not canonical")
    return value


def expect_keys(value: Any, keys: set[str], label: str) -> dict[str, Any]:
    if not isinstance(value, dict) or set(value) != keys:
        actual = sorted(value) if isinstance(value, dict) else type(value).__name__
        raise AbiError(f"{label}: expected keys {sorted(keys)}, got {actual}")
    return value


def load_descriptor(root: Path) -> dict[str, Any]:
    value = expect_keys(load_json(root / DESCRIPTOR, canonical=True),
                        {"lean_exports", "schema", "shim_functions", "structs"},
                        "descriptor")
    if type(value["schema"]) is not int or value["schema"] != 1:
        raise AbiError("descriptor: unsupported schema")
    structs = value["structs"]
    if not isinstance(structs, list) or not structs:
        raise AbiError("descriptor.structs must be nonempty")
    struct_names = []
    for index, item in enumerate(structs):
        item = expect_keys(item, {"align", "c_name", "fields", "rust_name", "size"},
                           f"descriptor.structs[{index}]")
        if not isinstance(item["c_name"], str) or not isinstance(item["rust_name"], str) \
                or type(item["size"]) is not int or type(item["align"]) is not int \
                or item["size"] <= 0 or item["align"] <= 0:
            raise AbiError("descriptor: malformed struct identity/layout")
        fields = item["fields"]
        if not isinstance(fields, list) or not fields:
            raise AbiError("descriptor: struct fields must be nonempty")
        names = []
        for field in fields:
            field = expect_keys(field, {"name", "offset", "type"}, "descriptor.field")
            if field["type"] not in {"i64", "u64"} or type(field["offset"]) is not int \
                    or field["offset"] < 0 or not isinstance(field["name"], str):
                raise AbiError("descriptor: malformed struct field")
            names.append(field["name"])
        if len(names) != len(set(names)):
            raise AbiError("descriptor: duplicate struct field")
        struct_names.append(item["c_name"])
    if struct_names != sorted(set(struct_names)):
        raise AbiError("descriptor: structs must be sorted and unique")

    lean_exports = value["lean_exports"]
    export_symbols = []
    for item in lean_exports:
        item = expect_keys(item, {"arity", "module", "symbol"}, "descriptor.lean_export")
        if type(item["arity"]) is not int or item["arity"] <= 0 \
                or not re.fullmatch(r"Uwueave(?:\.[A-Za-z0-9_]+)+", item["module"]) \
                or not re.fullmatch(r"uwueave_[a-z0-9_]+", item["symbol"]):
            raise AbiError("descriptor: malformed Lean export")
        export_symbols.append(item["symbol"])
    if [(item["module"], item["symbol"]) for item in lean_exports] != sorted(
            set((item["module"], item["symbol"]) for item in lean_exports)):
        raise AbiError("descriptor: Lean exports must be sorted and unique")

    allowed_types = {"const_i64_ptr", "const_replay_grant_ptr", "const_replay_op_ptr",
                     "const_u64_ptr", "const_u8_ptr", "mut_u8_ptr", "mut_usize_ptr",
                     "u8", "usize", "void"}
    functions = value["shim_functions"]
    symbols = []
    mapped_exports = []
    for item in functions:
        item = expect_keys(item, {"lean_export", "parameters", "return", "symbol"},
                           "descriptor.shim_function")
        if item["return"] not in allowed_types or not re.fullmatch(
                r"shim_uweave_[a-z0-9_]+", item["symbol"]):
            raise AbiError("descriptor: malformed shim function")
        if item["lean_export"] is not None:
            if item["lean_export"] not in export_symbols:
                raise AbiError("descriptor: shim maps an unknown Lean export")
            mapped_exports.append(item["lean_export"])
        parameters = item["parameters"]
        if not isinstance(parameters, list):
            raise AbiError("descriptor: parameters must be a list")
        names = []
        for parameter in parameters:
            parameter = expect_keys(parameter, {"name", "type"}, "descriptor.parameter")
            if not isinstance(parameter["name"], str) or parameter["type"] not in allowed_types \
                    or parameter["type"] == "void":
                raise AbiError("descriptor: malformed parameter")
            names.append(parameter["name"])
        if len(names) != len(set(names)):
            raise AbiError("descriptor: duplicate parameter name")
        symbols.append(item["symbol"])
    if symbols != sorted(set(symbols)):
        raise AbiError("descriptor: shim functions must be sorted and unique")
    if sorted(mapped_exports) != sorted(export_symbols):
        raise AbiError("descriptor: every Lean export must map to exactly one shim")
    return value


C_TYPES = {
    "const_i64_ptr": "const int64_t*",
    "const_replay_grant_ptr": "const shim_replay_grant*",
    "const_replay_op_ptr": "const shim_replay_op*",
    "const_u64_ptr": "const uint64_t*",
    "const_u8_ptr": "const uint8_t*",
    "mut_u8_ptr": "uint8_t*",
    "mut_usize_ptr": "size_t*",
    "u8": "uint8_t",
    "usize": "size_t",
    "void": "void",
}

RUST_TYPES = {
    "const_i64_ptr": "*consti64",
    "const_replay_grant_ptr": "*constReplayGrantInput",
    "const_replay_op_ptr": "*constReplayOpInput",
    "const_u64_ptr": "*constu64",
    "const_u8_ptr": "*constu8",
    "mut_u8_ptr": "*mutu8",
    "mut_usize_ptr": "*mutusize",
    "u8": "u8",
    "usize": "usize",
    "void": "()",
}


def strip_c(text: str) -> str:
    text = re.sub(r"/\*.*?\*/", " ", text, flags=re.S)
    text = re.sub(r"//[^\n]*", " ", text)
    return text


def compact_c(text: str) -> str:
    text = re.sub(r"\s+", " ", strip_c(text)).strip()
    text = re.sub(r"\s*\*\s*", "*", text)
    text = re.sub(r"\s*,\s*", ",", text)
    text = re.sub(r"\s*\(\s*", "(", text)
    text = re.sub(r"\s*\)\s*", ")", text)
    return text


def validate_c_surface(descriptor: dict[str, Any], text: str) -> None:
    compact = compact_c(text)
    for struct in descriptor["structs"]:
        fields = " ".join(
            f"{'uint64_t' if field['type'] == 'u64' else 'int64_t'} {field['name']};"
            for field in struct["fields"]
        )
        typedef = f"typedef struct {{ {fields} }} {struct['c_name']};"
        if compact.count(compact_c(typedef)) != 1:
            raise AbiError(f"C surface: exact typedef drift for {struct['c_name']}")
        required_assertions = [
            f"_Static_assert(sizeof({struct['c_name']}) == {struct['size']},",
            f"_Static_assert(_Alignof({struct['c_name']}) == {struct['align']},",
        ]
        required_assertions.extend(
            f"_Static_assert(offsetof({struct['c_name']},{field['name']}) == {field['offset']},"
            for field in struct["fields"]
        )
        for assertion in required_assertions:
            if compact_c(assertion) not in compact:
                raise AbiError(f"C surface: missing layout assertion {assertion}")

    for export in descriptor["lean_exports"]:
        pattern = re.compile(
            rf"extern lean_object\*{re.escape(export['symbol'])}\(([^)]*)\);"
        )
        matches = pattern.findall(compact)
        if len(matches) != 1:
            raise AbiError(f"C surface: Lean declaration drift for {export['symbol']}")
        parameters = [item for item in matches[0].split(",") if item]
        if len(parameters) != export["arity"] or any(
                re.fullmatch(r"lean_object\*(?:[A-Za-z_][A-Za-z0-9_]*)?", item) is None
                for item in parameters):
            raise AbiError(f"C surface: Lean declaration arity/type drift for {export['symbol']}")

    for function in descriptor["shim_functions"]:
        parameters = ",".join(
            f"{C_TYPES[item['type']]} {item['name']}" for item in function["parameters"]
        ) or "void"
        signature = compact_c(
            f"{C_TYPES[function['return']]} {function['symbol']}({parameters})"
        )
        if compact.count(signature) != 1 or signature + "{" not in compact.replace(" {", "{"):
            raise AbiError(f"C surface: shim definition drift for {function['symbol']}")


def compact_rust_type(text: str) -> str:
    return re.sub(r"\s+", "", text)


def validate_rust_surface(descriptor: dict[str, Any], text: str) -> None:
    for struct in descriptor["structs"]:
        pattern = re.compile(
            rf"#\[repr\(C\)\].*?struct\s+{re.escape(struct['rust_name'])}\s*\{{(?P<body>.*?)\}}",
            re.S,
        )
        match = pattern.search(text)
        if match is None:
            raise AbiError(f"Rust surface: repr(C) struct absent for {struct['rust_name']}")
        fields = re.findall(r"(?:pub\(crate\)\s+)?([A-Za-z_][A-Za-z0-9_]*)\s*:\s*([^,]+),",
                            match.group("body"))
        expected = [(field["name"], field["type"]) for field in struct["fields"]]
        actual = [(name, compact_rust_type(kind)) for name, kind in fields]
        if actual != expected:
            raise AbiError(f"Rust surface: field drift for {struct['rust_name']}: {actual}")
        assertions = [
            f"size_of::<{struct['rust_name']}>() == {struct['size']}",
            f"align_of::<{struct['rust_name']}>() == {struct['align']}",
        ]
        assertions.extend(
            f"offset_of!({struct['rust_name']}, {field['name']}) == {field['offset']}"
            for field in struct["fields"]
        )
        whitespace_free = re.sub(r"\s+", "", text)
        for assertion in assertions:
            if re.sub(r"\s+", "", assertion) not in whitespace_free:
                raise AbiError(f"Rust surface: missing layout assertion {assertion}")

    for function in descriptor["shim_functions"]:
        match = re.search(
            rf"\bfn\s+{re.escape(function['symbol'])}\s*\((?P<params>.*?)\)\s*"
            rf"(?:->\s*(?P<return>[^;]+))?;",
            text,
            flags=re.S,
        )
        if match is None:
            raise AbiError(f"Rust surface: binding absent for {function['symbol']}")
        params = []
        for parameter in re.split(r",", match.group("params")):
            if not parameter.strip():
                continue
            if ":" not in parameter:
                raise AbiError(f"Rust surface: malformed parameter for {function['symbol']}")
            params.append(compact_rust_type(parameter.split(":", 1)[1]))
        expected = [RUST_TYPES[item["type"]] for item in function["parameters"]]
        if params != expected:
            raise AbiError(f"Rust surface: signature drift for {function['symbol']}: {params}")
        actual_return = compact_rust_type(match.group("return") or "()")
        if actual_return != RUST_TYPES[function["return"]]:
            raise AbiError(f"Rust surface: return drift for {function['symbol']}")


def validate_ledger_mapping(descriptor: dict[str, Any], ledger: dict[str, Any]) -> None:
    surface = ledger["runtime_surface"]
    expected_exports = sorted(
        (item["module"], item["symbol"], item["shim_symbol"])
        for item in surface["lean_exports"]
    )
    shim_by_export = {
        item["lean_export"]: item["symbol"] for item in descriptor["shim_functions"]
        if item["lean_export"] is not None
    }
    export_symbols = {item["symbol"] for item in descriptor["lean_exports"]}
    if set(shim_by_export) != export_symbols:
        raise AbiError("canonical ABI descriptor and Ledger-2 exports differ")
    actual_exports = sorted(
        (item["module"], item["symbol"], shim_by_export[item["symbol"]])
        for item in descriptor["lean_exports"]
    )
    if actual_exports != expected_exports:
        raise AbiError("canonical ABI descriptor and Ledger-2 exports differ")
    support = sorted(
        item["symbol"] for item in descriptor["shim_functions"]
        if item["lean_export"] is None
    )
    if support != sorted(surface["shim_support_symbols"]):
        raise AbiError("canonical ABI support symbols and Ledger 2 differ")


def validate_lean_c_prototypes(descriptor: dict[str, Any], sources: dict[str, str]) -> None:
    for export in descriptor["lean_exports"]:
        text = sources.get(export["module"])
        if text is None:
            raise AbiError(f"native ABI: generated C absent for {export['module']}")
        pattern = re.compile(
            rf"LEAN_EXPORT\s+lean_object\s*\*\s*{re.escape(export['symbol'])}\s*\(([^)]*)\)"
        )
        matches = pattern.findall(text)
        if len(matches) != 2:
            raise AbiError(
                f"native ABI: expected declaration and definition for {export['symbol']}"
            )
        for parameters in matches:
            items = [item.strip() for item in parameters.split(",") if item.strip()]
            if len(items) != export["arity"] or any(
                    re.fullmatch(r"lean_object\s*\*\s*(?:[A-Za-z_][A-Za-z0-9_]*)?", item)
                    is None for item in items):
                raise AbiError(f"native ABI: generated Lean prototype drift for {export['symbol']}")


def parse_defined_globals(output: str) -> set[str]:
    result = set()
    for line in output.splitlines():
        fields = line.split()
        if len(fields) < 2:
            continue
        kind, symbol = fields[-2], fields[-1]
        if kind.upper() not in {"B", "D", "R", "S", "T", "W"} or kind != kind.upper():
            continue
        if symbol.startswith("_"):
            symbol = symbol[1:]
        result.add(symbol)
    return result


SHIM_CALLS = {
    "box_grant_fields": ["abort", "lean_alloc_array",
                         "lean_array_set_core", "lean_box_uint64",
                         "lean_array_set_core", "lean_box_uint64",
                         "lean_array_set_core", "lean_box_uint64"],
    "box_op_fields": ["abort", "lean_alloc_array",
                      "lean_array_set_core", "lean_box_uint64",
                      "lean_array_set_core", "lean_box_uint64",
                      "lean_array_set_core", "lean_box_uint64",
                      "lean_array_set_core", "lean_box_uint64",
                      "lean_array_set_core", "lean_box_uint64"],
    "box_parent_words": ["lean_alloc_array", "lean_array_set_core", "lean_box_uint64"],
    "box_u64_array": ["lean_alloc_array", "lean_array_set_core", "lean_box_uint64"],
    "shim_uweave_encode_request": ["box_parent_words", "box_op_fields",
                                    "box_grant_fields", "box_u64_array",
                                    "uwueave_encode_request", "copy_lean_bytes"],
    "shim_uweave_era": ["copy_rust_bytes", "uwueave_era_resolve", "copy_lean_bytes"],
    "shim_uweave_free": ["free"],
    "shim_uweave_init": ["lean_initialize_runtime_module",
                         "initialize_uwueave_Uwueave_RuntimeInit",
                         "lean_io_result_is_ok", "lean_dec_ref",
                         "lean_io_result_show_error", "abort",
                         "lean_io_mark_end_initialization"],
    "shim_uweave_preo_artifact_v2_validate_one": [
        "copy_rust_bytes", "uwueave_preo_artifact_v2_validate_one",
        "lean_sarray_size", "lean_sarray_cptr", "lean_dec_ref"],
    "shim_uweave_replay": ["copy_rust_bytes", "uwueave_replay_kernel", "copy_lean_bytes"],
    "shim_uweave_request_canonical": ["copy_rust_bytes", "uwueave_request_canonical",
                                       "lean_sarray_size", "lean_sarray_cptr",
                                       "lean_dec_ref"],
    "shim_uweave_runtime_auth_v4_check_admission_trace": [
        "copy_rust_bytes", "uwueave_runtime_auth_v4_check_admission_trace",
        "lean_sarray_size", "lean_sarray_cptr", "lean_dec_ref"],
    "shim_uweave_runtime_auth_v4_decode_canonical": [
        "lean_usize_to_nat", "copy_rust_bytes",
        "uwueave_runtime_auth_v4_decode_canonical", "copy_lean_bytes"],
    "shim_uweave_runtime_auth_v4_project_admission": [
        "lean_usize_to_nat", "copy_rust_bytes",
        "uwueave_runtime_auth_v4_project_admission", "copy_lean_bytes"],
    "shim_uweave_seq": ["copy_rust_bytes", "uwueave_seq_kernel", "copy_lean_bytes"],
}


def _ast_nodes(value: Any):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from _ast_nodes(child)
    elif isinstance(value, list):
        for child in value:
            yield from _ast_nodes(child)


def _function_calls(function: dict[str, Any]) -> list[str]:
    calls = []
    for node in _ast_nodes(function):
        if node.get("kind") != "DeclRefExpr":
            continue
        reference = node.get("referencedDecl", {})
        if reference.get("kind") != "FunctionDecl":
            continue
        name = reference.get("name")
        if not isinstance(name, str) or name.startswith("__builtin_object_size"):
            continue
        if name.startswith("__builtin___memcpy"):
            name = "memcpy"
        calls.append(name)
    return calls


def validate_shim_ast(root: Path, shim_path: Path | None = None) -> str:
    shim_path = (shim_path or root / "rust/shim.c").resolve()
    clang_text = os.environ.get("UWUEAVE_ABI_CLANG", "clang")
    clang = shutil.which(clang_text)
    if clang is None:
        raise AbiError(f"shim AST: clang is absent: {clang_text}")
    lean = shutil.which("lean")
    if lean is None:
        raise AbiError("shim AST: lean launcher is absent")
    prefix = subprocess.run([lean, "--print-prefix"], cwd=root, check=False,
                            capture_output=True, text=True, timeout=30)
    if prefix.returncode or not prefix.stdout.strip() or "\n" in prefix.stdout.strip():
        raise AbiError("shim AST: cannot resolve one Lean prefix")
    command = [clang, "-Xclang", "-ast-dump=json", "-fsyntax-only", "-Werror",
               "-I" + str(Path(prefix.stdout.strip()) / "include"), str(shim_path)]
    process = subprocess.run(command, cwd=root, check=False, capture_output=True,
                             timeout=60)
    if process.returncode:
        raise AbiError(f"shim AST: clang rejected shim.c: "
                       f"{process.stderr.decode(errors='replace')[:2000]}")
    try:
        tree = json.loads(process.stdout, object_pairs_hook=_unique_object,
                          parse_constant=_reject_constant)
    except (UnicodeError, json.JSONDecodeError) as exc:
        raise AbiError(f"shim AST: malformed clang JSON: {exc}") from None
    definitions = {}
    for node in _ast_nodes(tree):
        if node.get("kind") != "FunctionDecl" or node.get("name") not in {
                *SHIM_CALLS, "copy_lean_bytes", "copy_rust_bytes"}:
            continue
        if not any(isinstance(child, dict) and child.get("kind") == "CompoundStmt"
                   for child in node.get("inner", [])):
            continue
        definitions[node["name"]] = node
    expected_names = {*SHIM_CALLS, "copy_lean_bytes", "copy_rust_bytes"}
    if set(definitions) != expected_names:
        raise AbiError(f"shim AST: function set drift: {sorted(set(definitions) ^ expected_names)}")
    for name, expected in SHIM_CALLS.items():
        actual = _function_calls(definitions[name])
        if actual != expected:
            raise AbiError(f"shim AST: call/ownership path drift in {name}: {actual}")
    copy_lean = _function_calls(definitions["copy_lean_bytes"])
    required_copy_lean = ["lean_sarray_size", "malloc", "abort", "memcpy",
                          "lean_sarray_cptr", "lean_dec_ref"]
    if copy_lean != required_copy_lean:
        raise AbiError(f"shim AST: owned Lean copy/free path drift: {copy_lean}")
    copy_rust = _function_calls(definitions["copy_rust_bytes"])
    if copy_rust[:2] != ["lean_alloc_sarray", "memcpy"] \
            or copy_rust.count("lean_sarray_cptr") not in {1, 2} \
            or set(copy_rust) != {"lean_alloc_sarray", "memcpy", "lean_sarray_cptr"}:
        raise AbiError(f"shim AST: borrowed Rust copy path drift: {copy_rust}")
    expected_shapes = {
        "box_op_fields": (
            [">", "/", "*", "*", "<", "++", "*", "+", "+", "+", "+"],
            ["18446744073709551615", "5", "5", "5", "0", "5", "1", "2", "3", "4"],
            ["lamport", "replica", "child", "dest", "cite"],
        ),
        "box_grant_fields": (
            [">", "/", "*", "*", "<", "++", "*", "+", "+"],
            ["18446744073709551615", "3", "3", "3", "0", "3", "1", "2"],
            ["id", "parent", "scope"],
        ),
    }
    for name, (expected_ops, expected_ints, expected_members) in expected_shapes.items():
        nodes = list(_ast_nodes(definitions[name]))
        actual_ops = [node.get("opcode") for node in nodes if node.get("kind") in {
            "BinaryOperator", "CompoundAssignOperator", "UnaryOperator"}]
        actual_ints = [node.get("value") for node in nodes
                       if node.get("kind") == "IntegerLiteral"]
        actual_members = [node.get("name") for node in nodes
                          if node.get("kind") == "MemberExpr"]
        if actual_ops != expected_ops or actual_ints != expected_ints \
                or actual_members != expected_members:
            raise AbiError(f"shim AST: bounds/index arithmetic drift in {name}")
    version = subprocess.run([clang, "--version"], check=False, capture_output=True,
                             text=True, timeout=30)
    return version.stdout.splitlines()[0] if version.stdout else str(clang)


def validate_native(root: Path, descriptor: dict[str, Any], observation_path: Path) -> None:
    clang_version = validate_shim_ast(root)
    observation = load_json(observation_path, canonical=True)
    if observation.get("target") not in {
            "aarch64-apple-darwin", "x86_64-unknown-linux-gnu"}:
        raise AbiError("native ABI: unsupported observation target")
    modules = observation.get("closure", {}).get("modules", [])
    sources = {}
    for export in descriptor["lean_exports"]:
        if export["module"] not in modules:
            raise AbiError(f"native ABI: export module absent from closure: {export['module']}")
        path = root / ".lake/build/ir" / Path(*export["module"].split(".")).with_suffix(".c")
        sources[export["module"]] = stable_bytes(path).decode()
    validate_lean_c_prototypes(descriptor, sources)

    archive = Path(observation["archive"]["path"])
    if hashlib.sha256(stable_bytes(archive)).hexdigest() != observation["archive"]["sha256"]:
        raise AbiError("native ABI: archive differs from observation")
    shim_members = [item for item in observation["archive"]["members"]
                    if item.get("kind") == "shim"]
    if len(shim_members) != 1:
        raise AbiError("native ABI: observation lacks exactly one shim member")
    archiver = Path(observation["tools"]["verifier_archiver"]["path"])
    extracted = subprocess.run([archiver, "p", archive, shim_members[0]["name"]],
                               check=False, capture_output=True, timeout=30)
    if extracted.returncode or hashlib.sha256(extracted.stdout).hexdigest() \
            != shim_members[0]["sha256"]:
        raise AbiError("native ABI: cannot recover observed shim member")
    with tempfile.TemporaryDirectory(prefix="uwueave-abi-shim-") as temporary:
        object_path = Path(temporary) / "shim.o"
        object_path.write_bytes(extracted.stdout)
        nm = subprocess.run(["nm", "-g", object_path], check=False, capture_output=True,
                            text=True, timeout=30)
        if nm.returncode:
            raise AbiError(f"native ABI: nm failed: {nm.stderr.strip()}")
    actual = parse_defined_globals(nm.stdout)
    expected = {item["symbol"] for item in descriptor["shim_functions"]}
    if actual != expected:
        raise AbiError(f"native ABI: shim global allowlist drift: {sorted(actual ^ expected)}")
    print(f"abi-gate: shim AST checked by {clang_version}")


def check_source(root: Path) -> dict[str, Any]:
    root = root.resolve()
    descriptor = load_descriptor(root)
    ledger = load_json(root / LEDGER, canonical=True)
    validate_ledger_mapping(descriptor, ledger)
    shim_bytes = stable_bytes(root / "rust/shim.c")
    if hashlib.sha256(shim_bytes).hexdigest() != SHIM_SOURCE_SHA256:
        raise AbiError("C shim: exact mechanically reviewed source drift")
    validate_c_surface(descriptor, shim_bytes.decode())
    validate_rust_surface(descriptor, stable_bytes(root / "rust/src/ffi.rs").decode())
    return descriptor


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--root", type=Path, default=Path.cwd())
    subparsers = parser.add_subparsers(dest="command", required=True)
    subparsers.add_parser("source")
    native = subparsers.add_parser("native")
    native.add_argument("--observation", type=Path, required=True)
    args = parser.parse_args(argv)
    try:
        descriptor = check_source(args.root)
        if args.command == "native":
            validate_native(args.root.resolve(), descriptor, args.observation.resolve())
    except (AbiError, KeyError, UnicodeError, OSError, subprocess.TimeoutExpired) as exc:
        print(f"abi-gate: FAIL: {exc}", file=sys.stderr)
        return 1
    suffix = " source" if args.command == "source" else " native"
    print(f"abi-gate: OK ({suffix.strip()})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
