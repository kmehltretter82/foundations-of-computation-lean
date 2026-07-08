#!/usr/bin/env python3
"""Audit Lean compiler naming and path limits.

The strict limits come from the repository naming refactor plan.  Because the
current tree intentionally starts with known debt, this checker can also compare
against a checked-in baseline and fail only on newly introduced violations.
"""

from __future__ import annotations

import argparse
import json
import re
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


FORMAL_PREFIX = "formal"
LEAN_ROOT = Path("FoC")
COMPILER_ROOT = Path("FoC/Computability/Compiler")

MAX_COMPILER_DIR_DEPTH = 5
MAX_COMPILER_REL_PATH = 80
MAX_FORMAL_LEAN_PATH = 160
MAX_DECL_NAME = 128

DECL_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable|unsafe|partial)\s+)*"
    r"(?:(?:theorem|lemma|def|abbrev|structure|inductive|class|opaque|axiom)"
    r"\s+([^\s(:]+)|instance(?:\s+([^\s(:]+))?)",
    re.MULTILINE,
)


@dataclass(frozen=True)
class Violation:
    key: str
    path: str
    line: int | None
    value: int | str
    limit: int | str

    def to_json(self) -> dict[str, Any]:
        return {
            "key": self.key,
            "path": self.path,
            "line": self.line,
            "value": self.value,
            "limit": self.limit,
        }

    def stable_id(self) -> str:
        line = "" if self.line is None else str(self.line)
        return f"{self.key}\t{self.path}\t{line}\t{self.value}\t{self.limit}"


def line_starts(text: str) -> list[int]:
    starts = [0]
    for index, char in enumerate(text):
        if char == "\n":
            starts.append(index + 1)
    return starts


def line_of(starts: list[int], index: int) -> int:
    lo = 0
    hi = len(starts)
    while lo + 1 < hi:
        mid = (lo + hi) // 2
        if starts[mid] <= index:
            lo = mid
        else:
            hi = mid
    return lo + 1


def masked_source(text: str) -> str:
    chars = list(text)
    index = 0
    length = len(text)

    def mask_range(start: int, end: int) -> None:
        for pos in range(start, end):
            if chars[pos] != "\n":
                chars[pos] = " "

    while index < length:
        if text.startswith("--", index):
            start = index
            end = text.find("\n", index)
            if end == -1:
                end = length
            mask_range(start, end)
            index = end
        elif text.startswith("/-", index):
            start = index
            depth = 0
            while index < length:
                if text.startswith("/-", index):
                    depth += 1
                    index += 2
                elif text.startswith("-/", index):
                    depth -= 1
                    index += 2
                    if depth == 0:
                        break
                else:
                    index += 1
            mask_range(start, index)
        elif text[index] == '"':
            start = index
            index += 1
            while index < length:
                if text[index] == "\\":
                    index += 2
                elif text[index] == '"':
                    index += 1
                    break
                else:
                    index += 1
            mask_range(start, index)
        else:
            index += 1

    return "".join(chars)


def lean_files(root: Path) -> list[Path]:
    return sorted(path for path in (root / LEAN_ROOT).rglob("*.lean"))


def audit(root: Path) -> dict[str, list[Violation]]:
    violations: dict[str, list[Violation]] = {
        "compiler_dir_depth": [],
        "compiler_rel_path": [],
        "formal_lean_path": [],
        "decl_name": [],
        "route_contracts_file": [],
    }

    for path in lean_files(root):
        rel = path.relative_to(root)
        rel_text = rel.as_posix()
        formal_path = f"{FORMAL_PREFIX}/{rel_text}"
        formal_len = len(formal_path)
        if formal_len > MAX_FORMAL_LEAN_PATH:
            violations["formal_lean_path"].append(
                Violation(
                    "formal_lean_path",
                    formal_path,
                    None,
                    formal_len,
                    MAX_FORMAL_LEAN_PATH,
                )
            )

        try:
            compiler_rel = rel.relative_to(COMPILER_ROOT)
        except ValueError:
            compiler_rel = None

        if compiler_rel is not None:
            compiler_rel_text = compiler_rel.as_posix()
            compiler_rel_len = len(compiler_rel_text)
            if compiler_rel_len > MAX_COMPILER_REL_PATH:
                violations["compiler_rel_path"].append(
                    Violation(
                        "compiler_rel_path",
                        formal_path,
                        None,
                        compiler_rel_len,
                        MAX_COMPILER_REL_PATH,
                    )
                )

            compiler_depth = len(compiler_rel.parent.parts)
            if compiler_depth > MAX_COMPILER_DIR_DEPTH:
                violations["compiler_dir_depth"].append(
                    Violation(
                        "compiler_dir_depth",
                        formal_path,
                        None,
                        compiler_depth,
                        MAX_COMPILER_DIR_DEPTH,
                    )
                )

            if rel.name.endswith("RouteContracts.lean"):
                violations["route_contracts_file"].append(
                    Violation(
                        "route_contracts_file",
                        formal_path,
                        None,
                        rel.name,
                        "no *RouteContracts.lean files",
                    )
                )

        text = path.read_text(encoding="utf-8")
        starts = line_starts(text)
        masked = masked_source(text)
        for match in DECL_RE.finditer(masked):
            name = match.group(1) or match.group(2)
            if not name or name[0] in "[{(":
                continue
            name_len = len(name)
            if name_len > MAX_DECL_NAME:
                violations["decl_name"].append(
                    Violation(
                        "decl_name",
                        formal_path,
                        line_of(starts, match.start(1)),
                        name_len,
                        MAX_DECL_NAME,
                    )
                )

    return violations


def to_jsonable(violations: dict[str, list[Violation]]) -> dict[str, Any]:
    return {
        "limits": {
            "compiler_dir_depth": MAX_COMPILER_DIR_DEPTH,
            "compiler_rel_path": MAX_COMPILER_REL_PATH,
            "formal_lean_path": MAX_FORMAL_LEAN_PATH,
            "decl_name": MAX_DECL_NAME,
            "route_contracts_file": "no new *RouteContracts.lean files",
        },
        "violations": {
            key: [violation.to_json() for violation in value]
            for key, value in violations.items()
        },
    }


def ids_from_json(data: dict[str, Any]) -> dict[str, set[str]]:
    result: dict[str, set[str]] = {}
    for key, values in data["violations"].items():
        result[key] = {
            Violation(
                key=item["key"],
                path=item["path"],
                line=item["line"],
                value=item["value"],
                limit=item["limit"],
            ).stable_id()
            for item in values
        }
    return result


def print_summary(violations: dict[str, list[Violation]]) -> None:
    for key in sorted(violations):
        values = violations[key]
        print(f"{key}: {len(values)}")
        for violation in values[:10]:
            line = "" if violation.line is None else f":{violation.line}"
            print(
                f"  {violation.path}{line}: value {violation.value} "
                f"exceeds limit {violation.limit}"
            )
        if len(values) > 10:
            print(f"  ... {len(values) - 10} more")


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Audit compiler naming/path limits from NAMING_REFACTOR_PLAN.md."
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path("."),
        help="formal repository root (default: current directory)",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="print full JSON report instead of a compact summary",
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="fail if any current violation exists",
    )
    parser.add_argument(
        "--baseline",
        type=Path,
        help="fail only when violations not present in this JSON baseline appear",
    )
    parser.add_argument(
        "--write-baseline",
        type=Path,
        help="write the current violation set as a JSON baseline",
    )
    args = parser.parse_args(argv)

    root = args.root.resolve()
    violations = audit(root)
    jsonable = to_jsonable(violations)

    if args.write_baseline is not None:
        args.write_baseline.write_text(
            json.dumps(jsonable, indent=2, sort_keys=True) + "\n",
            encoding="utf-8",
        )

    if args.json:
        print(json.dumps(jsonable, indent=2, sort_keys=True))
    else:
        print_summary(violations)

    failed = False
    if args.strict:
        failed = any(violations.values())

    if args.baseline is not None:
        baseline = json.loads(args.baseline.read_text(encoding="utf-8"))
        baseline_ids = ids_from_json(baseline)
        current_ids = ids_from_json(jsonable)
        for key in sorted(current_ids):
            new_ids = sorted(current_ids[key] - baseline_ids.get(key, set()))
            for stable_id in new_ids:
                print(f"new {key} violation: {stable_id}", file=sys.stderr)
            failed = failed or bool(new_ids)

    return 1 if failed else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
