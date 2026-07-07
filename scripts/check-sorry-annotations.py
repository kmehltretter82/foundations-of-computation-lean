#!/usr/bin/env python3
"""Check that Lean `sorry` placeholders have nearby classification comments."""

from __future__ import annotations

import argparse
import bisect
import re
import sys
from dataclasses import dataclass
from pathlib import Path


CLASSIFICATIONS = ("obligation", "blocked", "invalid")
SORRY_RE = re.compile(r"(?<![\w'])sorry(?![\w'])", re.UNICODE)


@dataclass(frozen=True)
class Comment:
    start_line: int
    end_line: int
    text: str


def line_starts(text: str) -> list[int]:
    starts = [0]
    for index, char in enumerate(text):
        if char == "\n":
            starts.append(index + 1)
    return starts


def line_of(starts: list[int], index: int) -> int:
    return bisect.bisect_right(starts, index)


def masked_source_and_comments(text: str) -> tuple[str, list[Comment]]:
    starts = line_starts(text)
    chars = list(text)
    comments: list[Comment] = []
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
            comments.append(
                Comment(line_of(starts, start), line_of(starts, end), text[start:end])
            )
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
            end = index
            comments.append(
                Comment(line_of(starts, start), line_of(starts, end), text[start:end])
            )
            mask_range(start, end)
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

    return "".join(chars), comments


def annotated(
    comments: list[Comment], sorry_line: int, window_lines: int
) -> bool:
    for comment in comments:
        if comment.end_line <= sorry_line and sorry_line - comment.end_line <= window_lines:
            lower = comment.text.lower()
            if any(classification in lower for classification in CLASSIFICATIONS):
                return True
    return False


def lean_files(paths: list[Path]) -> list[Path]:
    files: list[Path] = []
    for path in paths:
        if path.is_dir():
            files.extend(sorted(path.rglob("*.lean")))
        elif path.suffix == ".lean":
            files.append(path)
    return files


def check_file(path: Path, window_lines: int) -> list[tuple[Path, int]]:
    text = path.read_text(encoding="utf-8")
    starts = line_starts(text)
    masked, comments = masked_source_and_comments(text)
    failures: list[tuple[Path, int]] = []
    for match in SORRY_RE.finditer(masked):
        sorry_line = line_of(starts, match.start())
        if not annotated(comments, sorry_line, window_lines):
            failures.append((path, sorry_line))
    return failures


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description=(
            "Require each Lean sorry to have a nearby preceding comment "
            "classified as obligation, blocked, or invalid."
        )
    )
    parser.add_argument(
        "paths",
        nargs="*",
        type=Path,
        default=[Path("FoC")],
        help="Lean files or directories to scan (default: FoC)",
    )
    parser.add_argument(
        "--window-lines",
        type=int,
        default=16,
        help="maximum distance from a classification comment to a sorry",
    )
    args = parser.parse_args(argv)

    failures: list[tuple[Path, int]] = []
    for path in lean_files(args.paths):
        failures.extend(check_file(path, args.window_lines))

    if failures:
        expected = ", ".join(CLASSIFICATIONS)
        for path, line in failures:
            print(
                f"{path}:{line}: sorry missing nearby classification comment "
                f"({expected})",
                file=sys.stderr,
            )
        return 1

    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
