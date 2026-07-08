#!/usr/bin/env python3
"""Summarize declaration CSV rows that deserve manual review."""

from __future__ import annotations

import argparse
import csv
from collections import Counter, defaultdict


def bool_col(row: dict[str, str], name: str) -> bool:
    return row.get(name) == "true"


def generated_name(name: str) -> bool:
    return (
        "._@" in name
        or "._proof_" in name
        or "._simp_" in name
        or "._aux_" in name
        or ".«_aux_" in name
        or ".match_" in name
        or ".rec_" in name
        or ".below" in name
        or ".brecOn" in name
        or ".noConfusion" in name
        or ".casesOn" in name
        or name.endswith(".rec")
        or name.endswith(".recOn")
        or ".ctorIdx" in name
        or "._sunfold" in name
        or "._unsafe_rec" in name
        or "._flat_ctor" in name
        or ".eq_def" in name
        or ".sizeOf_spec" in name
        or any(
            part.startswith("eq_") and part[3:].isdigit()
            for part in name.split(".")
        )
    )


def visible(row: dict[str, str], include_generated: bool, include_private: bool) -> bool:
    generated = bool_col(row, "is_generated") or generated_name(row.get("name", ""))
    if not include_generated and generated:
        return False
    if not include_private and bool_col(row, "is_private"):
        return False
    return True


def sorry_dependency(row: dict[str, str]) -> str:
    return row.get("depends_on_sorry", row.get("has_sorry", ""))


def short_name(row: dict[str, str]) -> str:
    name = row.get("name", "")
    return row.get("short_name") or name.rsplit(".", 1)[-1]


def print_rows(title: str, rows: list[dict[str, str]], limit: int) -> None:
    print(f"\n## {title} ({len(rows)})")
    for row in rows[:limit]:
        print(
            f"- {row['name']} [{row.get('file', row.get('module', ''))}] "
            f"kind={row.get('kind', '')} depends_on_sorry={sorry_dependency(row)}"
        )
    if len(rows) > limit:
        print(f"- ... {len(rows) - limit} more")


def duplicate_groups(
    rows: list[dict[str, str]], key: str, min_count: int
) -> list[tuple[str, list[dict[str, str]]]]:
    groups: dict[str, list[dict[str, str]]] = defaultdict(list)
    for row in rows:
        value = row.get(key)
        if value:
            groups[value].append(row)
    return sorted(
        [(value, group) for value, group in groups.items() if len(group) >= min_count],
        key=lambda item: (-len(item[1]), item[0]),
    )


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Print review-oriented smells from declaration CSV data."
    )
    parser.add_argument("csv_file")
    parser.add_argument("--limit", type=int, default=20)
    parser.add_argument("--long-name", type=int, default=100)
    parser.add_argument("--long-short-name", type=int, default=80)
    parser.add_argument("--long-type", type=int, default=1200)
    parser.add_argument("--include-generated", action="store_true")
    parser.add_argument("--include-private", action="store_true")
    parser.add_argument(
        "--kind",
        action="append",
        help="Only include this kind in the review queue; may be repeated.",
    )
    args = parser.parse_args()

    with open(args.csv_file, newline="") as f:
        rows = list(csv.DictReader(f))

    wanted_kinds = set(args.kind or [])
    review_rows = [
        row
        for row in rows
        if visible(row, args.include_generated, args.include_private)
        and (not wanted_kinds or row.get("kind") in wanted_kinds)
    ]

    print(f"# Declaration Smell Summary")
    print(f"rows: {len(rows)}")
    print(f"review_rows: {len(review_rows)}")
    print(f"kinds: {dict(Counter(row.get('kind', '') for row in review_rows))}")

    print_rows(
        "Declarations depending on sorry",
        [row for row in review_rows if sorry_dependency(row) == "true"],
        args.limit,
    )
    print_rows(
        "Long fully qualified names",
        sorted(
            [row for row in review_rows if len(row.get("name", "")) >= args.long_name],
            key=lambda row: (-len(row.get("name", "")), row.get("name", "")),
        ),
        args.limit,
    )
    print_rows(
        "Long local declaration names",
        sorted(
            [
                row for row in review_rows
                if len(short_name(row)) >= args.long_short_name
            ],
            key=lambda row: (-len(short_name(row)), row.get("name", "")),
        ),
        args.limit,
    )
    print_rows(
        "Long types",
        sorted(
            [row for row in review_rows if len(row.get("type", "")) >= args.long_type],
            key=lambda row: (-len(row.get("type", "")), row.get("name", "")),
        ),
        args.limit,
    )
    print_rows(
        "Axioms and opaques",
        [row for row in review_rows if row.get("kind") in {"axiom", "opaque"}],
        args.limit,
    )

    duplicate_modes = [
        ("type", "Exact duplicate type groups", review_rows),
        (
            "normalized_type",
            "Normalized duplicate type groups",
            [
                row
                for row in review_rows
                if row.get("normalization_ok", "true") == "true"
            ],
        ),
    ]
    skipped_normalized = sum(
        1 for row in review_rows if row.get("normalization_ok") == "false"
    )
    for key, title, rows_for_mode in duplicate_modes:
        groups = duplicate_groups(rows_for_mode, key, 2)
        print(f"\n## {title} ({len(groups)})")
        if key == "normalized_type" and skipped_normalized:
            print(
                f"- skipped {skipped_normalized} rows without successful normalized_type"
            )
        for value, group in groups[: args.limit]:
            names = "; ".join(row["name"] for row in group[:6])
            suffix = "" if len(group) <= 6 else f"; ... {len(group) - 6} more"
            print(f"- count={len(group)} {names}{suffix}")
        if len(groups) > args.limit:
            print(f"- ... {len(groups) - args.limit} more groups")

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
