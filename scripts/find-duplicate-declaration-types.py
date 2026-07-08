#!/usr/bin/env python3
"""Find declarations with exactly identical exported Lean type strings."""

from __future__ import annotations

import argparse
import csv
import hashlib
import sys
from collections import defaultdict


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


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Group exported declaration CSV rows by exact Lean type."
    )
    parser.add_argument("csv_file", help="CSV from scripts/export-declarations.lean")
    parser.add_argument(
        "--kind",
        action="append",
        help="Only include this kind; may be repeated, e.g. --kind theorem",
    )
    parser.add_argument(
        "--include-generated",
        action="store_true",
        help="Include compiler-generated auxiliary declaration names.",
    )
    parser.add_argument(
        "--include-private",
        action="store_true",
        help="Include private declarations.",
    )
    parser.add_argument(
        "--min-count",
        type=int,
        default=2,
        help="Minimum group size to print.",
    )
    parser.add_argument(
        "--normalized",
        action="store_true",
        help="Group by normalized_type instead of raw type.",
    )
    parser.add_argument(
        "--allow-normalization-failures",
        action="store_true",
        help="With --normalized, skip rows whose normalized_type was not generated.",
    )
    args = parser.parse_args()

    wanted_kinds = set(args.kind or [])
    groups: dict[str, list[dict[str, str]]] = defaultdict(list)
    normalization_failures = 0
    normalized_column_missing = False

    with open(args.csv_file, newline="") as f:
        reader = csv.DictReader(f)
        if args.normalized and "normalized_type" not in (reader.fieldnames or []):
            normalized_column_missing = True
        for row in reader:
            if wanted_kinds and row.get("kind") not in wanted_kinds:
                continue
            if not args.include_private and row.get("is_private") == "true":
                continue
            generated = row.get("is_generated") == "true" or generated_name(
                row.get("name", "")
            )
            if not args.include_generated and generated:
                continue
            if args.normalized:
                if row.get("normalization_ok") == "false":
                    normalization_failures += 1
                    continue
                key = row.get("normalized_type")
            else:
                key = row.get("type")
            if not key:
                continue
            groups[key].append(row)

    if normalized_column_missing:
        print(
            "--normalized requested, but CSV has no normalized_type column",
            file=sys.stderr,
        )
        return 2

    if args.normalized and normalization_failures and not args.allow_normalization_failures:
        print(
            "--normalized skipped "
            f"{normalization_failures} rows without successful normalized_type; "
            "pass --allow-normalization-failures to print partial groups",
            file=sys.stderr,
        )
        return 2

    writer = csv.writer(sys.stdout)
    key_label = "normalized_type" if args.normalized else "type"
    writer.writerow(["type_hash", "count", key_label, "declarations"])
    for type_text, rows in sorted(
        groups.items(), key=lambda item: (-len(item[1]), item[0])
    ):
        if len(rows) < args.min_count:
            continue
        digest = hashlib.sha256(type_text.encode()).hexdigest()[:16]
        decls = "; ".join(
            f'{row["name"]} [{row.get("file", row.get("module", ""))}]'
            for row in sorted(rows, key=lambda r: r["name"])
        )
        writer.writerow([digest, len(rows), type_text, decls])

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
