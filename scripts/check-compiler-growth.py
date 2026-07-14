#!/usr/bin/env python3
"""Enforce the Compiler size baseline and bounded campaign growth loans.

The checker deliberately measures whole physical Lean files.  Moving code
between files or splitting one implementation into several modules therefore
cannot evade the total budget.  Existing large files and deliberately opt-in
modules are grandfathered by the checked-in baseline, but they may not grow or
gain new peers without an explicit baseline review.
"""

from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import subprocess
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Any


LEAN_ROOT = Path("FoC")
FOC_ROOT_MODULE = "FoC"
FOC_ROOT_FILE = Path("FoC.lean")
COMPILER_ROOT = Path("FoC/Computability/Compiler")
MAX_NEW_FILE_LINES = 1_500
DEFAULT_NET_GROWTH = 10_000
MAX_OUTSTANDING_GROWTH_LOANS = 10_000

IMPORT_RE = re.compile(r"^import\s+([^\s]+)\s*$", re.MULTILINE)
DIRECT_SORRY_RE = re.compile(r"^\s*sorry(?:\s|$)", re.MULTILINE)


@dataclass(frozen=True)
class Metrics:
    raw_lines: int
    file_count: int
    direct_sorries: int
    over_limit_files: dict[str, int]
    unreachable_modules: list[str]

    def to_json(self) -> dict[str, Any]:
        return {
            "raw_lines": self.raw_lines,
            "file_count": self.file_count,
            "direct_sorries": self.direct_sorries,
            "over_limit_files": dict(sorted(self.over_limit_files.items())),
            "unreachable_modules": sorted(self.unreachable_modules),
        }


@dataclass(frozen=True)
class CampaignResult:
    name: str
    allowance: int
    failures: list[str]
    historical_debt: bool


def source_lines(path: Path) -> list[str]:
    return path.read_text(encoding="utf-8").splitlines()


def line_count(path: Path) -> int:
    return len(source_lines(path))


def compiler_files(root: Path) -> list[Path]:
    return sorted((root / COMPILER_ROOT).rglob("*.lean"))


def module_name(root: Path, path: Path) -> str:
    rel = path.relative_to(root).with_suffix("")
    return ".".join(rel.parts)


def module_graph(root: Path) -> tuple[dict[str, Path], dict[str, list[str]]]:
    paths = [root / FOC_ROOT_FILE]
    paths.extend(sorted((root / LEAN_ROOT).rglob("*.lean")))
    modules = {module_name(root, path): path for path in paths}
    edges: dict[str, list[str]] = {name: [] for name in modules}
    for name, path in modules.items():
        text = path.read_text(encoding="utf-8")
        edges[name] = [
            imported
            for imported in IMPORT_RE.findall(text)
            if imported in modules
        ]
    return modules, edges


def unreachable_compiler_modules(root: Path) -> list[str]:
    modules, edges = module_graph(root)
    reachable: set[str] = set()
    pending = [FOC_ROOT_MODULE]
    while pending:
        name = pending.pop()
        if name in reachable:
            continue
        reachable.add(name)
        pending.extend(edges.get(name, []))

    compiler_prefix = "FoC.Computability.Compiler."
    return sorted(
        name
        for name in modules
        if name.startswith(compiler_prefix) and name not in reachable
    )


def collect_metrics(root: Path) -> Metrics:
    files = compiler_files(root)
    counts = {
        path.relative_to(root).as_posix(): line_count(path)
        for path in files
    }
    direct_sorries = sum(
        len(DIRECT_SORRY_RE.findall(path.read_text(encoding="utf-8")))
        for path in files
    )
    return Metrics(
        raw_lines=sum(counts.values()),
        file_count=len(files),
        direct_sorries=direct_sorries,
        over_limit_files={
            path: count
            for path, count in counts.items()
            if count > MAX_NEW_FILE_LINES
        },
        unreachable_modules=unreachable_compiler_modules(root),
    )


def baseline_json(metrics: Metrics) -> dict[str, Any]:
    return {
        "limits": {
            "max_new_file_lines": MAX_NEW_FILE_LINES,
            "default_net_growth": DEFAULT_NET_GROWTH,
            "max_outstanding_growth_loans": MAX_OUTSTANDING_GROWTH_LOANS,
        },
        "metrics": metrics.to_json(),
    }


def read_json(path: Path) -> dict[str, Any]:
    return json.loads(path.read_text(encoding="utf-8"))


def git_head(root: Path) -> str:
    result = subprocess.run(
        ["git", "rev-parse", "HEAD"],
        cwd=root,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    return result.stdout.strip()


def baseline_review_failures(
    root: Path, path: Path, baseline: dict[str, Any]
) -> list[str]:
    review = baseline.get("review")
    if not isinstance(review, dict):
        return [f"{path}: missing reviewed baseline provenance"]
    reason = review.get("reason")
    recorded_against = str(review.get("recorded_against", ""))
    failures: list[str] = []
    if not isinstance(reason, str) or not reason.strip():
        failures.append(f"{path}: baseline review reason is empty")
    if not re.fullmatch(r"[0-9a-f]{40}", recorded_against):
        failures.append(
            f"{path}: review.recorded_against must be a full Git hash"
        )
    elif not git_commit_exists(root, recorded_against):
        failures.append(
            f"{path}: reviewed baseline commit is absent: {recorded_against}"
        )
    elif not git_is_ancestor(root, recorded_against):
        failures.append(
            f"{path}: reviewed baseline commit is not an ancestor of HEAD: "
            f"{recorded_against}"
        )
    return failures


def git_diff_net(root: Path, base: str, paths: list[str]) -> tuple[int, int]:
    command = ["git", "diff", "--numstat", base, "--", *paths]
    result = subprocess.run(
        command,
        cwd=root,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    additions = 0
    deletions = 0
    for line in result.stdout.splitlines():
        fields = line.split("\t", 2)
        if (
            len(fields) != 3
            or fields[0] == "-"
            or fields[1] == "-"
            or not fields[2].endswith(".lean")
        ):
            continue
        additions += int(fields[0])
        deletions += int(fields[1])

    untracked = subprocess.run(
        ["git", "ls-files", "--others", "--exclude-standard", "--", *paths],
        cwd=root,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
    )
    for relative in untracked.stdout.splitlines():
        path = root / relative
        if path.suffix == ".lean":
            additions += line_count(path)
    return additions, deletions


def git_commit_exists(root: Path, revision: str) -> bool:
    result = subprocess.run(
        ["git", "cat-file", "-e", f"{revision}^{{commit}}"],
        cwd=root,
        text=True,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    return result.returncode == 0


def git_is_ancestor(root: Path, ancestor: str, descendant: str = "HEAD") -> bool:
    result = subprocess.run(
        ["git", "merge-base", "--is-ancestor", ancestor, descendant],
        cwd=root,
        text=True,
        stdout=subprocess.DEVNULL,
        stderr=subprocess.DEVNULL,
    )
    return result.returncode == 0


def check_campaign(root: Path, path: Path) -> CampaignResult:
    campaign = read_json(path)
    required = {
        "name",
        "base_commit",
        "frontier",
        "paths",
        "focused_checks",
        "required_axiom_clean",
        "allow_net_growth",
    }
    missing = sorted(required - campaign.keys())
    if missing:
        return CampaignResult(
            path.stem,
            0,
            [f"{path}: missing campaign fields: {', '.join(missing)}"],
            False,
        )

    name = str(campaign["name"])
    failures: list[str] = []
    base = str(campaign["base_commit"])
    if not re.fullmatch(r"[0-9a-f]{40}", base):
        failures.append(f"{path}: base_commit must be a full 40-digit Git hash")
    elif not git_commit_exists(root, base):
        failures.append(f"{path}: base_commit is not present in this checkout: {base}")

    for field in ("frontier",):
        if not isinstance(campaign[field], str) or not campaign[field].strip():
            failures.append(f"{path}: {field} must be a nonempty string")

    for field in ("focused_checks", "required_axiom_clean"):
        value = campaign[field]
        if not isinstance(value, list) or not value or not all(
            isinstance(item, str) and item.strip() for item in value
        ):
            failures.append(f"{path}: {field} must be a nonempty string list")

    paths = campaign["paths"]
    if not isinstance(paths, list) or not paths:
        failures.append(f"{path}: campaign paths must be a nonempty list")
        paths = []
    elif not all(
        isinstance(item, str)
        and (
            item == COMPILER_ROOT.as_posix()
            or item.startswith(f"{COMPILER_ROOT.as_posix()}/")
        )
        for item in paths
    ):
        failures.append(
            f"{path}: every campaign path must stay under {COMPILER_ROOT}"
        )

    try:
        allowance = int(campaign["allow_net_growth"])
    except (TypeError, ValueError):
        allowance = 0
        failures.append(f"{path}: allow_net_growth must be an integer")
    if allowance < 0:
        failures.append(f"{path}: allow_net_growth may not be negative")

    historical_debt = bool(campaign.get("historical_debt", False))
    if historical_debt:
        reason = campaign.get("historical_debt_reason")
        if not isinstance(reason, str) or not reason.strip():
            failures.append(
                f"{path}: historical_debt requires historical_debt_reason"
            )
    elif allowance > 5_000:
        failures.append(f"{path}: ordinary growth loans may not exceed 5000")
    elif allowance > 1_500:
        review = campaign.get("architecture_review")
        if not isinstance(review, dict):
            failures.append(
                f"{path}: growth loans above 1500 require architecture_review"
            )
        else:
            reason = review.get("reason")
            recorded_against = str(review.get("recorded_against", ""))
            if not isinstance(reason, str) or not reason.strip():
                failures.append(
                    f"{path}: architecture_review.reason must be nonempty"
                )
            if not re.fullmatch(r"[0-9a-f]{40}", recorded_against):
                failures.append(
                    f"{path}: architecture_review.recorded_against must be a "
                    "full Git hash"
                )
            elif not git_commit_exists(root, recorded_against):
                failures.append(
                    f"{path}: reviewed commit is absent: {recorded_against}"
                )
            elif not git_is_ancestor(root, recorded_against):
                failures.append(
                    f"{path}: reviewed commit is not an ancestor of HEAD: "
                    f"{recorded_against}"
                )

    if failures or not paths:
        return CampaignResult(name, allowance, failures, historical_debt)

    additions, deletions = git_diff_net(
        root, base, [str(item) for item in paths]
    )
    net = additions - deletions
    print(
        f"campaign {name}: +{additions} -{deletions} "
        f"net {net}, allowance {allowance}"
    )
    if net > allowance:
        failures.append(
            f"campaign {name} exceeds its cumulative growth loan: "
            f"net {net} > {allowance}"
        )
    return CampaignResult(name, allowance, failures, historical_debt)


def read_unreachable_allowlist(path: Path) -> dict[str, dict[str, str]]:
    data = read_json(path)
    entries = data.get("modules", [])
    if not isinstance(entries, list):
        raise ValueError(f"{path}: modules must be a list")
    result: dict[str, dict[str, str]] = {}
    required = {"module", "category", "reason", "intended_consumer"}
    allowed_categories = {"active", "debug", "guardrail", "public-facade"}
    for entry in entries:
        if not isinstance(entry, dict) or not required.issubset(entry):
            raise ValueError(
                f"{path}: every module needs {', '.join(sorted(required))}"
            )
        module = str(entry["module"])
        if module in result:
            raise ValueError(f"{path}: duplicate module entry: {module}")
        category = str(entry["category"])
        if category not in allowed_categories:
            raise ValueError(
                f"{path}: invalid category for {module}: {category}"
            )
        if not str(entry["reason"]).strip() or not str(
            entry["intended_consumer"]
        ).strip():
            raise ValueError(f"{path}: empty rationale for {module}")
        result[module] = {str(key): str(value) for key, value in entry.items()}
    return result


def compare_unreachable_allowlist(
    current: Metrics, allowlist: dict[str, dict[str, str]]
) -> list[str]:
    actual = set(current.unreachable_modules)
    allowed = set(allowlist)
    failures = [
        f"Compiler module lacks an unreachable-module classification: {name}"
        for name in sorted(actual - allowed)
    ]
    failures.extend(
        f"stale unreachable-module allowlist entry: {name}"
        for name in sorted(allowed - actual)
    )
    return failures


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


def duplicate_theorem_groups(csv_path: Path) -> dict[str, list[str]]:
    by_type: dict[str, list[str]] = {}
    with csv_path.open(newline="", encoding="utf-8") as stream:
        for row in csv.DictReader(stream):
            name = row.get("name", "")
            if (
                row.get("kind") != "theorem"
                or row.get("is_private") == "true"
                or row.get("is_generated") == "true"
                or generated_name(name)
            ):
                continue
            type_text = row.get("type", "")
            if type_text:
                by_type.setdefault(type_text, []).append(name)
    return {
        hashlib.sha256(type_text.encode()).hexdigest()[:16]: sorted(names)
        for type_text, names in by_type.items()
        if len(names) >= 2
    }


def duplicate_baseline_json(groups: dict[str, list[str]]) -> dict[str, Any]:
    return {
        "description": (
            "Exact exported theorem-type duplicates; generated and private "
            "declarations are excluded."
        ),
        "groups": dict(sorted(groups.items())),
    }


def compare_duplicate_groups(
    current: dict[str, list[str]], baseline: dict[str, Any]
) -> list[str]:
    expected = {
        str(group_hash): set(str(name) for name in names)
        for group_hash, names in baseline.get("groups", {}).items()
    }
    failures: list[str] = []
    for group_hash, names in sorted(current.items()):
        old_names = expected.get(group_hash)
        if old_names is None:
            failures.append(
                "new exact duplicate theorem-type group "
                f"{group_hash}: {', '.join(names)}"
            )
            continue
        additions = sorted(set(names) - old_names)
        if additions:
            failures.append(
                "exact duplicate theorem-type group grew "
                f"{group_hash}: {', '.join(additions)}"
            )
    return failures


def compare(
    current: Metrics,
    baseline: dict[str, Any],
    allow_net_growth: int,
    check_unreachable: bool = True,
) -> list[str]:
    failures: list[str] = []
    expected = baseline["metrics"]
    baseline_lines = int(expected["raw_lines"])
    line_limit = baseline_lines + allow_net_growth
    if current.raw_lines > line_limit:
        failures.append(
            "Compiler raw LOC exceeds baseline allowance: "
            f"{current.raw_lines} > {baseline_lines} + {allow_net_growth}"
        )

    baseline_sorries = int(expected["direct_sorries"])
    if current.direct_sorries > baseline_sorries:
        failures.append(
            "direct Compiler sorry count increased: "
            f"{current.direct_sorries} > {baseline_sorries}"
        )

    baseline_large = {
        str(path): int(count)
        for path, count in expected["over_limit_files"].items()
    }
    for path, count in sorted(current.over_limit_files.items()):
        old_count = baseline_large.get(path)
        if old_count is None:
            failures.append(
                f"new file above {MAX_NEW_FILE_LINES} lines: {path} ({count})"
            )
        elif count > old_count:
            failures.append(
                f"existing oversized file grew: {path} ({old_count} -> {count})"
            )

    if check_unreachable:
        allowed_unreachable = set(expected["unreachable_modules"])
        new_unreachable = sorted(
            set(current.unreachable_modules) - allowed_unreachable
        )
        failures.extend(
            f"new Compiler module unreachable from FoC.lean: {name}"
            for name in new_unreachable
        )
    return failures


def print_metrics(metrics: Metrics) -> None:
    print(f"Compiler raw LOC: {metrics.raw_lines}")
    print(f"Compiler Lean files: {metrics.file_count}")
    print(f"Compiler direct sorries: {metrics.direct_sorries}")
    print(
        f"Compiler files above {MAX_NEW_FILE_LINES} lines: "
        f"{len(metrics.over_limit_files)}"
    )
    print(
        "Compiler modules unreachable from FoC.lean: "
        f"{len(metrics.unreachable_modules)}"
    )


def main(argv: list[str]) -> int:
    parser = argparse.ArgumentParser(
        description="Check Compiler size, reachability, and campaign budgets."
    )
    parser.add_argument(
        "--root",
        type=Path,
        default=Path("."),
        help="formal repository root (default: current directory)",
    )
    parser.add_argument(
        "--baseline",
        type=Path,
        help="checked-in Compiler growth baseline",
    )
    parser.add_argument(
        "--write-baseline",
        type=Path,
        help="write current metrics as a new baseline",
    )
    parser.add_argument(
        "--approve-baseline-update",
        metavar="REASON",
        help=(
            "required review reason when writing a baseline; prevents an "
            "accidental baseline ratchet"
        ),
    )
    parser.add_argument(
        "--allow-net-growth",
        type=int,
        default=0,
        help="temporary total global growth allowance override",
    )
    parser.add_argument(
        "--campaign",
        type=Path,
        action="append",
        default=[],
        help="campaign manifest with a pinned base and cumulative allowance",
    )
    parser.add_argument(
        "--unreachable-allowlist",
        type=Path,
        help="classified allowlist for modules intentionally outside FoC.lean",
    )
    parser.add_argument(
        "--declarations-csv",
        type=Path,
        help="raw Compiler declaration CSV used to audit exact duplicate types",
    )
    parser.add_argument(
        "--duplicate-baseline",
        type=Path,
        help="checked-in baseline of exact duplicate theorem-type groups",
    )
    parser.add_argument(
        "--write-duplicate-baseline",
        type=Path,
        help="write duplicate groups collected from --declarations-csv",
    )
    parser.add_argument(
        "--json",
        action="store_true",
        help="print current metrics as JSON",
    )
    args = parser.parse_args(argv)

    root = args.root.resolve()
    metrics = collect_metrics(root)

    if args.write_baseline is not None:
        if not args.approve_baseline_update:
            print(
                "--write-baseline requires --approve-baseline-update REASON",
                file=sys.stderr,
            )
            return 2
        output = baseline_json(metrics)
        output["review"] = {
            "reason": args.approve_baseline_update,
            "recorded_against": git_head(root),
        }
        args.write_baseline.write_text(
            json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )

    duplicate_groups: dict[str, list[str]] | None = None
    if args.declarations_csv is not None:
        duplicate_groups = duplicate_theorem_groups(args.declarations_csv)
    if args.write_duplicate_baseline is not None:
        if duplicate_groups is None:
            print(
                "--write-duplicate-baseline requires --declarations-csv",
                file=sys.stderr,
            )
            return 2
        if not args.approve_baseline_update:
            print(
                "--write-duplicate-baseline requires "
                "--approve-baseline-update REASON",
                file=sys.stderr,
            )
            return 2
        output = duplicate_baseline_json(duplicate_groups)
        output["review"] = {
            "reason": args.approve_baseline_update,
            "recorded_against": git_head(root),
        }
        args.write_duplicate_baseline.write_text(
            json.dumps(output, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )

    if args.json:
        print(json.dumps(baseline_json(metrics), indent=2, sort_keys=True))
    else:
        print_metrics(metrics)

    failures: list[str] = []
    campaign_results = [check_campaign(root, campaign) for campaign in args.campaign]
    for result in campaign_results:
        failures.extend(result.failures)
    outstanding_allowances = sum(
        result.allowance
        for result in campaign_results
        if not result.historical_debt
    )
    if outstanding_allowances > MAX_OUTSTANDING_GROWTH_LOANS:
        failures.append(
            "outstanding Compiler growth loans exceed the global cap: "
            f"{outstanding_allowances} > {MAX_OUTSTANDING_GROWTH_LOANS}"
        )
    effective_global_growth = max(args.allow_net_growth, outstanding_allowances)

    if args.baseline is not None:
        baseline = read_json(args.baseline)
        failures.extend(baseline_review_failures(root, args.baseline, baseline))
        limits = baseline.get("limits", {})
        reviewed_default_growth = limits.get("default_net_growth", 0)
        if (
            not isinstance(reviewed_default_growth, int)
            or reviewed_default_growth < 0
        ):
            failures.append(
                f"{args.baseline}: limits.default_net_growth must be a "
                "nonnegative integer"
            )
            reviewed_default_growth = 0
        effective_global_growth = max(
            effective_global_growth, reviewed_default_growth
        )
        failures.extend(
            compare(
                metrics,
                baseline,
                effective_global_growth,
                check_unreachable=args.unreachable_allowlist is None,
            )
        )
    elif args.write_baseline is None:
        failures.append("pass --baseline or --write-baseline")

    if args.unreachable_allowlist is not None:
        try:
            allowlist = read_unreachable_allowlist(args.unreachable_allowlist)
            failures.extend(compare_unreachable_allowlist(metrics, allowlist))
        except (OSError, ValueError, json.JSONDecodeError) as error:
            failures.append(str(error))

    if args.duplicate_baseline is not None:
        if duplicate_groups is None:
            failures.append(
                "--duplicate-baseline requires --declarations-csv"
            )
        else:
            duplicate_baseline = read_json(args.duplicate_baseline)
            failures.extend(
                baseline_review_failures(
                    root, args.duplicate_baseline, duplicate_baseline
                )
            )
            failures.extend(
                compare_duplicate_groups(
                    duplicate_groups, duplicate_baseline
                )
            )

    for failure in failures:
        print(failure, file=sys.stderr)
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv[1:]))
