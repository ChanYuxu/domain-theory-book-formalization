#!/usr/bin/env python3
"""Audit one DomainTheory_Lean4_texbook chapter without modifying the repo."""

from __future__ import annotations

import argparse
from collections import defaultdict
import json
from pathlib import Path
import re
import subprocess
import sys
from typing import Any


DECL_RE = re.compile(
    r"^\s*(?:(?:private|protected|noncomputable)\s+)*"
    r"(def|theorem|lemma|axiom|structure|class|inductive|abbrev|instance)"
    r"\s+([^\s:{(\[]+)"
)
NAMESPACE_RE = re.compile(r"^\s*namespace\s+([^\s]+)")
SECTION_RE = re.compile(r"^\s*section(?:\s+[^\s]+)?\s*$")
END_RE = re.compile(r"^\s*end(?:\s+[^\s]+)?\s*$")
CHAPTER_PATH_RE = re.compile(r"(?:^|/)Chapter(\d{2})(?:\.lean|/)")
CHAPTER_NAMESPACE_RE = re.compile(r"^Chapter(\d+)$")
DEBT_RE = re.compile(r"\b(conjecture(?=_|\b)|sorry\b|admit\b|axiom\b|unsafe\b)")
REQUIRED_ITEM_FIELDS = {"id", "number", "kind", "title", "lean"}
EXPECTED_DEFAULT_DECL_KINDS = {
    "Definition": {"def", "structure", "class", "inductive", "abbrev"},
    "Proposition": {"theorem", "lemma", "axiom"},
    "Theorem": {"theorem", "lemma", "axiom"},
    "Lemma": {"theorem", "lemma", "axiom"},
    "Corollary": {"theorem", "lemma", "axiom"},
    "Conjecture": {"def", "abbrev"},
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Build, map-check, and proof-debt audit one book chapter."
    )
    parser.add_argument("chapter", type=int, help="Chapter number, for example 2")
    parser.add_argument("--repo", type=Path, help="Repository root override")
    parser.add_argument("--no-build", action="store_true", help="Skip lake build")
    parser.add_argument(
        "--no-review", action="store_true", help="Skip docs/check_chapterN_review.py"
    )
    parser.add_argument(
        "--strict",
        action="store_true",
        help="Fail when any local sorry/admit/axiom/unsafe token is found",
    )
    parser.add_argument("--json", action="store_true", help="Emit JSON")
    return parser.parse_args()


def repo_root(args: argparse.Namespace) -> Path:
    root = args.repo.resolve() if args.repo else Path(__file__).resolve().parents[1]
    required = [root / "lakefile.toml", root / "Practice" / "DomainTheory.lean"]
    missing = [str(path) for path in required if not path.is_file()]
    if missing:
        raise SystemExit(f"Not a DomainTheory Lean repo; missing: {', '.join(missing)}")
    return root


def run(command: list[str], cwd: Path) -> dict[str, Any]:
    completed = subprocess.run(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
        check=False,
    )
    return {
        "command": command,
        "returncode": completed.returncode,
        "output": completed.stdout.rstrip(),
    }


def warning_lines(output: str) -> list[str]:
    return [line for line in output.splitlines() if "warning:" in line.lower()]


def strip_comments_and_strings(source: str) -> str:
    """Replace Lean comments and string contents with spaces, preserving lines."""

    out: list[str] = []
    i = 0
    block_depth = 0
    in_string = False
    escaped = False
    while i < len(source):
        pair = source[i : i + 2]
        char = source[i]
        if block_depth:
            if pair == "/-":
                block_depth += 1
                out.extend("  ")
                i += 2
            elif pair == "-/":
                block_depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if char == "\n" else " ")
                i += 1
            continue
        if in_string:
            if char == "\n":
                out.append("\n")
            else:
                out.append(" ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
            i += 1
            continue
        if pair == "--":
            while i < len(source) and source[i] != "\n":
                out.append(" ")
                i += 1
            continue
        if pair == "/-":
            block_depth = 1
            out.extend("  ")
            i += 2
            continue
        if char == '"':
            in_string = True
            out.append(" ")
            i += 1
            continue
        out.append(char)
        i += 1
    return "".join(out)


def lean_files(root: Path) -> list[Path]:
    book_root = root / "Practice" / "DomainTheory"
    return sorted(
        path
        for path in book_root.rglob("*.lean")
        if "Papers" not in path.relative_to(book_root).parts
    )


def declaration_index(paths: list[Path], root: Path) -> dict[str, list[dict[str, Any]]]:
    index: dict[str, list[dict[str, Any]]] = defaultdict(list)
    for path in paths:
        source = path.read_text(encoding="utf-8")
        clean = strip_comments_and_strings(source)
        source_lines = source.splitlines()
        clean_lines = clean.splitlines()
        scopes: list[tuple[str, str]] = []
        declarations: list[dict[str, Any]] = []
        for line_number, line in enumerate(clean_lines, start=1):
            namespace_match = NAMESPACE_RE.match(line)
            if namespace_match:
                scopes.append(("namespace", namespace_match.group(1)))
                continue
            if SECTION_RE.match(line):
                scopes.append(("section", ""))
                continue
            if END_RE.match(line):
                if scopes:
                    scopes.pop()
                continue
            match = DECL_RE.match(line)
            if not match:
                continue
            declaration_kind = match.group(1)
            declared = match.group(2).rstrip(".{}")
            namespace = ".".join(
                name for kind, name in scopes if kind == "namespace" and name
            )
            qualified = (
                declared.removeprefix("_root_.")
                if declared.startswith("_root_.")
                else ".".join(part for part in (namespace, declared) if part)
            )
            location = {
                "name": declared,
                "kind": declaration_kind,
                "qualified": qualified,
                "file": str(path.relative_to(root)),
                "line": line_number,
            }
            declarations.append(location)

        for position, location in enumerate(declarations):
            start = location["line"]
            end = (
                declarations[position + 1]["line"] - 1
                if position + 1 < len(declarations)
                else len(clean_lines)
            )
            direct_debt: list[dict[str, Any]] = []
            for line_number in range(start, end + 1):
                line = clean_lines[line_number - 1]
                for match in DEBT_RE.finditer(line):
                    if match.group(1) == "conjecture" and not re.match(
                        r"^\s*(?:def|abbrev)\s+conjecture_", line
                    ):
                        continue
                    direct_debt.append(
                        {
                            "kind": match.group(1),
                            "line": line_number,
                            "source": source_lines[line_number - 1].strip(),
                        }
                    )
            location["endLine"] = end
            location["directDebt"] = direct_debt
            parts = location["qualified"].split(".")
            for start in range(len(parts)):
                index[".".join(parts[start:])].append(location)
    return index


def candidate_chapter(candidate: dict[str, Any]) -> int | None:
    path_match = CHAPTER_PATH_RE.search(candidate["file"])
    if path_match:
        return int(path_match.group(1))
    for part in candidate["qualified"].split("."):
        namespace_match = CHAPTER_NAMESPACE_RE.match(part)
        if namespace_match:
            return int(namespace_match.group(1))
    return None


def semantic_name_depth(candidate: dict[str, Any]) -> int:
    parts = candidate["qualified"].split(".")
    for index, part in enumerate(parts):
        if CHAPTER_NAMESPACE_RE.match(part):
            return len(parts) - index - 1
    return len(parts)


def resolve_candidates(
    name: str,
    chapter: int,
    index: dict[str, list[dict[str, Any]]],
    preferred_file: str | None,
) -> list[dict[str, Any]]:
    unique = {
        (candidate["file"], candidate["line"]): candidate
        for candidate in index.get(name, [])
    }
    candidates = [
        candidate
        for candidate in unique.values()
        if candidate_chapter(candidate) is None
        or candidate_chapter(candidate) <= chapter
    ]
    if not candidates:
        return []
    if preferred_file:
        preferred = [
            candidate for candidate in candidates if candidate["file"] == preferred_file
        ]
        if preferred:
            candidates = preferred

    requested_depth = len(name.split("."))

    def rank(candidate: dict[str, Any]) -> tuple[int, int, int]:
        declaration_exactness = 0 if candidate["name"] == name else 1
        depth_excess = max(0, semantic_name_depth(candidate) - requested_depth)
        owner = candidate_chapter(candidate)
        chapter_distance = 0 if owner == chapter else 1 if owner is None else chapter - owner + 1
        return declaration_exactness, depth_excess, chapter_distance

    best_rank = min(rank(candidate) for candidate in candidates)
    return sorted(
        (candidate for candidate in candidates if rank(candidate) == best_rank),
        key=lambda candidate: (candidate["file"], candidate["line"]),
    )


def load_map(root: Path, chapter: int) -> tuple[dict[str, Any] | None, Path]:
    path = root / "docs" / f"chapter{chapter}-map.json"
    if not path.is_file():
        return None, path
    return json.loads(path.read_text(encoding="utf-8")), path


def audit_review_ledger(
    root: Path,
    chapter: int,
    map_data: dict[str, Any] | None,
    skip_validation: bool,
) -> dict[str, Any]:
    path = root / "docs" / f"chapter{chapter}-review.json"
    expected_ids = {
        str(item.get("id", ""))
        for item in (map_data or {}).get("items", [])
        if isinstance(item, dict)
        and item.get("formalizationStatus") in {"partial", "conjecture"}
    }
    map_ids = {
        str(item.get("id", ""))
        for item in (map_data or {}).get("items", [])
        if isinstance(item, dict)
    }
    report: dict[str, Any] = {
        "path": str(path),
        "present": path.is_file(),
        "items": 0,
        "expected_status_items": len(expected_ids),
        "missing_status_items": sorted(expected_ids),
        "unknown_items": [],
        "parse_error": "",
        "validation": {
            "skipped": skip_validation,
            "command": [],
        },
    }
    if not path.is_file():
        return report
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
    except json.JSONDecodeError as exc:
        report["parse_error"] = str(exc)
        return report
    ledger_items = data.get("items", {}) if isinstance(data, dict) else {}
    if not isinstance(ledger_items, dict):
        report["parse_error"] = "items must be an object"
        return report
    ledger_ids = set(ledger_items)
    report["items"] = len(ledger_ids)
    report["missing_status_items"] = sorted(expected_ids - ledger_ids)
    report["unknown_items"] = sorted(ledger_ids - map_ids)

    validator = root / "docs" / "validate_workflow_state.py"
    command = [sys.executable, str(validator.relative_to(root)), str(path.relative_to(root))]
    report["validation"]["command"] = command
    if not skip_validation:
        report["validation"].update(run(command, root))
    return report


def audit_map(
    data: dict[str, Any] | None,
    path: Path,
    index: dict[str, list[dict[str, Any]]],
    chapter: int,
) -> tuple[dict[str, Any], set[str]]:
    if data is None:
        return {
            "path": str(path),
            "present": False,
            "items": 0,
            "duplicate_ids": [],
            "duplicate_numbers": [],
            "invalid_items": [],
            "missing_declarations": [],
            "ambiguous_declarations": [],
            "default_kind_mismatches": [],
            "partial_items": [],
            "direct_debt_items": [],
            "untracked_debt_items": [],
        }, set()

    items = data.get("items", [])
    ids: dict[str, int] = defaultdict(int)
    numbers: dict[str, int] = defaultdict(int)
    invalid: list[dict[str, Any]] = []
    missing: list[dict[str, str]] = []
    ambiguous: list[dict[str, Any]] = []
    default_kind_mismatches: list[dict[str, str]] = []
    partial_items: list[dict[str, str]] = []
    direct_debt_items: list[dict[str, Any]] = []
    untracked_debt_items: list[dict[str, Any]] = []
    files_for_items: set[str] = set()

    for position, item in enumerate(items):
        if not isinstance(item, dict):
            invalid.append({"position": position, "reason": "item is not an object"})
            continue
        item_id = str(item.get("id", ""))
        number = str(item.get("number", ""))
        ids[item_id] += 1
        numbers[number] += 1
        if item.get("formalizationStatus") == "partial":
            partial_items.append(
                {
                    "id": item_id,
                    "number": number,
                    "note": str(item.get("reviewNote", "")),
                }
            )
        missing_fields = sorted(REQUIRED_ITEM_FIELDS - set(item))
        lean_names = item.get("lean")
        if missing_fields or not isinstance(lean_names, list) or not lean_names:
            invalid.append(
                {
                    "position": position,
                    "id": item_id,
                    "missing_fields": missing_fields,
                    "reason": "lean must be a non-empty list",
                }
            )
            continue
        item_direct_debt: list[dict[str, Any]] = []
        lean_file_value = item.get("leanFile", data.get("leanFile"))
        preferred_file: str | None = None
        if lean_file_value:
            candidate_path = (path.parent / str(lean_file_value)).resolve()
            try:
                preferred_file = str(candidate_path.relative_to(path.parent.parent))
            except ValueError:
                preferred_file = None
        for lean_position, name_value in enumerate(lean_names):
            name = str(name_value)
            candidates = resolve_candidates(name, chapter, index, preferred_file)
            if not candidates:
                missing.append({"id": item_id, "name": name})
                continue
            files_for_items.update(candidate["file"] for candidate in candidates)
            if len(candidates) > 1:
                ambiguous.append(
                    {"id": item_id, "name": name, "candidates": candidates}
                )
            for candidate in candidates:
                item_direct_debt.extend(
                    {
                        "declaration": candidate["qualified"],
                        "file": candidate["file"],
                        **entry,
                    }
                    for entry in candidate.get("directDebt", [])
                )
            if lean_position == 0 and len(candidates) == 1:
                actual_kind = candidates[0]["kind"]
                expected_kinds = EXPECTED_DEFAULT_DECL_KINDS.get(str(item.get("kind", "")))
                if expected_kinds is not None and actual_kind not in expected_kinds:
                    default_kind_mismatches.append(
                        {
                            "id": item_id,
                            "item_kind": str(item.get("kind", "")),
                            "name": name,
                            "declaration_kind": actual_kind,
                        }
                    )

        if item_direct_debt:
            debt_entry = {
                "id": item_id,
                "number": number,
                "occurrences": item_direct_debt,
            }
            direct_debt_items.append(debt_entry)
            debt_kinds = {entry["kind"] for entry in item_direct_debt}
            status = item.get("formalizationStatus")
            tracked = status == "partial" or (
                status == "conjecture" and debt_kinds == {"conjecture"}
            )
            if not tracked:
                untracked_debt_items.append(debt_entry)

    return {
        "path": str(path),
        "present": True,
        "items": len(items),
        "duplicate_ids": sorted(key for key, count in ids.items() if key and count > 1),
        "duplicate_numbers": sorted(
            key for key, count in numbers.items() if key and count > 1
        ),
        "invalid_items": invalid,
        "missing_declarations": missing,
        "ambiguous_declarations": ambiguous,
        "default_kind_mismatches": default_kind_mismatches,
        "partial_items": partial_items,
        "direct_debt_items": direct_debt_items,
        "untracked_debt_items": untracked_debt_items,
    }, files_for_items


def chapter_scope_files(
    root: Path, chapter: int, mapped_files: set[str]
) -> list[Path]:
    padded = f"{chapter:02d}"
    candidates: set[Path] = set()
    wrapper = root / "Practice" / "DomainTheory" / f"Chapter{padded}.lean"
    if wrapper.is_file():
        candidates.add(wrapper)
    chapter_dir = root / "Practice" / "DomainTheory" / f"Chapter{padded}"
    if chapter_dir.is_dir():
        candidates.update(chapter_dir.rglob("*.lean"))
    for relative in mapped_files:
        path = root / relative
        if path.is_file():
            candidates.add(path)
    return sorted(candidates)


def audit_debt(paths: list[Path], root: Path) -> list[dict[str, Any]]:
    debt: list[dict[str, Any]] = []
    for path in paths:
        source = path.read_text(encoding="utf-8")
        clean = strip_comments_and_strings(source)
        source_lines = source.splitlines()
        for line_number, line in enumerate(clean.splitlines(), start=1):
            for match in DEBT_RE.finditer(line):
                if match.group(1) == "conjecture" and not re.match(
                    r"^\s*(?:def|abbrev)\s+conjecture_", line
                ):
                    continue
                debt.append(
                    {
                        "kind": match.group(1),
                        "file": str(path.relative_to(root)),
                        "line": line_number,
                        "source": source_lines[line_number - 1].strip(),
                    }
                )
    return debt


def format_command(command: list[str]) -> str:
    return " ".join(command)


def print_text(report: dict[str, Any]) -> None:
    print(f"Chapter {report['chapter']} audit")
    print(f"repo: {report['repo']}")
    print(f"target: {report['target']}")

    build = report["build"]
    if build["skipped"]:
        print("build: SKIPPED")
    else:
        if build["returncode"] != 0:
            build_label = "FAIL"
        elif build["warnings"]:
            build_label = f"PASS WITH {len(build['warnings'])} WARNING(S)"
        else:
            build_label = "PASS"
        print(f"build: {build_label}")
        for warning in build["warnings"]:
            print(f"  {warning}")
        if build["returncode"] != 0 and build["output"]:
            print(build["output"])

    mapping = report["map"]
    if not mapping["present"]:
        print(f"map: MISSING ({mapping['path']})")
    else:
        print(
            "map: "
            f"{mapping['items']} items, "
            f"{len(mapping['missing_declarations'])} unresolved declarations, "
            f"{len(mapping['ambiguous_declarations'])} ambiguous declarations, "
            f"{len(mapping['default_kind_mismatches'])} default-kind mismatches, "
            f"{len(mapping['partial_items'])} tracked partial item(s), "
            f"{len(mapping['untracked_debt_items'])} untracked direct-debt item(s)"
        )
        for entry in mapping["missing_declarations"]:
            print(f"  unresolved: {entry['id']} -> {entry['name']}")
        for entry in mapping["ambiguous_declarations"]:
            locations = ", ".join(
                f"{candidate['file']}:{candidate['line']}"
                for candidate in entry["candidates"]
            )
            print(f"  ambiguous: {entry['id']} -> {entry['name']} ({locations})")
        for entry in mapping["default_kind_mismatches"]:
            print(
                "  default-kind mismatch: "
                f"{entry['id']} ({entry['item_kind']}) -> "
                f"{entry['name']} ({entry['declaration_kind']})"
            )
        for entry in mapping["partial_items"]:
            print(f"  partial: {entry['id']} ({entry['number']}) {entry['note']}")
        for entry in mapping["untracked_debt_items"]:
            occurrences = ", ".join(
                f"{debt['kind']} at {debt['file']}:{debt['line']}"
                for debt in entry["occurrences"]
            )
            print(
                f"  untracked direct debt: {entry['id']} "
                f"({entry['number']}) {occurrences}"
            )

    debt = report["proof_debt"]
    print(f"proof debt: {len(debt)} lexical code occurrence(s)")
    for entry in debt:
        print(f"  {entry['kind']}: {entry['file']}:{entry['line']} {entry['source']}")

    review = report["review"]
    if review["skipped"]:
        print("TeX review check: SKIPPED")
    elif not review["present"]:
        print("TeX review check: NOT AVAILABLE")
    else:
        print(f"TeX review check: {'PASS' if review['returncode'] == 0 else 'FAIL'}")
        if review["output"]:
            print(review["output"])

    ledger = report["review_ledger"]
    if not ledger["present"]:
        print(
            "workflow review ledger: MISSING "
            f"({len(ledger['missing_status_items'])} status item(s) uncovered)"
        )
    else:
        validation = ledger["validation"]
        if validation["skipped"]:
            validation_label = "VALIDATION SKIPPED"
        else:
            validation_label = "PASS" if validation.get("returncode") == 0 else "FAIL"
        print(
            "workflow review ledger: "
            f"{ledger['items']} item(s), "
            f"{len(ledger['missing_status_items'])} status item(s) uncovered, "
            f"{len(ledger['unknown_items'])} unknown item(s), "
            f"{validation_label}"
        )
        for item_id in ledger["missing_status_items"]:
            print(f"  missing ledger item: {item_id}")
        for item_id in ledger["unknown_items"]:
            print(f"  unknown ledger item: {item_id}")
        if ledger["parse_error"]:
            print(f"  ledger parse error: {ledger['parse_error']}")
        if not validation["skipped"] and validation.get("returncode") != 0:
            print(validation.get("output", ""))

    generated = report["generated"]
    state = "READY" if generated["marked_pdf"] and generated["extract_json"] else "MISSING"
    print(f"generated reader inputs: {state}")
    print(f"result: {'PASS' if report['ok'] else 'FAIL'}")


def main() -> int:
    args = parse_args()
    if args.chapter < 1 or args.chapter > 99:
        raise SystemExit("chapter must be between 1 and 99")
    root = repo_root(args)
    padded = f"{args.chapter:02d}"
    numbered_items = root / "Practice" / "DomainTheory" / f"Chapter{padded}" / "NumberedItems.lean"
    target = (
        f"Practice.DomainTheory.Chapter{padded}.NumberedItems"
        if numbered_items.is_file()
        else f"Practice.DomainTheory.Chapter{padded}"
    )

    all_lean_files = lean_files(root)
    index = declaration_index(all_lean_files, root)
    map_data, map_path = load_map(root, args.chapter)
    map_report, mapped_files = audit_map(map_data, map_path, index, args.chapter)
    review_ledger = audit_review_ledger(root, args.chapter, map_data, args.no_review)
    scope_files = chapter_scope_files(root, args.chapter, mapped_files)
    debt = audit_debt(scope_files, root)

    build = {
        "skipped": args.no_build,
        "command": ["lake", "build", target],
        "warnings": [],
    }
    if not args.no_build:
        build.update(run(["lake", "build", target], root))
        build["warnings"] = warning_lines(build["output"])

    review_path = root / "docs" / f"check_chapter{args.chapter}_review.py"
    review: dict[str, Any] = {
        "skipped": args.no_review,
        "present": review_path.is_file(),
        "command": [sys.executable, str(review_path.relative_to(root))],
    }
    if not args.no_review and review_path.is_file():
        review.update(run(review["command"], root))

    generated_dir = root / "docs" / "generated"
    generated = {
        "marked_pdf": (generated_dir / f"chapter{args.chapter}-marked.pdf").is_file(),
        "extract_json": (generated_dir / f"chapter{args.chapter}-extract.json").is_file(),
    }

    structural_failures = bool(
        map_report["duplicate_ids"]
        or map_report["invalid_items"]
        or map_report["missing_declarations"]
        or map_report["ambiguous_declarations"]
        or map_report["default_kind_mismatches"]
        or map_report["untracked_debt_items"]
        or review_ledger["missing_status_items"]
        or review_ledger["unknown_items"]
        or review_ledger["parse_error"]
    )
    build_failed = not args.no_build and build.get("returncode") != 0
    review_failed = (
        not args.no_review
        and review["present"]
        and review.get("returncode") != 0
    )
    ledger_validation_failed = (
        not args.no_review
        and review_ledger["present"]
        and review_ledger["validation"].get("returncode") != 0
    )
    strict_failed = args.strict and bool(debt)
    ok = not (
        structural_failures
        or build_failed
        or review_failed
        or ledger_validation_failed
        or strict_failed
    )

    report = {
        "chapter": args.chapter,
        "repo": str(root),
        "target": target,
        "scope_files": [str(path.relative_to(root)) for path in scope_files],
        "map": map_report,
        "proof_debt": debt,
        "build": build,
        "review": review,
        "review_ledger": review_ledger,
        "generated": generated,
        "strict": args.strict,
        "ok": ok,
    }

    if args.json:
        print(json.dumps(report, indent=2, ensure_ascii=False))
    else:
        print_text(report)
        if build.get("output") and build.get("returncode") == 0:
            print(f"build command: {format_command(build['command'])}")
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
