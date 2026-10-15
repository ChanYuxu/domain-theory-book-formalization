#!/usr/bin/env python3
"""Check Chapter 2--9 maps, proof debt, and review-ledger consistency.

This check deliberately does not fail merely because disclosed proof debt
exists.  It fails when debt is hidden, misclassified, unmapped, or absent from
the persistent review ledger.
"""

from __future__ import annotations

import json
from pathlib import Path
import re
import sys
from typing import Any

import audit_chapter
from serve_chapter2 import locate_item
import validate_workflow_state


ROOT = Path(__file__).resolve().parents[1]
CHAPTERS = range(2, 10)
ALLOWED_STATUSES = {None, "complete", "proved", "partial", "conjecture"}
SHA256_RE = re.compile(r"^[0-9a-f]{64}$")
BARE_TRUE_ASSIGNMENT_RE = re.compile(r":=\s*True\b")


def preferred_file(map_path: Path, map_data: dict[str, Any], item: dict[str, Any]) -> str | None:
    value = item.get("leanFile", map_data.get("leanFile"))
    if not value:
        return None
    candidate = (map_path.parent / str(value)).resolve()
    try:
        return str(candidate.relative_to(ROOT))
    except ValueError:
        return None


def resolve_item_locations(
    chapter: int,
    map_path: Path,
    map_data: dict[str, Any],
    index: dict[str, list[dict[str, Any]]],
) -> tuple[dict[str, list[dict[str, Any]]], set[tuple[str, int]]]:
    resolved: dict[str, list[dict[str, Any]]] = {}
    locations: set[tuple[str, int]] = set()
    for item in map_data.get("items", []):
        item_locations: list[dict[str, Any]] = []
        preferred = preferred_file(map_path, map_data, item)
        for name in item.get("lean", []):
            candidates = audit_chapter.resolve_candidates(str(name), chapter, index, preferred)
            item_locations.extend(candidates)
            locations.update((candidate["file"], candidate["line"]) for candidate in candidates)
        resolved[str(item.get("id", ""))] = item_locations
    return resolved, locations


def fallback_range_errors(
    chapter: int,
    map_path: Path,
    map_data: dict[str, Any],
    index: dict[str, list[dict[str, Any]]],
) -> list[str]:
    """Require one declaration-specific static fallback for every mapped name."""
    errors: list[str] = []
    for item in map_data.get("items", []):
        item_id = str(item.get("id", ""))
        names = [str(name) for name in item.get("lean", [])]
        fallbacks = item.get("fallbackDeclarations")
        if not isinstance(fallbacks, list):
            errors.append(f"{item_id}: fallbackDeclarations must be a list")
            continue
        fallback_names = [
            str(entry.get("declaration", "")) if isinstance(entry, dict) else ""
            for entry in fallbacks
        ]
        if fallback_names != names:
            errors.append(
                f"{item_id}: fallback declaration order {fallback_names!r} != {names!r}"
            )
            continue
        for entry in fallbacks:
            if not isinstance(entry, dict):
                continue
            name = str(entry.get("declaration", ""))
            source_value = entry.get("leanFile")
            if not source_value:
                errors.append(f"{item_id}/{name}: leanFile is required")
                continue
            source_path = (map_path.parent / str(source_value)).resolve()
            try:
                source_file = str(source_path.relative_to(ROOT))
            except ValueError:
                errors.append(f"{item_id}/{name}: leanFile escapes the repository")
                continue
            start = entry.get("startLine")
            end = entry.get("endLine")
            if not isinstance(start, int) or not isinstance(end, int) or start < 1 or end < start:
                errors.append(f"{item_id}/{name}: invalid fallback line range {start!r}-{end!r}")
                continue
            candidates = audit_chapter.resolve_candidates(name, chapter, index, source_file)
            if len(candidates) != 1:
                errors.append(
                    f"{item_id}/{name}: expected one declaration in {source_file}, got {len(candidates)}"
                )
                continue
            candidate = candidates[0]
            if candidate["file"] != source_file:
                errors.append(
                    f"{item_id}/{name}: fallback file {source_file} != {candidate['file']}"
                )
            if not (start <= candidate["line"] <= end):
                errors.append(
                    f"{item_id}/{name}: fallback {start}-{end} does not cover "
                    f"declaration line {candidate['line']}"
                )
            resolved = locate_item(item_id, name)
            expected = {
                "declaration": name,
                "leanFile": "../" + resolved["file"],
                "startLine": resolved["startLine"],
                "endLine": resolved["endLine"],
            }
            if entry != expected:
                errors.append(
                    f"{item_id}/{name}: fallback range is stale; "
                    "run docs/update_reader_ranges.py"
                )
        if fallbacks:
            first = fallbacks[0]
            for field in ("leanFile", "startLine", "endLine"):
                if item.get(field) != first.get(field):
                    errors.append(
                        f"{item_id}: canonical {field} must match the first fallback declaration"
                    )
    return errors


def unique_declarations(index: dict[str, list[dict[str, Any]]]) -> list[dict[str, Any]]:
    declarations: dict[tuple[str, int], dict[str, Any]] = {}
    for candidates in index.values():
        for candidate in candidates:
            declarations[(candidate["file"], candidate["line"])] = candidate
    return list(declarations.values())


def bare_true_assignment_errors() -> list[str]:
    """Reject truth-valued record fillers that conceal an unencoded interface."""
    errors: list[str] = []
    for path in audit_chapter.lean_files(ROOT):
        match = re.search(r"Chapter0?([2-7])(?:\D|$)", str(path))
        if not match:
            continue
        for line_number, line in enumerate(path.read_text(encoding="utf-8").splitlines(), 1):
            if BARE_TRUE_ASSIGNMENT_RE.search(line):
                errors.append(
                    f"bare `:= True` semantic placeholder at "
                    f"{path.relative_to(ROOT)}:{line_number}"
                )
    return errors


def boundary_matches_direct_debt(
    item_id: str,
    kinds: set[str],
    ledger_item: dict[str, Any],
    errors: list[str],
) -> None:
    boundary = ledger_item.get("proofBoundary", {})
    boundary_kind = boundary.get("kind")
    if "unsafe" in kinds:
        errors.append(f"{item_id}: unsafe declaration is not an allowed proof boundary")
    expected = kinds - {"unsafe"}
    if expected and boundary_kind not in expected:
        errors.append(
            f"{item_id}: direct Lean debt {sorted(expected)} disagrees with ledger boundary {boundary_kind!r}"
        )
    cycle = ledger_item.get("currentRevisionCycle", {})
    if "sorry" in kinds and boundary.get("reason") == "automation_exhausted":
        if cycle.get("attemptsUsed", 0) < 10:
            errors.append(f"{item_id}: automation_exhausted sorry requires ten recorded attempts")


def chapter_check(
    chapter: int,
    index: dict[str, list[dict[str, Any]]],
    declarations: list[dict[str, Any]],
) -> tuple[list[str], dict[str, int]]:
    errors: list[str] = []
    map_data, map_path = audit_chapter.load_map(ROOT, chapter)
    if map_data is None:
        return [f"chapter {chapter}: missing {map_path.relative_to(ROOT)}"], {}
    map_report, mapped_files = audit_chapter.audit_map(
        map_data, map_path, index, chapter
    )
    for key in (
        "duplicate_ids",
        "duplicate_numbers",
        "invalid_items",
        "missing_declarations",
        "ambiguous_declarations",
        "default_kind_mismatches",
        "untracked_debt_items",
    ):
        if map_report[key]:
            errors.append(f"chapter {chapter}: map {key}: {map_report[key]}")
    errors.extend(
        f"chapter {chapter}: fallback {error}"
        for error in fallback_range_errors(chapter, map_path, map_data, index)
    )

    review_path = ROOT / "docs" / f"chapter{chapter}-review.json"
    try:
        review_data = json.loads(review_path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        return [*errors, f"chapter {chapter}: invalid review ledger: {exc}"], {}
    review_errors = validate_workflow_state.validate_review(review_path, review_data)
    errors.extend(f"chapter {chapter}: ledger {error}" for error in review_errors)

    map_items = map_data.get("items", [])
    by_id = {str(item.get("id", "")): item for item in map_items}
    ledger_items = review_data.get("items", {})
    status_ids = {
        item_id
        for item_id, item in by_id.items()
        if item.get("formalizationStatus") in {"partial", "conjecture"}
    }
    missing_ledger = status_ids - set(ledger_items)
    unknown_ledger = set(ledger_items) - set(by_id)
    if missing_ledger:
        errors.append(f"chapter {chapter}: status items missing from ledger: {sorted(missing_ledger)}")
    if unknown_ledger:
        errors.append(f"chapter {chapter}: ledger IDs absent from map: {sorted(unknown_ledger)}")

    source_version = review_data.get("sourceVersion", {})
    if not SHA256_RE.fullmatch(str(source_version.get("pdfSha256", ""))):
        errors.append(f"chapter {chapter}: sourceVersion.pdfSha256 is not a SHA-256 digest")
    for item_id, item in by_id.items():
        status = item.get("formalizationStatus")
        if status not in ALLOWED_STATUSES:
            errors.append(f"chapter {chapter}: {item_id} has invalid formalizationStatus {status!r}")
        if status in {"partial", "conjecture"} and not str(item.get("reviewNote", "")).strip():
            errors.append(f"chapter {chapter}: {item_id} needs a nonempty reviewNote")
        ledger_item = ledger_items.get(item_id)
        if not isinstance(ledger_item, dict):
            continue
        if ledger_item.get("number") != item.get("number"):
            errors.append(f"chapter {chapter}: {item_id} number differs between map and ledger")
        canonical = str(ledger_item.get("lean", {}).get("canonical", ""))
        if canonical and not any(
            canonical == str(name) or canonical.endswith("." + str(name))
            for name in item.get("lean", [])
        ):
            errors.append(f"chapter {chapter}: {item_id} canonical declaration is not in its map entry")
        if ledger_item.get("proofBoundary", {}).get("kind") == "conjecture" and status != "conjecture":
            errors.append(f"chapter {chapter}: {item_id} conjecture boundary must use conjecture map status")
    direct_by_id: dict[str, set[str]] = {}
    for entry in map_report["direct_debt_items"]:
        item_id = entry["id"]
        kinds = {occurrence["kind"] for occurrence in entry["occurrences"]}
        direct_by_id[item_id] = kinds
        ledger_item = ledger_items.get(item_id)
        if not isinstance(ledger_item, dict):
            errors.append(f"chapter {chapter}: directly indebted {item_id} has no ledger record")
            continue
        boundary_matches_direct_debt(item_id, kinds, ledger_item, errors)

    resolved, mapped_locations = resolve_item_locations(chapter, map_path, map_data, index)
    for item_id, locations in resolved.items():
        ledger_item = ledger_items.get(item_id)
        if not isinstance(ledger_item, dict) or not locations:
            continue
        canonical = str(ledger_item.get("lean", {}).get("canonical", ""))
        canonical_locations = [
            location
            for location in locations
            if canonical == location["qualified"]
            or canonical.endswith("." + location["name"])
        ]
        if canonical_locations:
            actual_module = ".".join(
                Path(canonical_locations[0]["file"]).with_suffix("").parts
            )
            ledger_module = ledger_item.get("lean", {}).get("module")
            if ledger_module != actual_module:
                errors.append(
                    f"chapter {chapter}: {item_id} ledger module {ledger_module!r} != {actual_module!r}"
                )

    scope = {
        str(path.relative_to(ROOT))
        for path in audit_chapter.chapter_scope_files(ROOT, chapter, mapped_files)
    }
    serialized_ledger = json.dumps(review_data, ensure_ascii=False)
    support_debt = 0
    for declaration in declarations:
        if declaration["file"] not in scope or not declaration.get("directDebt"):
            continue
        location = (declaration["file"], declaration["line"])
        if location in mapped_locations:
            continue
        name = declaration["name"]
        qualified = declaration["qualified"]
        if name not in serialized_ledger and qualified not in serialized_ledger:
            errors.append(
                f"chapter {chapter}: helper debt {qualified} at "
                f"{declaration['file']}:{declaration['line']} is not linked from the review ledger"
            )
        else:
            support_debt += 1

    counts = {
        "items": len(map_items),
        "status": len(status_ids),
        "directDebt": len(direct_by_id),
        "supportDebt": support_debt,
        "ledger": len(ledger_items),
    }
    return errors, counts


def main() -> int:
    index = audit_chapter.declaration_index(audit_chapter.lean_files(ROOT), ROOT)
    declarations = unique_declarations(index)
    failures: list[str] = []
    failures.extend(bare_true_assignment_errors())
    for chapter in CHAPTERS:
        errors, counts = chapter_check(chapter, index, declarations)
        if counts:
            print(
                f"Chapter {chapter}: {counts['items']} items, {counts['status']} tracked status items, "
                f"{counts['directDebt']} direct-debt items, {counts['supportDebt']} linked helper-debt declarations, "
                f"{counts['ledger']} ledger records."
            )
        failures.extend(errors)
    source_versions = {
        (
            data.get("sourceVersion", {}).get("id"),
            data.get("sourceVersion", {}).get("pdfSha256"),
        )
        for chapter in CHAPTERS
        for data in [
            json.loads((ROOT / "docs" / f"chapter{chapter}-review.json").read_text(encoding="utf-8"))
        ]
    }
    if len(source_versions) != 1:
        failures.append(f"chapters do not share one source version: {sorted(source_versions)}")
    if failures:
        for failure in failures:
            print(f"error: {failure}", file=sys.stderr)
        return 1
    print("Formalization metadata check passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
