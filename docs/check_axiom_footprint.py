#!/usr/bin/env python3
"""Use Lean to verify transitive axiom disclosure for mapped Chapters 2--9.

Standard Lean axioms used by mathlib are reported but accepted.  `sorryAx` and
project-local axioms require the owning map item to be marked `partial`.
"""

from __future__ import annotations

import argparse
from collections import defaultdict
import json
from pathlib import Path
import re
import subprocess
import sys
import tempfile
from typing import Any

import audit_chapter


ROOT = Path(__file__).resolve().parents[1]
CHAPTERS = range(2, 10)
TRUSTED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MARKER_RE = re.compile(r"^AXIOM_AUDIT__[^\n]+$", re.MULTILINE)
AXIOMS_RE = re.compile(r"depends on axioms: \[(.*?)\]", re.DOTALL)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser()
    parser.add_argument(
        "--no-build",
        action="store_true",
        help="Do not run lake build Practice before the Lean environment audit.",
    )
    return parser.parse_args()


def mapped_declarations() -> list[dict[str, Any]]:
    index = audit_chapter.declaration_index(audit_chapter.lean_files(ROOT), ROOT)
    rows: list[dict[str, Any]] = []
    for chapter in CHAPTERS:
        map_data, map_path = audit_chapter.load_map(ROOT, chapter)
        if map_data is None:
            raise ValueError(f"missing {map_path.relative_to(ROOT)}")
        for item in map_data.get("items", []):
            preferred_value = item.get("leanFile", map_data.get("leanFile"))
            preferred_file = None
            if preferred_value:
                preferred_path = (map_path.parent / str(preferred_value)).resolve()
                preferred_file = str(preferred_path.relative_to(ROOT))
            for declaration in item.get("lean", []):
                candidates = audit_chapter.resolve_candidates(
                    str(declaration), chapter, index, preferred_file
                )
                if len(candidates) != 1:
                    raise ValueError(
                        f"{item.get('id')} -> {declaration} resolves to {len(candidates)} declarations"
                    )
                rows.append(
                    {
                        "chapter": chapter,
                        "id": item["id"],
                        "status": item.get("formalizationStatus", "complete"),
                        "qualified": candidates[0]["qualified"],
                    }
                )
    return rows


def lean_source(rows: list[dict[str, Any]]) -> tuple[str, dict[str, dict[str, Any]]]:
    lines = [
        "import Practice.DomainTheory",
        "",
        "set_option pp.universes false",
        "set_option pp.all false",
        "",
    ]
    metadata: dict[str, dict[str, Any]] = {}
    for index, row in enumerate(rows):
        marker = f"AXIOM_AUDIT__{row['chapter']}__{row['id']}__{index}"
        metadata[marker] = row
        lines.append(f'#eval IO.println "{marker}"')
        lines.append(f"#print axioms {row['qualified']}")
    return "\n".join(lines) + "\n", metadata


def parse_output(
    output: str, metadata: dict[str, dict[str, Any]]
) -> list[dict[str, Any]]:
    markers = list(MARKER_RE.finditer(output))
    rows: list[dict[str, Any]] = []
    for position, match in enumerate(markers):
        marker = match.group(0)
        end = markers[position + 1].start() if position + 1 < len(markers) else len(output)
        block = output[match.end() : end]
        axiom_match = AXIOMS_RE.search(block)
        axioms = []
        if axiom_match:
            axioms = [
                value.strip()
                for value in axiom_match.group(1).replace("\n", " ").split(",")
                if value.strip()
            ]
        rows.append(
            {
                **metadata[marker],
                "axioms": axioms,
                "projectAxioms": [axiom for axiom in axioms if axiom not in TRUSTED_AXIOMS],
            }
        )
    if len(rows) != len(metadata):
        raise ValueError(
            f"Lean emitted {len(rows)} audit markers for {len(metadata)} declarations"
        )
    return rows


def main() -> int:
    args = parse_args()
    if not args.no_build:
        build = subprocess.run(["lake", "build", "Practice"], cwd=ROOT, check=False)
        if build.returncode != 0:
            return build.returncode

    try:
        declarations = mapped_declarations()
        source, metadata = lean_source(declarations)
    except (OSError, json.JSONDecodeError, KeyError, ValueError) as exc:
        print(f"axiom audit setup failed: {exc}", file=sys.stderr)
        return 1

    with tempfile.TemporaryDirectory(prefix="domain-theory-axioms-") as directory:
        audit_path = Path(directory) / "AxiomAudit.lean"
        audit_path.write_text(source, encoding="utf-8")
        completed = subprocess.run(
            ["lake", "env", "lean", str(audit_path)],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
    if completed.returncode != 0:
        print(completed.stdout, file=sys.stderr)
        return completed.returncode

    try:
        results = parse_output(completed.stdout, metadata)
    except ValueError as exc:
        print(f"axiom audit parse failed: {exc}", file=sys.stderr)
        return 1

    untracked = [
        row
        for row in results
        if row["projectAxioms"] and row["status"] != "partial"
    ]
    by_chapter: dict[int, set[str]] = defaultdict(set)
    for row in results:
        if row["projectAxioms"]:
            by_chapter[row["chapter"]].add(row["id"])
    print(
        f"Axiom footprint: {len(results)} declarations; "
        f"{sum(bool(row['projectAxioms']) for row in results)} declarations and "
        f"{sum(len(ids) for ids in by_chapter.values())} items have disclosed project debt."
    )
    for chapter in CHAPTERS:
        print(f"Chapter {chapter}: {len(by_chapter[chapter])} item(s) with project debt.")
    if untracked:
        for row in untracked:
            print(
                f"error: {row['id']} ({row['qualified']}) has untracked axioms "
                f"{row['projectAxioms']} with status {row['status']!r}",
                file=sys.stderr,
            )
        return 1
    print("Axiom footprint disclosure check passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
