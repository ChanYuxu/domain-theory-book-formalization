#!/usr/bin/env python3
"""Validate that the GitHub Pages artifact is complete and public-safe."""

from __future__ import annotations

import argparse
import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs"
DEFAULT_SITE = ROOT / "_site"
CHAPTERS = range(2, 10)
TEXT_SUFFIXES = {".html", ".css", ".js", ".json", ".tex", ".md", ".txt"}
FORBIDDEN_PATH_PARTS = {"generated", "tmp", "Papers", "skills"}
FORBIDDEN_TEXT = [
    re.compile(r"/(?:Users|home)/", re.IGNORECASE),
    re.compile(r"BEGIN (?:RSA |OPENSSH |EC )?PRIVATE KEY"),
    re.compile(r"Practice/DomainTheory/Papers"),
    re.compile(r"chapter\d+-extract\.json"),
]


def load_json(path: Path) -> dict:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def fail(message: str) -> None:
    raise SystemExit(f"Public release check failed: {message}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("site", nargs="?", type=Path, default=DEFAULT_SITE)
    args = parser.parse_args()
    site = args.site.expanduser().resolve()
    if not site.is_dir():
        fail(f"site directory does not exist: {site}")

    manifest = load_json(site / "data" / "manifest.json")
    manifest_chapters = {entry["number"]: entry for entry in manifest.get("chapters", [])}
    if set(manifest_chapters) != set(CHAPTERS):
        fail(f"manifest chapters are {sorted(manifest_chapters)}")

    pdfjs = site / "vendor" / "pdfjs"
    for asset in ("pdf.mjs", "pdf.worker.mjs", "LICENSE"):
        if not (pdfjs / asset).is_file():
            fail(f"PDF.js asset is missing: vendor/pdfjs/{asset}")
    if "Apache License" not in (pdfjs / "LICENSE").read_text(encoding="utf-8"):
        fail("PDF.js license notice is invalid")

    total_items = 0
    for chapter in CHAPTERS:
        chapter_data = load_json(site / "data" / f"chapter{chapter}.json")
        map_data = load_json(DOCS / f"chapter{chapter}-map.json")
        items = chapter_data.get("items", [])
        if len(items) != len(map_data["items"]):
            fail(f"Chapter {chapter} item count does not match its map")
        if any(not item.get("declarations") for item in items):
            fail(f"Chapter {chapter} contains an item without Lean declarations")
        item_ids = [item["id"] for item in items]
        if len(item_ids) != len(set(item_ids)):
            fail(f"Chapter {chapter} contains duplicate item ids")
        total_items += len(items)

        tex = site / "companion" / f"chapter{chapter}-companion.tex"
        pdf = site / "companion" / f"chapter{chapter}-companion.pdf"
        if not tex.is_file() or not pdf.is_file() or pdf.stat().st_size < 10_000:
            fail(f"Chapter {chapter} companion TeX/PDF is missing or empty")
        marker_ids = re.findall(r"\\leanmarker\{([^}]+)\}", tex.read_text(encoding="ascii"))
        if marker_ids != item_ids:
            fail(f"Chapter {chapter} TeX markers do not match map order")

    for path in site.rglob("*"):
        if path.is_symlink():
            fail(f"symbolic link is not allowed: {path.relative_to(site)}")
        if not path.is_file():
            continue
        relative = path.relative_to(site)
        if any(part in FORBIDDEN_PATH_PARTS for part in relative.parts):
            fail(f"forbidden path in site artifact: {relative}")
        if path.suffix.lower() not in TEXT_SUFFIXES:
            continue
        text = path.read_text(encoding="utf-8", errors="replace")
        for pattern in FORBIDDEN_TEXT:
            if pattern.search(text):
                fail(f"forbidden text pattern {pattern.pattern!r} in {relative}")

    print(f"Public release check passed: Chapters 2-9, {total_items} mapped items")


if __name__ == "__main__":
    main()
