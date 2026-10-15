#!/usr/bin/env python3
"""Export source-page locators without publishing extracted textbook text.

The local chapter extracts contain OCR text and absolute source paths, so they
must stay ignored.  This script retains only the stable item id, one-based PDF
page, and source block id needed to order the public TeX companion.
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs"
DEFAULT_OUTPUT = DOCS / "public" / "source-locators.json"
CHAPTERS = range(2, 10)


def load_json(path: Path) -> dict:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def chapter_locators(chapter: int) -> dict:
    chapter_map = load_json(DOCS / f"chapter{chapter}-map.json")
    extract = load_json(DOCS / "generated" / f"chapter{chapter}-extract.json")
    expected = {item["id"] for item in chapter_map["items"]}
    locators: dict[str, dict] = {}

    for page in extract["pages"]:
        pdf_page = int(page["pdfPage"])
        for block in page["blocks"]:
            marker = block.get("marker")
            if not marker:
                continue
            item_id = marker["id"]
            if item_id in locators:
                raise SystemExit(f"Duplicate marker in Chapter {chapter}: {item_id}")
            locators[item_id] = {
                "pdfPage": pdf_page,
                "block": block["id"],
            }

    missing = sorted(expected - set(locators))
    unknown = sorted(set(locators) - expected)
    if missing or unknown:
        raise SystemExit(
            f"Chapter {chapter} locator mismatch; missing={missing}, unknown={unknown}"
        )

    return {
        "sourcePdfPages": extract["pdfPages"],
        "items": locators,
    }


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()

    payload = {
        "schemaVersion": 1,
        "source": {
            "title": "Domain Theory",
            "authors": ["Samson Abramsky", "Achim Jung"],
            "edition": "Corrected and expanded version",
            "pageNumbering": "one-based PDF pages",
            "notice": "Locators only; no source PDF path or extracted prose is included.",
        },
        "chapters": {
            str(chapter): chapter_locators(chapter) for chapter in CHAPTERS
        },
    }

    output = args.output.expanduser().resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    output.write_text(
        json.dumps(payload, ensure_ascii=True, indent=2) + "\n",
        encoding="utf-8",
    )
    print(f"Wrote {output.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
