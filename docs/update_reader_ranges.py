#!/usr/bin/env python3
"""Refresh fallback Lean file/range data from the reader's declaration resolver."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

from serve_chapter2 import ROOT, locate_item


def update_chapter(chapter: int) -> None:
    path = ROOT / "docs" / f"chapter{chapter}-map.json"
    data = json.loads(path.read_text(encoding="utf-8"))
    for item in data["items"]:
        canonical = item["lean"][0]
        resolved = locate_item(item["id"], canonical)
        item["leanFile"] = "../" + resolved["file"]
        item["startLine"] = resolved["startLine"]
        item["endLine"] = resolved["endLine"]
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(f"Updated {len(data['items'])} Chapter {chapter} fallback ranges")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("chapters", type=int, nargs="+", choices=tuple(range(2, 8)))
    args = parser.parse_args()
    for chapter in args.chapters:
        update_chapter(chapter)


if __name__ == "__main__":
    main()
