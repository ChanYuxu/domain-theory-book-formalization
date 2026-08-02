#!/usr/bin/env python3
"""Report Chapter 6 TeX review coverage.

The public repository stores paraphrase metadata in `chapter6-map.json` and
human-reviewed TeX snippets in `chapter6-tex-overrides.json`.  This script keeps
the review process auditable without storing the source PDF text.
"""

from __future__ import annotations

import json
from pathlib import Path


DOCS = Path(__file__).resolve().parent
MAP_PATH = DOCS / "chapter6-map.json"
OVERRIDES_PATH = DOCS / "chapter6-tex-overrides.json"
GENERATED_EXTRACT_PATH = DOCS / "generated" / "chapter6-extract.json"


def main() -> None:
    map_data = json.loads(MAP_PATH.read_text(encoding="utf-8"))
    overrides = json.loads(OVERRIDES_PATH.read_text(encoding="utf-8"))
    reviewed = {
        item_id
        for item_id, entry in overrides.get("items", {}).items()
        if entry.get("status") == "reviewed" and entry.get("tex", "").strip()
    }
    known = {item["id"] for item in map_data["items"]}
    unknown = sorted(reviewed - known)
    if unknown:
        raise SystemExit(f"Unknown reviewed override ids: {', '.join(unknown)}")

    missing = [item for item in map_data["items"] if item["id"] not in reviewed]
    print(f"Chapter 6 reviewed TeX items: {len(reviewed)}/{len(map_data['items'])}")
    if missing:
        print("Missing:")
        for item in missing:
            print(f"- {item['id']}: {item['number']} {item['title']}")
    else:
        print("All mapped Chapter 6 items have reviewed TeX overrides.")

    if not GENERATED_EXTRACT_PATH.exists():
        print("Generated extract not found; run docs/build_chapter6_extract.py to check emitted prose blocks.")
        return

    block_overrides = {
        block_id: entry
        for block_id, entry in overrides.get("blocks", {}).items()
        if entry.get("status") == "reviewed" and entry.get("tex", "").strip()
    }
    data = json.loads(GENERATED_EXTRACT_PATH.read_text(encoding="utf-8"))
    emitted_auto_blocks = []
    emitted_reviewed_blocks = []
    emitted_marker_blocks = []
    skip_blocks = 0
    for page in data["pages"]:
        for block in page["blocks"]:
            if skip_blocks > 0:
                skip_blocks -= 1
                continue
            block_id = block["id"]
            marker = block.get("marker")
            if block_id in block_overrides:
                emitted_reviewed_blocks.append(block_id)
                skip_blocks = int(block_overrides[block_id].get("skipBlocksAfter", 0))
                continue
            if marker and marker["id"] in reviewed:
                emitted_marker_blocks.append(block_id)
                skip_blocks = int(overrides["items"][marker["id"]].get("skipBlocksAfter", 0))
                continue
            emitted_auto_blocks.append(block)

    print(
        "Emitted Chapter 6 blocks: "
        f"{len(emitted_marker_blocks)} reviewed item blocks, "
        f"{len(emitted_reviewed_blocks)} reviewed prose blocks, "
        f"{len(emitted_auto_blocks)} automatic prose blocks."
    )
    if emitted_auto_blocks:
        print("Automatic prose still emitted:")
        for block in emitted_auto_blocks[:40]:
            text = block["text"].replace("\n", " ")
            if len(text) > 96:
                text = text[:93] + "..."
            print(f"- {block['id']}: {text}")
        if len(emitted_auto_blocks) > 40:
            print(f"- ... {len(emitted_auto_blocks) - 40} more")


if __name__ == "__main__":
    main()
