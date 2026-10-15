#!/usr/bin/env python3
"""Add explicit statement/source relations to existing review ledgers."""

from __future__ import annotations

import json
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parent


def inferred_relation(item: dict) -> str:
    evidence = " ".join(
        str(entry) for entry in item.get("proofBoundary", {}).get("evidence", [])
    )
    reasons = " ".join(str(entry) for entry in item.get("risk", {}).get("reasons", []))
    if re.search(r"interface[-_ ]only", f"{evidence} {reasons}", flags=re.IGNORECASE):
        item.setdefault("states", {})["sourceAligned"] = False
        return "interface_only"
    if item.get("states", {}).get("sourceAligned") is True:
        return "exact"
    return "unresolved"


def main() -> None:
    for path in sorted(ROOT.glob("chapter*-review.json")):
        data = json.loads(path.read_text(encoding="utf-8"))
        for item in data.get("items", {}).values():
            item.setdefault("statementRelation", inferred_relation(item))
        path.write_text(
            json.dumps(data, ensure_ascii=False, indent=2) + "\n", encoding="utf-8"
        )
        print(f"Updated {path.name}")


if __name__ == "__main__":
    main()
