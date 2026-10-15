#!/usr/bin/env python3
"""Create pending review ledgers for source-bounded survey chapter items.

This bootstrapper is intentionally limited to Chapters 8 and 9.  It computes
content hashes and preserves the distinction between direct book-omission
admits and compilable interfaces whose external laws are absent from the
source chapter.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path

import audit_chapter


ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs"
SOURCE_VERSION = {
    "id": "abramsky-jung-domain-theory-pdf-v1",
    "pdfSha256": "74adfbb57ae86a8b24e5afae312ffa77138480962186136d6823098a2c9c8991",
}


def sha256(value: str) -> str:
    return hashlib.sha256(value.encode("utf-8")).hexdigest()


def normalized_signature(block: str) -> str:
    for marker in (":= by", ":=\n", " where\n"):
        if marker in block:
            return block.split(marker, 1)[0].rstrip()
    return block.splitlines()[0].rstrip()


def module_name(file_name: str) -> str:
    return ".".join(Path(file_name).with_suffix("").parts)


def source_locators(chapter: int) -> dict[str, tuple[int, str]]:
    extract = json.loads(
        (DOCS / "generated" / f"chapter{chapter}-extract.json").read_text(
            encoding="utf-8"
        )
    )
    locators: dict[str, tuple[int, str]] = {}
    for page in extract["pages"]:
        for block in page["blocks"]:
            marker = block.get("marker")
            if marker:
                locators[marker["id"]] = (int(page["pdfPage"]), block["id"])
    return locators


def build_ledger(chapter: int, index: dict) -> dict:
    map_path = DOCS / f"chapter{chapter}-map.json"
    map_data = json.loads(map_path.read_text(encoding="utf-8"))
    overrides = json.loads(
        (DOCS / f"chapter{chapter}-tex-overrides.json").read_text(encoding="utf-8")
    )
    locators = source_locators(chapter)
    ledger = {"schemaVersion": 1, "sourceVersion": SOURCE_VERSION, "items": {}}

    for item in map_data["items"]:
        if item.get("formalizationStatus") not in {"partial", "conjecture"}:
            continue
        preferred = str(
            (
                map_path.parent
                / item.get("leanFile", map_data["leanFile"])
            ).resolve().relative_to(ROOT)
        )
        canonical_name = item["lean"][0]
        candidates = audit_chapter.resolve_candidates(
            canonical_name, chapter, index, preferred
        )
        if len(candidates) != 1:
            raise ValueError(
                f"{item['id']}: expected one canonical declaration, got {len(candidates)}"
            )
        candidate = candidates[0]
        lines = (ROOT / candidate["file"]).read_text(encoding="utf-8").splitlines()
        block = (
            "\n".join(lines[candidate["line"] - 1 : candidate["endLine"]]).rstrip()
            + "\n"
        )
        tex = overrides["items"][item["id"]]["tex"].rstrip()
        pdf_page, block_id = locators[item["id"]]
        is_admit = item.get("proofBoundaryStatus") == "admit"
        boundary_kind = "admit" if is_admit else "proved"
        boundary_reason = (
            "book_proof_omitted"
            if is_admit
            else "interface_only_source_underspecified"
        )
        statement_relation = "exact" if is_admit else "interface_only"
        signature_hash = sha256(normalized_signature(block))
        body_hash = sha256(block)
        tex_hash = sha256(tex)
        ledger["items"][item["id"]] = {
            "permanentId": item["id"],
            "number": item["number"],
            "source": {
                "pdfPage": pdf_page,
                "printedPage": str(pdf_page),
                "texSha256": tex_hash,
                "locator": f"page:{pdf_page}:block:{block_id}",
            },
            "lean": {
                "canonical": candidate["qualified"],
                "module": module_name(candidate["file"]),
                "signatureSha256": signature_hash,
                "bodySha256": body_hash,
            },
            "states": {
                "translated": True,
                "proved": not is_admit,
                "sourceAligned": is_admit,
                "architectureStable": False,
                "mathlibCandidate": False,
            },
            "statementRelation": statement_relation,
            "proofBoundary": {
                "kind": boundary_kind,
                "reason": boundary_reason,
                "evidence": [
                    item["reviewNote"],
                    f"Canonical declaration: {candidate['qualified']}.",
                    "The declaration compiles and the reader exposes the source limitation explicitly.",
                ],
            },
            "risk": {
                "level": "high" if is_admit else "medium",
                "reasons": [boundary_reason],
                "downstreamCount": 0,
            },
            "currentRevisionCycle": {
                "cycle": 1,
                "attemptsUsed": 0,
                "attempts": [],
            },
            "dependencies": {"planned": [], "actual": [], "mismatch": False},
            "reviews": {
                "sourceTex": {"status": "pending"},
                "leanSemantics": {"status": "pending"},
                "proofBoundary": {"status": "pending"},
                "mathlibAlignment": {"status": "pending"},
                "readerMapping": {"status": "pending"},
            },
            "cache": {
                "key": (
                    f"{item['id']}:{tex_hash[:8]}:"
                    f"{signature_hash[:8]}:{body_hash[:8]}"
                )
            },
        }
    return ledger


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("chapters", nargs="*", type=int, choices=(8, 9))
    args = parser.parse_args()
    chapters = args.chapters or [8, 9]
    index = audit_chapter.declaration_index(audit_chapter.lean_files(ROOT), ROOT)
    for chapter in chapters:
        ledger = build_ledger(chapter, index)
        output = DOCS / f"chapter{chapter}-review.json"
        output.write_text(
            json.dumps(ledger, ensure_ascii=False, indent=2) + "\n",
            encoding="utf-8",
        )
        print(
            f"Wrote {output.relative_to(ROOT)} with "
            f"{len(ledger['items'])} records"
        )


if __name__ == "__main__":
    main()
