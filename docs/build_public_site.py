#!/usr/bin/env python3
"""Build the self-contained, read-only GitHub Pages reader."""

from __future__ import annotations

import argparse
import json
import os
import shutil
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs"
PUBLIC = DOCS / "public"
SITE_SOURCE = PUBLIC / "site"
COMPANION = PUBLIC / "companion"
LOCATORS = PUBLIC / "source-locators.json"
PDFJS = DOCS / "vendor" / "pdfjs"
DEFAULT_OUTPUT = ROOT / "_site"
CHAPTERS = range(2, 10)
CHAPTER_TITLES = {
    2: "Domains individually",
    3: "Domains collectively",
    4: "Cartesian closed categories of domains",
    5: "Recursive domain equations",
    6: "Equational theories",
    7: "Domains and logic",
    8: "Further directions",
    9: "Guide to the literature",
}
REPOSITORY = os.environ.get(
    "GITHUB_REPOSITORY", "ChanYuxu/domain-theory-book-formalization"
)

sys.path.insert(0, str(DOCS))
from serve_chapter2 import locate_item  # noqa: E402


def load_json(path: Path) -> dict:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def read_first_line(path: Path) -> str:
    return path.read_text(encoding="utf-8").splitlines()[0].strip()


def current_commit() -> str:
    result = subprocess.run(
        ["git", "rev-parse", "--short=12", "HEAD"],
        cwd=ROOT,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.DEVNULL,
    )
    return result.stdout.strip() if result.returncode == 0 else "working-tree"


def github_source_url(file_name: str, start: int, end: int) -> str:
    anchor = f"#L{start}" if start == end else f"#L{start}-L{end}"
    return f"https://github.com/{REPOSITORY}/blob/main/{file_name}{anchor}"


def public_item(item: dict, source_locator: dict) -> dict:
    declarations = []
    for declaration_name in item["lean"]:
        resolved = locate_item(item["id"], declaration_name)
        declarations.append({
            "name": declaration_name,
            "file": resolved["file"],
            "module": resolved["module"],
            "startLine": resolved["startLine"],
            "endLine": resolved["endLine"],
            "code": resolved["code"],
            "githubUrl": github_source_url(
                resolved["file"], resolved["startLine"], resolved["endLine"]
            ),
        })

    return {
        "id": item["id"],
        "number": item["number"],
        "section": item.get("section", ""),
        "kind": item.get("kind", ""),
        "title": item.get("title", ""),
        "summary": item.get("summary", ""),
        "formalizationStatus": item.get("formalizationStatus", ""),
        "proofBoundaryStatus": item.get("proofBoundaryStatus", ""),
        "reviewNote": item.get("reviewNote", ""),
        "sourcePdfPage": source_locator["pdfPage"],
        "declarations": declarations,
    }


def build_chapter_data(chapter: int, locators: dict, output: Path) -> dict:
    chapter_map = load_json(DOCS / f"chapter{chapter}-map.json")
    chapter_locators = locators["chapters"][str(chapter)]
    items = [
        public_item(item, chapter_locators["items"][item["id"]])
        for item in chapter_map["items"]
    ]
    payload = {
        "schemaVersion": 1,
        "chapter": chapter,
        "title": CHAPTER_TITLES[chapter],
        "notice": chapter_map.get("notice", ""),
        "sourcePdfPages": chapter_locators["sourcePdfPages"],
        "items": items,
    }
    data_path = output / "data" / f"chapter{chapter}.json"
    data_path.write_text(
        json.dumps(payload, ensure_ascii=True, indent=2) + "\n",
        encoding="utf-8",
    )
    return {
        "number": chapter,
        "title": CHAPTER_TITLES[chapter],
        "itemCount": len(items),
        "data": f"data/chapter{chapter}.json",
        "pdf": f"companion/chapter{chapter}-companion.pdf",
    }


def validate_output_path(output: Path) -> None:
    if output == ROOT or ROOT not in output.parents:
        raise SystemExit(f"Refusing to replace unsafe output path: {output}")


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=DEFAULT_OUTPUT)
    args = parser.parse_args()

    output = args.output.expanduser().resolve()
    validate_output_path(output)
    required = [SITE_SOURCE, COMPANION, LOCATORS, PDFJS]
    missing = [str(path.relative_to(ROOT)) for path in required if not path.exists()]
    if missing:
        raise SystemExit(f"Missing public reader inputs: {', '.join(missing)}")

    if output.exists():
        shutil.rmtree(output)
    output.mkdir(parents=True)
    (output / "data").mkdir()
    shutil.copytree(SITE_SOURCE, output, dirs_exist_ok=True)
    shutil.copytree(COMPANION, output / "companion")
    shutil.copytree(PDFJS, output / "vendor" / "pdfjs")
    (output / ".nojekyll").write_text("", encoding="ascii")

    locators = load_json(LOCATORS)
    chapters = [build_chapter_data(chapter, locators, output) for chapter in CHAPTERS]
    manifest = {
        "schemaVersion": 1,
        "project": "Domain Theory Book Formalization",
        "repository": f"https://github.com/{REPOSITORY}",
        "commit": current_commit(),
        "leanToolchain": read_first_line(ROOT / "lean-toolchain"),
        "chapters": chapters,
    }
    (output / "data" / "manifest.json").write_text(
        json.dumps(manifest, ensure_ascii=True, indent=2) + "\n",
        encoding="utf-8",
    )
    print(
        f"Built {output.relative_to(ROOT)} with "
        f"{sum(chapter['itemCount'] for chapter in chapters)} mapped items"
    )


if __name__ == "__main__":
    main()
