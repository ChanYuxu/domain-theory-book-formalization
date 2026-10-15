#!/usr/bin/env python3
"""Build local marked TeX/PDF artifacts for survey Chapters 8 and 9.

Unlike Chapters 2--7, these chapters have no sequence of numbered theorem
environments to recover by OCR.  Their project-authored reviewed TeX is the
source of truth.  The user's PDF is used only to identify the source edition;
no original prose or absolute path is written outside ignored docs/generated/.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess


ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs"
GENERATED = DOCS / "generated"
SOURCE_PDF_SHA256 = "74adfbb57ae86a8b24e5afae312ffa77138480962186136d6823098a2c9c8991"
CHAPTER_TITLES = {
    8: "Further directions",
    9: "Guide to the literature",
}


def load_json(path: Path) -> dict:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def reviewed_items(chapter: int) -> tuple[dict, list[tuple[dict, str]]]:
    chapter_map = load_json(DOCS / f"chapter{chapter}-map.json")
    overrides = load_json(DOCS / f"chapter{chapter}-tex-overrides.json")
    rows: list[tuple[dict, str]] = []
    for item in chapter_map["items"]:
        override = overrides.get("items", {}).get(item["id"], {})
        if override.get("status") != "reviewed" or not override.get("tex"):
            raise SystemExit(f"Chapter {chapter}: missing reviewed TeX for {item['id']}")
        rows.append((item, override["tex"].rstrip()))
    return chapter_map, rows


def build_extract(chapter: int, pdf: Path, rows: list[tuple[dict, str]]) -> dict:
    by_page: dict[int, list[tuple[dict, str]]] = {}
    for item, tex in rows:
        page = int(item["sourcePdfPage"])
        by_page.setdefault(page, []).append((item, tex))
    pages = []
    for page, page_rows in by_page.items():
        blocks = []
        for index, (item, _tex) in enumerate(page_rows, start=1):
            blocks.append(
                {
                    "id": f"p{page}-b{index}",
                    "text": item.get("summary", item["title"]),
                    "marker": {"id": item["id"], "number": item["number"]},
                }
            )
        pages.append({"pdfPage": page, "blocks": blocks})
    source_pages = sorted(by_page)
    return {
        "sourcePdf": str(pdf),
        "sourcePdfSha256": file_sha256(pdf),
        "chapter": f"Chapter {chapter}",
        "pdfPages": [source_pages[0], source_pages[-1]],
        "markerCount": len(rows),
        "pages": pages,
    }


def build_tex(chapter: int, rows: list[tuple[dict, str]]) -> str:
    lines = [
        r"\documentclass[11pt]{article}",
        r"\usepackage[a4paper,left=25mm,right=30mm,top=22mm,bottom=24mm,marginparwidth=18mm]{geometry}",
        r"\usepackage{amsmath,amssymb,mathtools,stmaryrd}",
        r"\usepackage{fontspec}",
        r"\setmainfont{STIX Two Text}",
        r"\usepackage[hidelinks]{hyperref}",
        r"\usepackage{xcolor}",
        r"\usepackage{marginnote}",
        r"\usepackage{microtype}",
        r"\definecolor{LeanTeal}{HTML}{087F72}",
        r"\definecolor{SourceGray}{HTML}{66736F}",
        r"\setlength{\parindent}{0pt}",
        r"\setlength{\parskip}{0.65em}",
        r"\setlength{\emergencystretch}{2em}",
        r"\newcommand{\leanmarker}[2]{%",
        r"  \marginnote{\hyperlink{#1}{\color{LeanTeal}\fbox{\scriptsize Lean}}}%",
        r"  \hypertarget{#1}{\textbf{#2.}}%",
        r"}",
        r"\newcommand{\sourcepage}[1]{\par\medskip\noindent\textcolor{SourceGray}{\scriptsize Source PDF page #1}\par\smallskip}",
        r"\pagestyle{plain}",
        r"\begin{document}",
        rf"\begin{{center}}\LARGE\bfseries Chapter {chapter}: {CHAPTER_TITLES[chapter]}\end{{center}}",
        r"\noindent\textit{Project-generated reviewed reading copy. It contains source-aligned definitions, formulas, bibliography keys, and locators; it does not reproduce the original PDF or automatic OCR prose.}",
        r"\bigskip\hrule\bigskip",
    ]
    current_page = None
    current_section = None
    for item, tex in rows:
        page = int(item["sourcePdfPage"])
        section = item.get("section", "")
        if page != current_page:
            if current_page is not None:
                lines.append(r"\clearpage")
            lines.append(rf"\sourcepage{{{page}}}")
            current_page = page
            current_section = None
        if section and section != current_section:
            lines.append(rf"\subsection*{{Section {section}}}")
            current_section = section
        lines.extend([tex, ""])
    lines.append(r"\end{document}")
    return "\n".join(lines) + "\n"


def compile_tex(tex_path: Path) -> None:
    xelatex = shutil.which("xelatex")
    if not xelatex:
        raise SystemExit("xelatex is required to build the local marked PDF")
    for _ in range(2):
        completed = subprocess.run(
            [
                xelatex,
                "-interaction=nonstopmode",
                "-halt-on-error",
                "-file-line-error",
                f"-output-directory={GENERATED}",
                str(tex_path),
            ],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
            check=False,
        )
        if completed.returncode != 0:
            print(completed.stdout)
            raise SystemExit(f"TeX build failed for {tex_path.name}")


def build_chapter(chapter: int, pdf: Path) -> None:
    if chapter not in CHAPTER_TITLES:
        raise SystemExit(f"Unsupported survey chapter: {chapter}")
    if not pdf.is_file():
        raise SystemExit(f"PDF not found: {pdf}")
    actual_hash = file_sha256(pdf)
    if actual_hash != SOURCE_PDF_SHA256:
        print(
            "Warning: the selected PDF differs from the audited source edition; "
            "stable source-page locators may need human review."
        )
    _chapter_map, rows = reviewed_items(chapter)
    GENERATED.mkdir(parents=True, exist_ok=True)
    extract = build_extract(chapter, pdf, rows)
    extract_path = GENERATED / f"chapter{chapter}-extract.json"
    tex_path = GENERATED / f"chapter{chapter}-marked.tex"
    extract_path.write_text(
        json.dumps(extract, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    tex_path.write_text(build_tex(chapter, rows), encoding="ascii")
    compile_tex(tex_path)
    print(f"Wrote {extract_path}")
    print(f"Wrote {tex_path}")
    print(f"Wrote {GENERATED / f'chapter{chapter}-marked.pdf'}")
    print(f"Mapped {len(rows)} reviewed items")


def main_for_chapter(chapter: int) -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("pdf", type=Path, help="Path to Domain Theory.pdf")
    args = parser.parse_args()
    build_chapter(chapter, args.pdf.expanduser().resolve())
