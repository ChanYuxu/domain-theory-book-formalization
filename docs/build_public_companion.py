#!/usr/bin/env python3
"""Build public TeX companion PDFs for Chapters 2--9.

Only reviewed numbered items and diagram environments are included.  Automatic
OCR prose and the original textbook PDF never enter this build.
"""

from __future__ import annotations

import argparse
import json
import re
import shutil
import subprocess
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs"
PUBLIC = DOCS / "public"
COMPANION = PUBLIC / "companion"
LOCATORS = PUBLIC / "source-locators.json"
BUILD_DIR = ROOT / "tmp" / "public-companion"
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

BLOCK_ID_RE = re.compile(r"^p(?P<page>\d+)-b(?P<block>\d+)$")
FIGURE_RE = re.compile(r"\\begin\{figure\}.*?\\end\{figure\}", re.DOTALL)
CENTER_RE = re.compile(r"\\begin\{center\}.*?\\end\{center\}", re.DOTALL)
DISPLAY_RE = re.compile(r"\\\[.*?\\\]", re.DOTALL)


def load_json(path: Path) -> dict:
    with path.open(encoding="utf-8") as handle:
        return json.load(handle)


def diagram_fragments(tex: str) -> list[str]:
    """Return TikZ-bearing display environments, excluding surrounding prose."""
    figures = [
        match.group(0).replace(r"\begin{figure}[h]", r"\begin{figure}[ht]")
        for match in FIGURE_RE.finditer(tex)
    ]
    if figures:
        return figures
    centered = [
        match.group(0) for match in CENTER_RE.finditer(tex)
        if "tikzpicture" in match.group(0)
    ]
    if centered:
        return centered
    return [
        match.group(0) for match in DISPLAY_RE.finditer(tex)
        if "tikzpicture" in match.group(0)
    ]


def diagram_key(tex: str) -> str:
    return re.sub(r"\s+", " ", tex).strip()


def block_order(block_id: str) -> tuple[int, int]:
    match = BLOCK_ID_RE.match(block_id)
    if not match:
        raise SystemExit(f"Invalid source block id: {block_id}")
    return int(match.group("page")), int(match.group("block"))


def tex_preamble(chapter: int, title: str) -> list[str]:
    return [
        r"\documentclass[11pt]{article}",
        r"\usepackage[T1]{fontenc}",
        r"\usepackage{lmodern}",
        r"\usepackage[a4paper,left=25mm,right=30mm,top=22mm,bottom=24mm,marginparwidth=18mm]{geometry}",
        r"\usepackage{amsmath,amssymb,mathtools,stmaryrd}",
        r"\usepackage{tikz}",
        r"\usetikzlibrary{arrows.meta,calc,positioning}",
        r"\usepackage{caption}",
        r"\usepackage{xcolor}",
        r"\usepackage{marginnote}",
        r"\usepackage{microtype}",
        r"\usepackage{needspace}",
        r"\usepackage[hidelinks]{hyperref}",
        r"\definecolor{LeanTeal}{HTML}{087F72}",
        r"\definecolor{SourceGray}{HTML}{66736F}",
        r"\setlength{\parindent}{0pt}",
        r"\setlength{\parskip}{0.55em}",
        r"\setlength{\emergencystretch}{2em}",
        r"\newcommand{\leanmarker}[2]{%",
        r"  \Needspace{3\baselineskip}%",
        r"  \marginnote{\hyperlink{#1}{\color{LeanTeal}\fbox{\scriptsize Lean}}}%",
        r"  \hypertarget{#1}{\textbf{#2.}}%",
        r"}",
        r"\newcommand{\sourcepage}[1]{\par\medskip\noindent\textcolor{SourceGray}{\scriptsize Source PDF page #1}\par\smallskip}",
        r"\pagestyle{plain}",
        r"\begin{document}",
        rf"\begin{{center}}\LARGE\bfseries {title}\par\medskip",
        rf"\large Lean 4 Formalization Companion -- Chapter {chapter}\end{{center}}",
        r"\medskip",
        r"\noindent\textit{This project-generated reading copy contains reviewed mathematical items, short source locators, and redrawn diagrams. It does not reproduce the original PDF or automatic OCR prose. Click a Lean tag in the web reader to open the mapped Lean declaration.}",
        r"\bigskip\hrule\bigskip",
    ]


def build_chapter_tex(chapter: int, locators: dict) -> str:
    chapter_map = load_json(DOCS / f"chapter{chapter}-map.json")
    overrides = load_json(DOCS / f"chapter{chapter}-tex-overrides.json")
    locator_items = locators["chapters"][str(chapter)]["items"]
    events: list[tuple[int, int, int, dict]] = []
    item_diagram_keys: set[str] = set()

    for map_index, item in enumerate(chapter_map["items"]):
        item_id = item["id"]
        override = overrides.get("items", {}).get(item_id)
        if not override or override.get("status") != "reviewed" or not override.get("tex"):
            raise SystemExit(f"Chapter {chapter}: missing reviewed TeX for {item_id}")
        locator = locator_items.get(item_id)
        if not locator:
            raise SystemExit(f"Chapter {chapter}: missing public locator for {item_id}")
        page, block = block_order(locator["block"])
        item_tex = override["tex"].replace(
            r"\begin{figure}[h]", r"\begin{figure}[ht]"
        )
        item_diagram_keys.update(diagram_key(fragment) for fragment in diagram_fragments(item_tex))
        events.append((page, block, 10 + map_index, {"type": "item", "map": item, "tex": item_tex}))

    for block_id, override in overrides.get("blocks", {}).items():
        if override.get("status") != "reviewed":
            continue
        fragments = diagram_fragments(override.get("tex", ""))
        if not fragments:
            continue
        page, block = block_order(block_id)
        for fragment_index, fragment in enumerate(fragments):
            if diagram_key(fragment) in item_diagram_keys:
                continue
            events.append((page, block, fragment_index, {"type": "diagram", "tex": fragment}))

    events.sort(key=lambda event: event[:3])
    lines = tex_preamble(chapter, CHAPTER_TITLES[chapter])
    current_section = ""
    current_page = 0
    seen_items: set[str] = set()

    for page, _block, _tie, event in events:
        if event["type"] == "item":
            item = event["map"]
            item_id = item["id"]
            if item_id in seen_items:
                raise SystemExit(f"Chapter {chapter}: duplicate public item {item_id}")
            seen_items.add(item_id)
            section = item.get("section", "")
            if section and section != current_section:
                if current_section:
                    lines.append(r"\clearpage")
                lines.append(rf"\section*{{Section {section}}}")
                current_section = section
            if page != current_page:
                lines.append(rf"\sourcepage{{{page}}}")
                current_page = page
            lines.extend([event["tex"].rstrip(), ""])
        else:
            lines.extend([event["tex"].rstrip(), ""])

    expected = {item["id"] for item in chapter_map["items"]}
    if seen_items != expected:
        raise SystemExit(
            f"Chapter {chapter}: companion coverage mismatch; "
            f"missing={sorted(expected - seen_items)}"
        )
    lines.append(r"\end{document}")
    return "\n".join(lines) + "\n"


def compile_tex(tex_path: Path) -> Path:
    pdflatex = shutil.which("pdflatex")
    if not pdflatex:
        raise SystemExit("pdflatex is required unless --no-compile is used")
    chapter_dir = BUILD_DIR / tex_path.stem
    chapter_dir.mkdir(parents=True, exist_ok=True)
    command = [
        pdflatex,
        "-interaction=nonstopmode",
        "-halt-on-error",
        "-file-line-error",
        f"-output-directory={chapter_dir}",
        str(tex_path),
    ]
    for _ in range(2):
        result = subprocess.run(
            command,
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
        if result.returncode != 0:
            print(result.stdout)
            raise SystemExit(f"TeX build failed for {tex_path.name}")
    pdf_path = chapter_dir / f"{tex_path.stem}.pdf"
    if not pdf_path.exists():
        raise SystemExit(f"TeX build did not produce {pdf_path}")
    return pdf_path


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--chapter", type=int, choices=CHAPTERS, action="append")
    parser.add_argument("--no-compile", action="store_true")
    args = parser.parse_args()

    if not LOCATORS.exists():
        raise SystemExit(
            f"Missing {LOCATORS.relative_to(ROOT)}; run docs/export_public_locators.py first"
        )
    locators = load_json(LOCATORS)
    chapters = args.chapter or list(CHAPTERS)
    COMPANION.mkdir(parents=True, exist_ok=True)

    for chapter in chapters:
        tex_path = COMPANION / f"chapter{chapter}-companion.tex"
        tex_path.write_text(build_chapter_tex(chapter, locators), encoding="ascii")
        print(f"Wrote {tex_path.relative_to(ROOT)}")
        if not args.no_compile:
            built_pdf = compile_tex(tex_path)
            pdf_path = tex_path.with_suffix(".pdf")
            shutil.copy2(built_pdf, pdf_path)
            print(f"Wrote {pdf_path.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
