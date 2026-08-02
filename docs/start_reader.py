#!/usr/bin/env python3
"""Build local reading artifacts and start the editable book-to-Lean reader."""

from __future__ import annotations

import argparse
import os
import shutil
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
DOCS = ROOT / "docs"
GENERATED = DOCS / "generated"
CHAPTERS = range(2, 8)


def requested_pdf(value: str) -> Path:
    candidate = value.strip() or os.environ.get("DOMAIN_THEORY_PDF", "").strip()
    if not candidate and sys.stdin.isatty():
        candidate = input("Path to Domain Theory.pdf: ").strip()
    if not candidate:
        raise SystemExit("Pass --pdf or set DOMAIN_THEORY_PDF.")
    path = Path(candidate).expanduser().resolve()
    if not path.is_file():
        raise SystemExit(f"PDF not found: {path}")
    return path


def artifact_is_stale(chapter: int, pdf: Path) -> bool:
    artifacts = [
        GENERATED / f"chapter{chapter}-extract.json",
        GENERATED / f"chapter{chapter}-marked.pdf",
    ]
    if any(not artifact.exists() for artifact in artifacts):
        return True
    inputs = [
        pdf,
        DOCS / f"build_chapter{chapter}_extract.py",
        DOCS / f"chapter{chapter}-map.json",
        DOCS / f"chapter{chapter}-tex-overrides.json",
    ]
    newest_input = max(path.stat().st_mtime for path in inputs if path.exists())
    return min(artifact.stat().st_mtime for artifact in artifacts) < newest_input


def require_build_tools() -> None:
    missing = [command for command in ("pdftotext", "xelatex") if not shutil.which(command)]
    if missing:
        raise SystemExit(
            "Missing local reader tools: "
            + ", ".join(missing)
            + ". Install Poppler and a TeX distribution, or use the online read-only reader."
        )


def build_chapters(pdf: Path) -> None:
    stale = [chapter for chapter in CHAPTERS if artifact_is_stale(chapter, pdf)]
    if not stale:
        print("Local marked PDFs are current.")
        return
    require_build_tools()
    for chapter in stale:
        print(f"Building local Chapter {chapter} marked PDF...")
        subprocess.run(
            [sys.executable, str(DOCS / f"build_chapter{chapter}_extract.py"), str(pdf)],
            cwd=ROOT,
            check=True,
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--pdf", default="", help="Path to the user's Domain Theory PDF")
    parser.add_argument("--port", type=int, default=int(os.environ.get("PORT", "8080")))
    parser.add_argument("--no-build", action="store_true", help="Use existing local generated files")
    parser.add_argument("--no-browser", action="store_true", help="Do not open a browser automatically")
    args = parser.parse_args()

    pdf = requested_pdf(args.pdf)
    if not args.no_build:
        build_chapters(pdf)

    env = os.environ.copy()
    env["DOMAIN_THEORY_PDF"] = str(pdf)
    env["PORT"] = str(args.port)
    if args.no_browser:
        env["NO_BROWSER"] = "1"
    print(f"Starting reader at http://127.0.0.1:{args.port}/docs/index.html")
    raise SystemExit(
        subprocess.call(
            [sys.executable, str(DOCS / "serve_chapter2.py"), str(pdf)],
            cwd=ROOT,
            env=env,
        )
    )


if __name__ == "__main__":
    main()
