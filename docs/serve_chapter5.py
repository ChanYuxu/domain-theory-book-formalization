#!/usr/bin/env python3
"""Serve the Chapter 5 reader and a local, untracked copy of the book PDF.

Usage:
    DOMAIN_THEORY_PDF="/path/to/Domain Theory.pdf" python3 docs/serve_chapter5.py

The repository files are served from the project root.  The PDF is streamed from
the path in DOMAIN_THEORY_PDF, or from the first command-line argument.  The PDF
is not copied into the repository.
"""

from __future__ import annotations

import http.server
import mimetypes
import os
from pathlib import Path
import sys
from urllib.parse import unquote


ROOT = Path(__file__).resolve().parents[1]
PORT = int(os.environ.get("PORT", "8080"))
PDF_PATH = Path(sys.argv[1] if len(sys.argv) > 1 else os.environ.get("DOMAIN_THEORY_PDF", ""))


class Chapter5Handler(http.server.SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=str(ROOT), **kwargs)

    def do_GET(self):
        if unquote(self.path.split("?", 1)[0]) == "/book.pdf":
            self.serve_pdf()
            return
        super().do_GET()

    def serve_pdf(self):
        if not PDF_PATH or not PDF_PATH.exists():
            self.send_error(404, "Set DOMAIN_THEORY_PDF to the local Domain Theory PDF path")
            return
        file_size = PDF_PATH.stat().st_size
        range_header = self.headers.get("Range")
        if range_header and range_header.startswith("bytes="):
            start_text, _, end_text = range_header.removeprefix("bytes=").partition("-")
            start = int(start_text or "0")
            end = int(end_text) if end_text else file_size - 1
            end = min(end, file_size - 1)
            if start > end:
                self.send_error(416, "Invalid byte range")
                return
            self.send_response(206)
            self.send_header("Content-Type", mimetypes.guess_type(PDF_PATH.name)[0] or "application/pdf")
            self.send_header("Accept-Ranges", "bytes")
            self.send_header("Content-Range", f"bytes {start}-{end}/{file_size}")
            self.send_header("Content-Length", str(end - start + 1))
            self.end_headers()
            with PDF_PATH.open("rb") as handle:
                handle.seek(start)
                self.wfile.write(handle.read(end - start + 1))
            return

        self.send_response(200)
        self.send_header("Content-Type", mimetypes.guess_type(PDF_PATH.name)[0] or "application/pdf")
        self.send_header("Accept-Ranges", "bytes")
        self.send_header("Content-Length", str(file_size))
        self.end_headers()
        with PDF_PATH.open("rb") as handle:
            self.copyfile(handle, self.wfile)


def main() -> None:
    if not PDF_PATH:
        print("Set DOMAIN_THEORY_PDF or pass the PDF path as the first argument.", file=sys.stderr)
    elif not PDF_PATH.exists():
        print(f"PDF path does not exist: {PDF_PATH}", file=sys.stderr)
    else:
        print(f"Serving PDF: {PDF_PATH}")
    print(f"Open http://127.0.0.1:{PORT}/docs/chapter5-tex-reader.html")
    http.server.ThreadingHTTPServer(("127.0.0.1", PORT), Chapter5Handler).serve_forever()


if __name__ == "__main__":
    main()
