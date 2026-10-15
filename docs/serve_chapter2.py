#!/usr/bin/env python3
"""Serve the book-to-Lean readers and a local, untracked copy of the book PDF.

Usage:
    DOMAIN_THEORY_PDF="/path/to/Domain Theory.pdf" python3 docs/serve_chapter2.py

The repository files are served from the project root.  The PDF is streamed
from the path in DOMAIN_THEORY_PDF, or from the first command-line argument.
The PDF is not copied into the repository.
"""

from __future__ import annotations

import http.server
import hashlib
import json
import mimetypes
import os
from pathlib import Path
import re
import subprocess
import sys
import threading
import time
from urllib.parse import unquote
import webbrowser


ROOT = Path(__file__).resolve().parents[1]
PORT = int(os.environ.get("PORT", "8080"))
PDF_PATH = Path(sys.argv[1] if len(sys.argv) > 1 else os.environ.get("DOMAIN_THEORY_PDF", ""))
SAVE_LOCK = threading.Lock()

CHAPTERS = {
    2: {
        "map": ROOT / "docs/chapter2-map.json",
        "target": "Practice.DomainTheory.Chapter02",
    },
    3: {
        "map": ROOT / "docs/chapter3-map.json",
        "target": "Practice.DomainTheory.Chapter03",
    },
    4: {
        "map": ROOT / "docs/chapter4-map.json",
        "target": "Practice.DomainTheory.Chapter04.NumberedItems",
    },
    5: {
        "map": ROOT / "docs/chapter5-map.json",
        "target": "Practice.DomainTheory.Chapter05.NumberedItems",
    },
    6: {
        "map": ROOT / "docs/chapter6-map.json",
        "target": "Practice.DomainTheory.Chapter06.NumberedItems",
    },
    7: {
        "map": ROOT / "docs/chapter7-map.json",
        "target": "Practice.DomainTheory.Chapter07.NumberedItems",
    },
    8: {
        "map": ROOT / "docs/chapter8-map.json",
        "target": "Practice.DomainTheory.Chapter08",
    },
    9: {
        "map": ROOT / "docs/chapter9-map.json",
        "target": "Practice.DomainTheory.Chapter09",
    },
}


DECL_KEYWORDS = r"(?:def|theorem|lemma|axiom|structure|class|inductive|abbrev|instance)"
DECL_LINE_RE = re.compile(
    rf"^\s*(?:(?:private|protected|noncomputable)\s+)*{DECL_KEYWORDS}\s+([^\s:{{(\[]+)"
)
TOP_LEVEL_RE = re.compile(
    r"^(?:/--|/-!|section\s+|namespace\s+|end\s+|"
    r"(?:(?:private|protected|noncomputable)\s+)*(?:def|theorem|lemma|axiom|"
    r"structure|class|inductive|abbrev|instance)\s+)"
)


class ReaderHandler(http.server.SimpleHTTPRequestHandler):
    def __init__(self, *args, **kwargs):
        super().__init__(*args, directory=str(ROOT), **kwargs)

    def do_GET(self):
        path = unquote(self.path.split("?", 1)[0])
        if path == "/":
            self.path = "/docs/index.html"
            super().do_GET()
            return
        if path == "/book.pdf":
            self.serve_pdf()
            return
        if path == "/api/lean-item":
            self.serve_lean_item()
            return
        super().do_GET()

    def do_POST(self):
        path = unquote(self.path.split("?", 1)[0])
        if path == "/api/save-lean":
            self.save_lean_item()
            return
        self.send_error(404, "Unknown endpoint")

    def send_json(self, status, payload):
        body = json.dumps(payload, ensure_ascii=False).encode("utf-8")
        self.send_response(status)
        self.send_header("Content-Type", "application/json; charset=utf-8")
        self.send_header("Content-Length", str(len(body)))
        self.end_headers()
        self.wfile.write(body)

    def request_query(self):
        _, _, query = self.path.partition("?")
        values = {}
        for part in query.split("&"):
            if not part:
                continue
            key, _, value = part.partition("=")
            values[unquote(key)] = unquote(value)
        return values

    def request_json(self):
        length = int(self.headers.get("Content-Length", "0"))
        raw = self.rfile.read(length)
        if not raw:
            return {}
        return json.loads(raw.decode("utf-8"))

    def serve_lean_item(self):
        query = self.request_query()
        item_id = query.get("id", "")
        declaration = query.get("decl", "")
        try:
            item = locate_item(item_id, declaration or None)
        except Exception as exc:
            self.send_json(400, {"ok": False, "error": str(exc)})
            return
        self.send_json(200, {"ok": True, **item})

    def save_lean_item(self):
        try:
            payload = self.request_json()
            item_id = str(payload.get("id", ""))
            declaration = str(payload.get("declaration", ""))
            new_code = str(payload.get("code", ""))
            expected_file = str(payload.get("file", ""))
            expected_start = int(payload.get("startLine", 0))
            expected_end = int(payload.get("endLine", 0))
            expected_version = str(payload.get("version", ""))
        except Exception as exc:
            self.send_json(400, {"ok": False, "error": f"Invalid JSON payload: {exc}"})
            return

        with SAVE_LOCK:
            try:
                item = locate_item(item_id, declaration or None)
                if not item.get("editable"):
                    raise ValueError(item.get("reason") or "This item is not editable as one contiguous Lean range.")
                if (
                    item["file"] != expected_file
                    or item["startLine"] != expected_start
                    or item["endLine"] != expected_end
                    or item["version"] != expected_version
                ):
                    raise ValueError("The Lean source changed after this item was loaded. Reload it before saving.")
                result = replace_and_build(item, new_code)
            except Exception as exc:
                self.send_json(400, {"ok": False, "error": str(exc)})
                return
        status = 200 if result["ok"] else 409
        self.send_json(status, result)

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
    url = f"http://127.0.0.1:{PORT}/docs/index.html"
    print(f"Open {url}")
    if os.environ.get("NO_BROWSER", "") != "1":
        threading.Timer(0.8, lambda: webbrowser.open(url)).start()
    http.server.ThreadingHTTPServer(("127.0.0.1", PORT), ReaderHandler).serve_forever()


def chapter_number(item_id):
    match = re.search(r"-(\d+)-", item_id)
    if not match:
        raise ValueError(f"Item id does not contain a chapter number: {item_id}")
    chapter = int(match.group(1))
    if chapter not in CHAPTERS:
        raise ValueError(f"Editing is not enabled for Chapter {chapter}")
    return chapter


def load_chapter_map(chapter):
    with CHAPTERS[chapter]["map"].open(encoding="utf-8") as handle:
        return json.load(handle)


def lean_files(chapter, chapter_map):
    files = set()
    for item in chapter_map.get("items", []):
        source = item.get("leanFile", chapter_map.get("leanFile"))
        if source:
            files.add((CHAPTERS[chapter]["map"].parent / source).resolve())
    chapter_dir = ROOT / f"Practice/DomainTheory/Chapter{chapter:02d}"
    if chapter_dir.is_dir():
        files.update(chapter_dir.rglob("*.lean"))
    chapter_file = ROOT / f"Practice/DomainTheory/Chapter{chapter:02d}.lean"
    if chapter_file.is_file():
        files.add(chapter_file)
    if chapter == 2:
        files.update([
            ROOT / "Practice/DomainTheory/Order/DCPO/Basic.lean",
            ROOT / "Practice/DomainTheory/Order/WayBelow.lean",
            ROOT / "Practice/DomainTheory/Topology/ScottTopology.lean",
            ROOT / "Practice/DomainTheory/Chapter02.lean",
        ])
    return sorted(path for path in files if path.is_file())


def module_name(path):
    rel = path.relative_to(ROOT).with_suffix("")
    return ".".join(rel.parts)


def find_doc_start(lines, decl_index):
    i = decl_index - 1
    while i >= 0 and lines[i].strip() == "":
        i -= 1
    if i >= 0 and lines[i].strip().endswith("-/"):
        while i >= 0:
            if lines[i].lstrip().startswith("/--") or lines[i].lstrip().startswith("/-!"):
                return i
            i -= 1
    return decl_index


def find_decl_end(lines, decl_index):
    for i in range(decl_index + 1, len(lines)):
        if TOP_LEVEL_RE.match(lines[i]):
            return i
    return len(lines)


def find_declaration(full_name, paths, preferred_file=None, item_number=""):
    matches = []
    ordered_paths = paths
    if preferred_file in paths:
        ordered_paths = [preferred_file, *(path for path in paths if path != preferred_file)]
    for path in ordered_paths:
        lines = path.read_text(encoding="utf-8").splitlines()
        for index, line in enumerate(lines):
            match = DECL_LINE_RE.match(line)
            if match:
                declared = match.group(1).rstrip(".{}")
            else:
                declared = ""
            if declared == full_name or declared == full_name.split(".")[-1]:
                start = find_doc_start(lines, index)
                end = find_decl_end(lines, index)
                matches.append({
                    "name": declared,
                    "filePath": path,
                    "file": str(path.relative_to(ROOT)),
                    "module": module_name(path),
                    "startLine": start + 1,
                    "endLine": end,
                })
    if not matches:
        return None
    if item_number:
        numbered = []
        for match in matches:
            lines = match["filePath"].read_text(encoding="utf-8").splitlines()
            snippet = "\n".join(lines[match["startLine"] - 1:match["endLine"]])
            if item_number in snippet:
                numbered.append(match)
        if numbered:
            matches = numbered
    if preferred_file:
        preferred = [match for match in matches if match["filePath"] == preferred_file]
        if preferred:
            matches = preferred
    exact = [match for match in matches if match["name"] == full_name]
    ranked = exact or matches
    if len({(match["file"], match["startLine"]) for match in ranked}) != 1:
        locations = ", ".join(f'{match["file"]}:{match["startLine"]}' for match in ranked)
        raise ValueError(f"Ambiguous Lean declaration {full_name}: {locations}")
    return ranked[0]


def locate_item(item_id, declaration_name=None):
    chapter = chapter_number(item_id)
    chapter_map = load_chapter_map(chapter)
    item = next((entry for entry in chapter_map["items"] if entry["id"] == item_id), None)
    if not item:
        raise ValueError(f"Unknown map item: {item_id}")
    if declaration_name and declaration_name not in item.get("lean", []):
        raise ValueError(f"Declaration {declaration_name} is not mapped by {item_id}")
    paths = lean_files(chapter, chapter_map)
    source = item.get("leanFile", chapter_map.get("leanFile"))
    preferred_file = (CHAPTERS[chapter]["map"].parent / source).resolve() if source else None
    requested_names = [declaration_name] if declaration_name else item.get("lean", [])
    decls = [
        find_declaration(name, paths, preferred_file, item.get("number", ""))
        for name in requested_names
    ]
    decls = [decl for decl in decls if decl]
    if not decls:
        raise ValueError(f"No Lean declarations found for {item.get('number', item_id)}")
    by_file = {}
    for decl in decls:
        by_file.setdefault(decl["file"], []).append(decl)
    file_name, file_decls = max(by_file.items(), key=lambda pair: len(pair[1]))
    file_decls = sorted(file_decls, key=lambda decl: decl["startLine"])
    path = ROOT / file_name
    lines = path.read_text(encoding="utf-8").splitlines()
    contiguous = True
    for left, right in zip(file_decls, file_decls[1:]):
        gap = "\n".join(lines[left["endLine"]:right["startLine"] - 1])
        if gap.strip():
            contiguous = False
            break
    editable = len(by_file) == 1 and contiguous
    start = min(decl["startLine"] for decl in file_decls)
    end = max(decl["endLine"] for decl in file_decls)
    if editable:
        code = "\n".join(lines[start - 1:end])
    else:
        blocks = []
        for decl in decls:
            decl_lines = decl["filePath"].read_text(encoding="utf-8").splitlines()
            header = f'-- {decl["file"]}:{decl["startLine"]}-{decl["endLine"]}'
            blocks.append(header + "\n" + "\n".join(
                decl_lines[decl["startLine"] - 1:decl["endLine"]]
            ))
        code = "\n\n".join(blocks)
    if len(by_file) != 1:
        reason = "This item resolves to declarations in multiple Lean files."
    elif not contiguous:
        reason = "This item resolves to non-contiguous declarations; edit the declarations separately."
    else:
        reason = ""
    return {
        "id": item_id,
        "number": item.get("number", item_id),
        "title": item.get("title", ""),
        "file": file_name,
        "module": module_name(path),
        "startLine": start,
        "endLine": end,
        "code": code,
        "chapter": chapter,
        "target": CHAPTERS[chapter]["target"],
        "declaration": declaration_name or "",
        "version": hashlib.sha256(code.encode("utf-8")).hexdigest(),
        "editable": editable,
        "reason": reason,
        "declarations": [
            {k: v for k, v in decl.items() if k != "filePath"}
            for decl in decls
        ],
    }


def replace_and_build(item, new_code):
    path = (ROOT / item["file"]).resolve()
    if ROOT not in path.parents or "Practice" not in path.parts or path.suffix != ".lean":
        raise ValueError(f"Refusing to edit non-Lean project file: {path}")
    original = path.read_text(encoding="utf-8")
    original_lines = original.splitlines()
    start = item["startLine"] - 1
    end = item["endLine"]
    replacement = new_code.replace("\r\n", "\n").replace("\r", "\n").split("\n")
    updated = "\n".join(original_lines[:start] + replacement + original_lines[end:]) + "\n"

    started = time.time()
    try:
        path.write_text(updated, encoding="utf-8")
        build = subprocess.run(
            ["lake", "build", item["target"]],
            cwd=ROOT,
            text=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.STDOUT,
        )
    except Exception:
        path.write_text(original, encoding="utf-8")
        raise
    if build.returncode != 0:
        path.write_text(original, encoding="utf-8")
        return {
            "ok": False,
            "error": "Lean build failed; the original file was restored.",
            "output": build.stdout,
            "target": item["target"],
            "seconds": round(time.time() - started, 2),
        }
    return {
        "ok": True,
        "message": "Saved and Lean build passed.",
        "output": build.stdout,
        "target": item["target"],
        "seconds": round(time.time() - started, 2),
    }


if __name__ == "__main__":
    main()
