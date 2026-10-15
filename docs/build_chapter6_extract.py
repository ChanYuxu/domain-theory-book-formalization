#!/usr/bin/env python3
"""Build local Chapter 6 reading artifacts from the user's PDF.

The generated files contain extracted textbook text and are intentionally written
under docs/generated/, which is ignored by git.  Keep the public repository to
mapping data, scripts, and UI code.
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
GENERATED = DOCS / "generated"
MAP_PATH = DOCS / "chapter6-map.json"
OVERRIDES_PATH = DOCS / "chapter6-tex-overrides.json"
CHAPTER6_PDF_PAGES = range(85, 106)
ITEM_RE = re.compile(r"^(Definition|Proposition|Lemma|Theorem|Corollary) (6\.\d+\.\d+)(?:\([^)]+\))?\.")
ITEM_SPLIT_RE = re.compile(r"(?m)^(Definition|Proposition|Lemma|Theorem|Corollary) 6\.\d+\.\d+(?:\([^)]+\))?\.")


def run_pdftotext(pdf: Path, page: int) -> str:
    result = subprocess.run(
        ["pdftotext", "-f", str(page), "-l", str(page), str(pdf), "-"],
        check=True,
        text=True,
        capture_output=True,
    )
    return result.stdout.replace("\r\n", "\n")


def normalize_text(text: str) -> str:
    text = text.replace("\u000c", "")
    text = text.replace(
        "\nS\nrelation R is to pass to the transitive closure of R, defined as n∈N\\{0} Rn .",
        "\nrelation R is to pass to the transitive closure of R, defined as ∪_{n∈N∖{0}} R^n.",
    )
    text = re.sub(
        r"\nS\nrelation R is to pass to the transitive closure of R, defined as n∈N\\\{0\} Rn \.",
        "\nrelation R is to pass to the transitive closure of R, defined as ∪_{n∈N∖{0}} R^n.",
        text,
    )
    text = text.replace(
        "T that is, whenever each member of a family (Ai )i∈I belongs to L then so does i∈I Ai .",
        "that is, whenever each member of a family (A_i)_{i∈I} belongs to L then so does ∩_{i∈I} A_i.",
    )
    text = text.replace(
        "\nT\n{B ∈ L | A ⊆ B}.",
        "\n∩ {B ∈ L | A ⊆ B}.",
    )
    text = text.replace(
        "Proposition\nF ↑ 2.2.7.\n↓x holds.",
        "Proposition 2.2.7.",
    )
    text = text.replace(
        "2. If p is a kernel operator on D then for all x ∈ D we have that p(x) = max{y ∈\nim(p) | y ⊑ x}.",
        "2. If p is a kernel operator on D then for all x ∈ D we have that p(x) = max{y ∈ im(p) | y ⊑ x}.",
    )
    text = re.sub(r"[ \t]+\n", "\n", text)
    text = re.sub(r"\n{3,}", "\n\n", text)
    return text.strip()


def split_blocks(text: str) -> list[str]:
    text = ITEM_SPLIT_RE.sub(lambda match: "\n\n" + match.group(0), text)
    raw_blocks = [block.strip() for block in re.split(r"\n\s*\n", text) if block.strip()]
    blocks: list[str] = []
    for block in raw_blocks:
        lines = [line.strip() for line in block.splitlines()]
        if len(lines) == 1 and lines[0].isdigit():
            continue
        blocks.append("\n".join(lines))
    return blocks


def item_id_by_number(items: list[dict]) -> dict[str, str]:
    lookup: dict[str, str] = {}
    for item in items:
        match = re.search(r"6\.\d+\.\d+", item["number"])
        if match:
            lookup[match.group(0)] = item["id"]
    return lookup


def load_overrides(items: list[dict]) -> dict[str, dict]:
    if not OVERRIDES_PATH.exists():
        return {}
    with OVERRIDES_PATH.open("r", encoding="utf-8") as handle:
        data = json.load(handle)
    known = {item["id"] for item in items}
    overrides: dict[str, dict] = {}
    for item_id, entry in data.get("items", {}).items():
        if item_id not in known:
            raise SystemExit(f"Unknown override id in {OVERRIDES_PATH}: {item_id}")
        if entry.get("status") != "reviewed":
            continue
        tex = entry.get("tex", "").rstrip()
        if not tex:
            raise SystemExit(f"Reviewed override has empty TeX: {item_id}")
        overrides[item_id] = {**entry, "tex": tex}
    return overrides


def load_block_overrides() -> dict[str, dict]:
    if not OVERRIDES_PATH.exists():
        return {}
    with OVERRIDES_PATH.open("r", encoding="utf-8") as handle:
        data = json.load(handle)
    overrides: dict[str, dict] = {}
    for block_id, entry in data.get("blocks", {}).items():
        if entry.get("status") != "reviewed":
            continue
        tex = entry.get("tex", "").rstrip()
        if not tex:
            raise SystemExit(f"Reviewed block override has empty TeX: {block_id}")
        overrides[block_id] = {**entry, "tex": tex}
    return overrides


def detect_marker(block: str, lookup: dict[str, str]) -> dict | None:
    first_line = block.splitlines()[0].strip()
    match = ITEM_RE.match(first_line)
    if not match:
        return None
    number = match.group(2)
    item_id = lookup.get(number)
    if not item_id:
        return None
    return {"id": item_id, "number": f"{match.group(1)} {number}"}


TEXT_REPLACEMENTS = {
        "\\": r"\textbackslash{}",
        "&": r"\&",
        "%": r"\%",
        "$": r"\$",
        "#": r"\#",
        "_": r"\_",
        "{": r"\{",
        "}": r"\}",
        "~": r"\textasciitilde{}",
        "^": r"\textasciicircum{}",
        "❜": r"\(\bullet\)",
        "❝": r"\(\bullet\)",
        "❅": r"/",
        "❵": r"\(\cdots\)",
        "❍": r"\(\circ\)",
        "✓": r"v",
        "✒": r"-",
        "✁": r"-",
        "✏": r"-",
        "✑": r"-",
        "❆": r"\textbackslash{}",
        "❘": r"\(|\)",
        "❄": r"\(\downarrow\)",
    "✲": r"\(\to\)",
    "ց": r"\(\searrow\)",
    "❩": r"/",
    "✡": r"/",
    "❏": r"/",
    "\x1a": r"\{",
    "✛": r"+",
    "✘": r"x",
    "✚": r"+",
    "✙": r"+",
    "✟": r"|",
}

MATH_REPLACEMENTS = {
    "\\": r"\setminus",
    "⊑": r"\sqsubseteq",
    "⊒": r"\sqsupseteq",
    "⊔": r"\sqcup",
    "⊓": r"\sqcap",
    "⊥": r"\bot",
    "⊤": r"\top",
    "⊆": r"\subseteq",
    "⊇": r"\supseteq",
    "⊂": r"\subset",
    "∈": r"\in",
    "∉": r"\notin",
    "∅": r"\emptyset",
    "∩": r"\cap",
    "∪": r"\cup",
    "∧": r"\wedge",
    "∨": r"\vee",
    "∀": r"\forall",
    "∃": r"\exists",
    "⇒": r"\Rightarrow",
    "⇔": r"\Leftrightarrow",
    "⇀": r"\rightharpoonup",
    "⇋": r"\leftrightarrows",
    "⇌": r"\rightleftarrows",
    "≠": r"\ne",
    "≤": r"\leq",
    "≥": r"\geq",
    "≪": r"\ll",
    "≺": r"\prec",
    "≻": r"\succ",
    "∼": r"\sim",
    "≃": r"\simeq",
    "∆": r"\Delta",
    "ω": r"\omega",
    "α": r"\alpha",
    "β": r"\beta",
    "σ": r"\sigma",
    "π": r"\pi",
    "λ": r"\lambda",
    "ǫ": r"\epsilon",
    "↑": r"\uparrow",
    "↓": r"\downarrow",
    "→": r"\to",
    "−": r"-",
    "×": r"\times",
    "◦": r"\circ",
    "′": r"'",
    "∗": r"\ast",
    "〈": r"\langle",
    "〉": r"\rangle",
    "∖": r"\setminus",
}

MATH_CHARS = set(MATH_REPLACEMENTS)
TOKEN_RE = re.compile(r"[A-Za-z]+|\d+|[ \t]+|.")


def escape_text(text: str) -> str:
    return "".join(TEXT_REPLACEMENTS.get(char, char) for char in text)


def math_to_latex(text: str) -> str:
    text = text.replace("=⇒", "⇒")
    text = text.replace("6=", "≠")
    rendered = "".join(
        f"{replacement} " if replacement.startswith("\\") else replacement
        for char in text
        for replacement in [MATH_REPLACEMENTS.get(char, char)]
    )
    rendered = re.sub(r"\bN\b", r"\\mathbb{N}", rendered)
    rendered = re.sub(r"(?<!\\)\b([A-Z])n\b", r"\1^n", rendered)
    rendered = re.sub(r"\b([A-Za-z])\s+op\b", r"\1^{op}", rendered)
    rendered = re.sub(r"h\s*([A-Za-z])\s*,\s*([^i]+?)\s*i", r"\\langle \1, \2\\rangle", rendered)
    rendered = rendered.replace(r"\cup _", r"\bigcup_")
    rendered = rendered.replace(r"\cap _", r"\bigcap_")
    rendered = re.sub(r"\s+", " ", rendered).strip()
    return f"${rendered}$"


def is_math_trigger(token: str) -> bool:
    return any(char in MATH_CHARS for char in token) or token == "=⇒"


def is_mathish(token: str) -> bool:
    if token.isspace():
        return True
    if any(char in MATH_CHARS for char in token):
        return True
    if re.fullmatch(r"[A-Za-z]", token):
        return True
    if token in {"op", "id", "Idl"}:
        return True
    if re.fullmatch(r"[A-Z][a-z]", token) and token not in {"If"}:
        return True
    if re.fullmatch(r"\d+", token):
        return True
    return bool(re.fullmatch(r"[,;:=+*/_|^\(\){}\[\]<>\\-]+", token))


def trim_math_span(line: str, start: int, end: int) -> tuple[int, int]:
    while start < end and line[start].isspace():
        start += 1
    while start < end and line[end - 1].isspace():
        end -= 1
    while start < end and line[start] in ",;:":
        start += 1
    while start < end and line[end - 1] in ",;:({[":
        end -= 1
    return start, end


def math_spans(line: str) -> list[tuple[int, int]]:
    tokens = [(match.group(0), match.start(), match.end()) for match in TOKEN_RE.finditer(line)]
    spans: list[tuple[int, int]] = []
    for index, (token, start, end) in enumerate(tokens):
        if not is_math_trigger(token):
            continue
        left = index
        while left > 0 and is_mathish(tokens[left - 1][0]):
            left -= 1
        right = index
        while right + 1 < len(tokens) and is_mathish(tokens[right + 1][0]):
            right += 1
        span = trim_math_span(line, tokens[left][1], tokens[right][2])
        if span[0] >= span[1]:
            continue
        if spans and span[0] <= spans[-1][1]:
            spans[-1] = (spans[-1][0], max(spans[-1][1], span[1]))
        else:
            spans.append(span)
    return spans


def latex_escape_line(line: str) -> str:
    line = re.sub(r"h([A-Za-z])\s*,\s*([⊑⊒≤≥])i", r"〈\1, \2〉", line)
    if line == "{ M | M ⊆ A finite and non-empty} .":
        return r"$\{M \mid M \subseteq A \text{ finite and non-empty}\}$."
    if line == "∩ {B ∈ L | A ⊆ B}. This is the least superset of A which belongs to L and is called":
        return r"$\bigcap\{B \in L \mid A \subseteq B\}$. This is the least superset of A which belongs to L and is called"
    if line == "2. If p is a kernel operator on D then for all x ∈ D we have that p(x) = max{y ∈ im(p) | y ⊑ x}.":
        return r"2. If \(p\) is a kernel operator on \(D\), then for all \(x \in D\), \(p(x)=\max\{y \in \operatorname{im}(p) \mid y \sqsubseteq x\}\)."
    if line == "4. ≪im(p) = (≪D ) ∩ (im(p) × im(p)).":
        return r"4. \(\ll_{\operatorname{im}(p)} = (\ll_D) \cap (\operatorname{im}(p) \times \operatorname{im}(p))\)."
    if line == "D × E = {hx, yi | x ∈ D, y ∈ E},":
        return r"\(D \times E = \{\langle x,y\rangle \mid x \in D,\ y \in E\}\),"
    if line == "hx, yi ⊑ hx′ , y ′ i if and only if x ⊑ x′ and y ⊑ y ′ .":
        return r"\(\langle x,y\rangle \sqsubseteq \langle x',y'\rangle\) if and only if \(x \sqsubseteq x'\) and \(y \sqsubseteq y'\)."
    idl_open = re.match(r"the set \{A ∈ Idl\(B\) \| M ∩ A 6= ∅\} is Scott-open in Idl\(B\)(.*)", line)
    if idl_open:
        return r"the set $\{A \in \operatorname{Idl}(B) \mid M \cap A \ne \emptyset\}$ is Scott-open in $\operatorname{Idl}(B)$" + escape_text(idl_open.group(1))
    set_builder = re.fullmatch(r"\{([A-Za-z]) ∈ ([A-Za-z]) \| \1 ([A-Za-z -]+)\}", line)
    if set_builder:
        var, carrier, condition = set_builder.groups()
        return rf"$\{{{var} \in {carrier} \mid {var}\text{{ {condition}}}\}}$"
    spans = math_spans(line)
    if not spans:
        return escape_text(line)
    parts: list[str] = []
    cursor = 0
    for start, end in spans:
        parts.append(escape_text(line[cursor:start]))
        math = math_to_latex(line[start:end])
        if parts and parts[-1] and not parts[-1][-1].isspace():
            math = " " + math
        if end < len(line) and (line[end].isalnum() or line[end] == "("):
            math += " "
        parts.append(math)
        cursor = end
    parts.append(escape_text(line[cursor:]))
    return "".join(parts)


def latex_escape(text: str) -> str:
    return "\n".join(latex_escape_line(line) for line in text.splitlines())


def build_tex(data: dict, overrides: dict[str, dict], block_overrides: dict[str, dict]) -> str:
    lines = [
        r"\documentclass[11pt]{article}",
        r"\usepackage[a4paper,margin=0.82in,marginparwidth=0.65in]{geometry}",
        r"\usepackage{amsmath,amssymb}",
        r"\usepackage{caption}",
        r"\usepackage{tikz}",
        r"\usepackage{fontspec}",
        r"\setmainfont{STIX Two Text}",
        r"\newfontfamily\symbolfont{Apple Symbols}",
        r"\usepackage{newunicodechar}",
        r"\newunicodechar{❜}{{\symbolfont ❜}}",
        r"\newunicodechar{❅}{{\symbolfont ❅}}",
        r"\newunicodechar{❵}{{\symbolfont ❵}}",
        r"\newunicodechar{❍}{{\symbolfont ❍}}",
        r"\newunicodechar{✓}{{\symbolfont ✓}}",
        r"\newunicodechar{✒}{{\symbolfont ✒}}",
        r"\newunicodechar{✁}{{\symbolfont ✁}}",
        r"\newunicodechar{✏}{{\symbolfont ✏}}",
        r"\newunicodechar{✑}{{\symbolfont ✑}}",
        r"\newunicodechar{❆}{{\symbolfont ❆}}",
        r"\newunicodechar{❘}{{\symbolfont ❘}}",
        r"\newunicodechar{❄}{{\symbolfont ❄}}",
        r"\newunicodechar{✲}{{\symbolfont ✲}}",
        r"\usepackage[hidelinks]{hyperref}",
        r"\usepackage{xcolor}",
        r"\usepackage{marginnote}",
        r"\usepackage{needspace}",
        r"\setlength{\parindent}{0pt}",
        r"\setlength{\parskip}{0.6em}",
        r"\newcommand{\leanmarker}[2]{\Needspace{3\baselineskip}\marginnote{\hyperlink{#1}{\color{teal}\fbox{\scriptsize Lean}}}\hypertarget{#1}{\textbf{#2.}}}",
        r"\begin{document}",
        r"\section*{Chapter 6 marked reading copy}",
        r"\textit{Generated locally from the user's PDF. Do not publish this extracted text unless you have the right to do so.}",
    ]
    skip_blocks = 0
    stop_output = False
    for page in data["pages"]:
        if stop_output:
            break
        page_lines: list[str] = []
        for block in page["blocks"]:
            if block["text"].startswith("Exercises 6.2.23."):
                stop_output = True
                break
            if skip_blocks > 0:
                skip_blocks -= 1
                continue
            marker = block.get("marker")
            if marker and marker["id"] in overrides:
                override = overrides[marker["id"]]
                page_lines.append(override["tex"])
                page_lines.append("")
                marker_skip = int(override.get("skipBlocksAfter", 0))
                block_override = block_overrides.get(block["id"])
                if block_override:
                    page_lines.append(block_override["tex"])
                    page_lines.append("")
                block_skip = int((block_override or {}).get("skipBlocksAfter", 0))
                skip_blocks = max(marker_skip, block_skip)
                continue
            if block["id"] in block_overrides:
                override = block_overrides[block["id"]]
                page_lines.append(override["tex"])
                page_lines.append("")
                skip_blocks = int(override.get("skipBlocksAfter", 0))
                continue
            block_text = block["text"]
            if "Exercises 6.2.23." in block_text:
                block_text = block_text.split("Exercises 6.2.23.", 1)[0].rstrip()
                stop_output = True
                if not block_text:
                    break
            text = latex_escape(block_text)
            if marker:
                number = latex_escape(marker["number"])
                text = ITEM_RE.sub(rf"\\leanmarker{{{marker['id']}}}{{{number}}}", text, count=1)
            page_lines.append(text)
            page_lines.append("")
        if page_lines:
            lines.append(rf"\subsection*{{PDF page {page['pdfPage']}}}")
            lines.extend(page_lines)
    lines.append(r"\end{document}")
    return "\n".join(lines)


def compile_tex(tex_path: Path) -> None:
    xelatex = shutil.which("xelatex")
    if not xelatex:
        print("xelatex not found; wrote TeX but did not compile PDF")
        return
    for _ in range(2):
        subprocess.run(
            [
                xelatex,
                "-interaction=nonstopmode",
                "-halt-on-error",
                f"-output-directory={GENERATED}",
                str(tex_path),
            ],
            cwd=ROOT,
            check=True,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.STDOUT,
        )


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("pdf", type=Path, help="Path to Domain Theory.pdf")
    args = parser.parse_args()
    pdf = args.pdf.expanduser().resolve()
    if not pdf.exists():
      raise SystemExit(f"PDF not found: {pdf}")

    with MAP_PATH.open("r", encoding="utf-8") as handle:
        map_data = json.load(handle)
    lookup = item_id_by_number(map_data["items"])
    overrides = load_overrides(map_data["items"])
    block_overrides = load_block_overrides()

    pages = []
    seen_markers: set[str] = set()
    for pdf_page in CHAPTER6_PDF_PAGES:
        text = normalize_text(run_pdftotext(pdf, pdf_page))
        blocks = []
        for index, block in enumerate(split_blocks(text)):
            marker = detect_marker(block, lookup)
            if marker and marker["id"] in seen_markers:
                marker = None
            if marker:
                seen_markers.add(marker["id"])
            blocks.append({
                "id": f"p{pdf_page}-b{index + 1}",
                "text": block,
                **({"marker": marker} if marker else {}),
            })
        pages.append({"pdfPage": pdf_page, "blocks": blocks})

    GENERATED.mkdir(parents=True, exist_ok=True)
    data = {
        "sourcePdf": str(pdf),
        "chapter": "Chapter 6",
        "pdfPages": [min(CHAPTER6_PDF_PAGES), max(CHAPTER6_PDF_PAGES)],
        "markerCount": len(seen_markers),
        "pages": pages,
    }
    (GENERATED / "chapter6-extract.json").write_text(
        json.dumps(data, ensure_ascii=False, indent=2) + "\n",
        encoding="utf-8",
    )
    (GENERATED / "chapter6-marked.tex").write_text(build_tex(data, overrides, block_overrides), encoding="utf-8")
    compile_tex(GENERATED / "chapter6-marked.tex")
    print(f"Wrote {GENERATED / 'chapter6-extract.json'}")
    print(f"Wrote {GENERATED / 'chapter6-marked.tex'}")
    if (GENERATED / "chapter6-marked.pdf").exists():
        print(f"Wrote {GENERATED / 'chapter6-marked.pdf'}")
    print(f"Detected {len(seen_markers)} mapped markers")


if __name__ == "__main__":
    main()
