# Abramsky--Jung Domain Theory in Lean 4

[![Lean CI and Pages](https://github.com/ChanYuxu/domain-theory-book-formalization/actions/workflows/ci-pages.yml/badge.svg)](https://github.com/ChanYuxu/domain-theory-book-formalization/actions/workflows/ci-pages.yml)
[![Lean 4](https://img.shields.io/badge/Lean-4.30.0--rc2-0b7285)](lean-toolchain)
[![mathlib](https://img.shields.io/badge/mathlib-v4.30.0--rc2-c2410c)](lakefile.toml)
[![Status](https://img.shields.io/badge/status-research%20preview-9b5c00)](#project-status)

An inspectable Lean 4 formalization of Samson Abramsky and Achim Jung's
*Domain Theory*, together with a TeX-to-Lean reader that connects numbered
definitions and results to their Lean declarations.

**[Open the interactive reader](https://chanyuxu.github.io/domain-theory-book-formalization/)**

The project now covers Chapters 1-9. The public reader covers Chapters 2-9 with
291 mapped mathematical and bibliographic items. Chapters 8 and 9 are survey
chapters: their entries preserve definitions, displayed formulas, source
claims, research-interface boundaries, and the complete literature guide
without inventing theorem numbering. This remains a research formalization in
progress, not a proof-complete replacement for the textbook and not yet a
mathlib-ready library.

This publication uses the source snapshot last repaired on **2026-08-18**,
revalidated for release on **2026-10-15**. The source snapshot includes the
Chapter 2-7 statement and interface repairs, the split module architecture,
and declaration-specific reader navigation.

## What This Repository Provides

- A compilable Lean/Lake project with a book-level import:
  `import Practice.DomainTheory`.
- Stable book-facing wrappers that preserve chapter numbering and source
  terminology.
- Reusable order- and topology-level modules where the formalization has a
  sufficiently general interface.
- A static GitHub Pages reader: TeX companion PDF on the left, mapped Lean
  declarations and their disclosed proof boundaries on the right.
- A local transactional editor: save a mapped Lean declaration, run the narrow
  chapter build, and restore the original source automatically if Lean rejects
  the edit.
- Explicit proof boundaries. Remaining `axiom`, `admit`, and `sorry` uses are
  visible rather than hidden behind a completion claim.

## Interactive Reader

### Online, No Installation

Open the [public reader](https://chanyuxu.github.io/domain-theory-book-formalization/),
choose a chapter, and click a `Lean` marker in the TeX-rendered PDF. The right
pane shows the corresponding declaration, source module, and GitHub location.
The PDF and Lean panes scroll independently, and the divider can be resized.

The online reader is deliberately read-only. GitHub Pages serves static files
and cannot run the local Lean compiler or write back to a checkout.

The public companion PDFs are generated from reviewed TeX mathematical items,
short source locators, and redrawn diagrams. The original textbook PDF and
automatic OCR prose are not published. The Pages workflow recompiles these PDFs
from the tracked TeX sources before every deployment.

### Local, Editable

The local reader retains the full save/build/rollback workflow. It uses your
local source PDF only to generate ignored reading artifacts under
`docs/generated/`; those artifacts are never needed by the online reader.

Requirements:

- Python 3
- Lean and Lake through [elan](https://github.com/leanprover/elan)
- Poppler (`pdftotext`)
- A TeX distribution with `xelatex`

Start all Chapter 2-9 readers with one command:

```bash
python3 docs/start_reader.py --pdf "/absolute/path/to/Domain Theory.pdf"
```

Platform launchers are also included:

```text
macOS:   Domain Theory Readers.command
Linux:   ./start-reader.sh --pdf "/path/to/Domain Theory.pdf"
Windows: start-reader.bat --pdf "C:\path\to\Domain Theory.pdf"
```

The launcher builds stale or missing local marked PDFs, starts the reader at
`http://127.0.0.1:8080/docs/index.html`, and opens the chapter chooser.

For Chapters 2-9, selecting one mapped declaration enables editing. A save
is accepted only when:

1. the selected declaration still resolves to the same file and range;
2. only that approved contiguous Lean range is replaced; and
3. the matching chapter target builds successfully.

On a failed build, the server restores the original file byte-for-byte and
returns Lean's diagnostic output to the browser.

### Portable Windows Reader

Maintainers can build a self-contained, read-only Windows package after
building `_site`:

```bash
python3 docs/build_public_site.py
python3 docs/build_portable_reader.py
```

Copy `downloads/DomainTheory-Reader-Windows.zip` to a Windows 10 or 11 machine,
extract it, and double-click `Start Reader.bat`. The package uses Windows
PowerShell to serve the files on loopback and needs no Python, Lean, TeX,
network connection, or original textbook PDF. `SHA256SUMS.txt` records every
packaged file. This mode is deliberately read-only.

## Build the Lean Project

Clone the repository and run:

```bash
git clone https://github.com/ChanYuxu/domain-theory-book-formalization.git
cd domain-theory-book-formalization
lake exe cache get
lake build Practice
```

Use the book as a dependency through its aggregate module:

```lean
import Practice.DomainTheory
```

The repository pins:

```text
Lean    leanprover/lean4:v4.30.0-rc2
mathlib v4.30.0-rc2
```

## Chapter Coverage

| Chapter | Topic | Lean entry point | Reader items | Items with project proof debt |
|---|---|---|---:|---:|
| 1 | Introduction and overview | `Practice.DomainTheory.Chapter01` | - | - |
| 2 | Domains individually | `Practice.DomainTheory.Chapter02` | 57 | 5 |
| 3 | Domains collectively | `Practice.DomainTheory.Chapter03` | 38 | 6 |
| 4 | Cartesian closed categories of domains | `Practice.DomainTheory.Chapter04` | 38 | 23 |
| 5 | Recursive domain equations | `Practice.DomainTheory.Chapter05` | 28 | 6 |
| 6 | Equational theories | `Practice.DomainTheory.Chapter06` | 36 | 18 |
| 7 | Domains and logic | `Practice.DomainTheory.Chapter07` | 63 | 21 |
| 8 | Further directions | `Practice.DomainTheory.Chapter08` | 19 | 2 |
| 9 | Guide to the literature | `Practice.DomainTheory.Chapter09` | 12 | 0 |

The debt column counts mapped items whose declarations depend directly or
transitively on a project axiom or proof placeholder. It is not a count of
untranslated items, and the remaining items still need independent source and
human review. Interface-only and conjectural entries are disclosed separately
in the chapter maps and review ledgers.

Chapter 8 has two disclosed `admit` boundaries: the source states, but does not
prove, the two algebraic characterizations of stability in Section 8.2. Its
other incomplete external theories are represented as interfaces and tracked
for human review rather than asserted as axioms. Chapter 9 contains no proof
debt; it is executable bibliography metadata with verified query examples.

## Repository Structure

```text
Practice.lean                         package entry point
Practice/DomainTheory.lean            book entry point, Chapters 1-9
Practice/DomainTheory/ChapterNN.lean  chapter facades
Practice/DomainTheory/ChapterNN/      section and numbered-item modules
Practice/DomainTheory/Order/          reusable order-theory layer
Practice/DomainTheory/Topology/       reusable topology layer
docs/chapterN-map.json                stable book-item-to-Lean mapping
docs/chapterN-tex-overrides.json      reviewed mathematical TeX items
docs/chapterN-review.json             persistent proof/review ledger
docs/public/                          public companion PDFs and static UI
architecture/module-policy.json       module ownership and import policy
architecture/README.md                human-readable module architecture
docs/check_architecture.py            architecture policy validator
docs/check_formalization_metadata.py  map/debt/ledger consistency validator
docs/check_axiom_footprint.py         Lean-derived transitive axiom audit
docs/build_public_site.py             self-contained Pages artifact builder
docs/build_portable_reader.py         offline Windows package builder
docs/build_survey_chapter.py          reviewed local builders for Chapters 8-9
docs/bootstrap_survey_reviews.py      source-bound review-ledger bootstrapper
docs/serve_chapter2.py                shared local transactional server
```

The book-facing layer preserves printed numbering even when an implementation
delegates to a reusable core theorem or a verified mathlib bridge. A mathlib
theorem is infrastructure, not permission to alter the textbook statement.

## Project Status

A green Lean build establishes elaboration of the named target. It does not by
itself establish source fidelity, proof completeness, API quality, or human
review.

The release audit covers 555 mapped declarations: 96 declarations across 81
book items have disclosed project axiom or proof debt. The 102 tracked review
records have 510 human-review dimensions, all still pending. These records do
not assert human approval or mathlib readiness.

The larger remaining proof gaps concern the categorical results in Chapter 4,
powerdomain representations in Chapter 6, and duality and domain logic in
Chapter 7. Proposition 5.2.7 currently exposes a lawful interface with an
explicit family of chosen solutions; it does not yet construct the source's
canonical bilimits independently.

Proof boundaries follow these project conventions:

| Boundary | Meaning |
|---|---|
| proposition-valued `def` | The source explicitly presents an open claim or conjecture; no evidence is introduced. |
| `axiom` | The book explicitly invokes an externally verified result whose statement has been located and checked. |
| `by admit` | The book states the result but omits its proof. |
| `by sorry` | A supplied proof exhausted ten meaningful formalization attempts, or an external reference remains unresolved. |

Ordinary repository builds may contain disclosed proof debt. A declaration is
not considered a mathlib candidate while it depends on local conjectures,
axioms, admits, or sorries.

## Validation

Build the complete active book:

```bash
lake build Practice
```

Build a bounded chapter target:

```bash
lake build Practice.DomainTheory.Chapter02
lake build Practice.DomainTheory.Chapter03
lake build Practice.DomainTheory.Chapter04.NumberedItems
lake build Practice.DomainTheory.Chapter08
lake build Practice.DomainTheory.Chapter09
```

Rebuild and check the public reader:

```bash
python3 docs/check_architecture.py
python3 docs/validate_workflow_state.py docs/chapter*-review.json architecture/module-policy.json
python3 docs/check_formalization_metadata.py
python3 docs/check_axiom_footprint.py --no-build
python3 docs/build_public_companion.py
python3 docs/build_public_site.py
python3 docs/check_public_release.py _site
```

This publication build requires `pdflatex`, Latin Modern, and the standard AMS,
TikZ, `stmaryrd`, and `microtype` packages.

The tracked `docs/public/source-locators.json` is the sanitized publication
input. `docs/export_public_locators.py` is a maintainer-only command for
refreshing it from ignored local extraction artifacts; CI and clean clones do
not require those artifacts or the original PDF.

The GitHub Actions workflow runs the Lean build before uploading the static
Pages artifact. A failed Lean or publication-safety check prevents deployment.

## Source Material Policy

This repository does not contain the original textbook PDF, absolute local
source paths, or generated OCR extracts. Local extraction output is ignored by
Git. The tracked TeX companions contain the mathematical items used to inspect
the formalization and project-created redrawings of relevant diagrams.

The underlying text is the corrected and expanded online version of the chapter
originally published as:

> Samson Abramsky and Achim Jung, "Domain Theory," in *Handbook of Logic in
> Computer Science*, Volume 3, Clarendon Press, 1994.

Rights in the original work remain with its authors and publisher. This
repository is an independent formalization project and is not an official
edition of the book.

## Contributing

Focused contributions are preferred: one numbered item or one coherent theorem
family at a time. A useful pull request should:

1. preserve the source statement and permanent item id;
2. explain any mathlib theorem reused and the exact semantic bridge;
3. keep proof debt explicit;
4. update the chapter map when declaration ownership changes; and
5. run the narrow chapter build and `lake build Practice` when shared APIs move.

For source-alignment changes, also rebuild the companion PDF and verify the
marker-to-declaration interaction rather than relying only on JSON coverage.
