# Lean module architecture

The public API is organized around stable chapter imports and concept-owned
implementation modules.  This follows the same practical separation used in
mathlib: users import a stable facade, while reusable definitions and proofs
have one documented owner with explicit dependencies.

## Module roles

| Role | Typical path | Responsibility |
|---|---|---|
| Book facade | `ChapterNN.lean` | Stable public import for one complete chapter |
| Foundation/core | `ChapterNN/Core.lean`, `Order/`, `Topology/` | Reusable mathematical structures and operations |
| Book implementation | `ChapterNN/Section*.lean` | Source-ordered definitions, statements, and proofs |
| Numbered facade | `ChapterNN/NumberedItems.lean` | Import-only aggregation of textbook declarations |
| Internal split | `SectionXX/*.lean`, `NumberedItems/*.lean` | Coherent dependency clusters behind a stable import path |

The role is semantic, not a line-count category.  A long proof stays intact. A
module over 1000 lines triggers a recorded split review, but it is split only
when the resulting modules have meaningful mathematical ownership and useful
independent build targets.

## Import direction

Implementation dependencies point from specialized material to the smallest
module that owns the required API:

```text
foundation/core <- section implementation <- numbered facade <- chapter facade
```

In particular:

- an internal module does not import its chapter's public facade;
- a later chapter imports a previous `Core` or section module when it only needs
  that API, rather than importing the complete previous chapter;
- compatibility paths remain import-only facades after a physical split;
- declarations keep their namespace and canonical name when ownership moves.

## Stable identity

Physical source paths may change, but the following identities are preserved:

- the public imports `Practice.DomainTheory.ChapterNN`;
- canonical Lean declaration names;
- permanent textbook item ids in `docs/chapterN-map.json`;
- source page and TeX-review records;
- proof-boundary classification in `docs/chapterN-review.json`.

When a declaration moves, refresh reader ranges and ledger module locators in
the same change.  Do not use a facade to hide stale ownership metadata.

## Enforcement

`module-policy.json` records every governed module, its layer, mathematical
owner, exact imports, stable consumers, and split-review decision.  Validate a
structural change with:

```bash
python3 docs/update_reader_ranges.py 2 3 4 5 6 7
python3 docs/check_architecture.py
python3 docs/check_formalization_metadata.py
python3 docs/check_axiom_footprint.py --no-build
lake build Practice
```

The architecture check rejects unregistered modules, undeclared imports,
forbidden layer dependencies, stale public-consumer records, duplicate owners,
book-item ownership drift, and import cycles.
