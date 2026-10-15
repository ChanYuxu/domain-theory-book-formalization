#!/usr/bin/env python3
"""Validate Domain Theory review ledgers and module policy JSON files."""

from __future__ import annotations

import argparse
import json
from pathlib import Path
import re
import sys
from typing import Any


ITEM_ID_RE = re.compile(
    r"^(?:def|prop|lemma|thm|theorem|cor|corollary|formula)-\d+(?:-\d+)+$"
)
RISK_LEVELS = {"critical", "high", "medium", "low"}
PROOF_KINDS = {"proved", "conjecture", "axiom", "admit", "sorry"}
REVIEW_DIMENSIONS = {
    "sourceTex",
    "leanSemantics",
    "proofBoundary",
    "mathlibAlignment",
    "readerMapping",
}
REVIEW_STATUSES = {"pending", "humanApproved", "humanRejected", "stale"}
LAYERS = {"foundation", "core", "book", "reader", "facade"}
STATEMENT_RELATIONS = {
    "exact",
    "equivalent",
    "specialized",
    "stronger",
    "weaker",
    "interface_only",
    "different",
    "unresolved",
}


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(
        description="Validate chapter review and architecture policy JSON."
    )
    parser.add_argument("paths", nargs="+", type=Path)
    return parser.parse_args()


def load_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise ValueError(f"cannot read valid JSON: {exc}") from exc


def require(condition: bool, errors: list[str], message: str) -> None:
    if not condition:
        errors.append(message)


def validate_review(path: Path, data: Any) -> list[str]:
    errors: list[str] = []
    require(isinstance(data, dict), errors, "root must be an object")
    if not isinstance(data, dict):
        return errors
    require(data.get("schemaVersion") == 1, errors, "schemaVersion must be 1")
    source_version = data.get("sourceVersion")
    require(isinstance(source_version, dict), errors, "sourceVersion must be an object")
    if isinstance(source_version, dict):
        require(bool(source_version.get("id")), errors, "sourceVersion.id is required")
        require(
            bool(source_version.get("pdfSha256")),
            errors,
            "sourceVersion.pdfSha256 is required",
        )
    items = data.get("items")
    require(isinstance(items, dict), errors, "items must be an object")
    if not isinstance(items, dict):
        return errors

    for item_id, item in items.items():
        prefix = f"items.{item_id}"
        require(bool(ITEM_ID_RE.match(item_id)), errors, f"{prefix}: invalid permanent ID")
        require(isinstance(item, dict), errors, f"{prefix}: item must be an object")
        if not isinstance(item, dict):
            continue
        require(
            item.get("permanentId") == item_id,
            errors,
            f"{prefix}.permanentId must match its key",
        )
        source = item.get("source")
        require(isinstance(source, dict), errors, f"{prefix}.source must be an object")
        if isinstance(source, dict):
            for field in ("pdfPage", "printedPage", "texSha256", "locator"):
                require(field in source, errors, f"{prefix}.source.{field} is required")

        lean = item.get("lean")
        require(isinstance(lean, dict), errors, f"{prefix}.lean must be an object")
        if isinstance(lean, dict):
            for field in ("canonical", "module", "signatureSha256", "bodySha256"):
                require(bool(lean.get(field)), errors, f"{prefix}.lean.{field} is required")

        relation = item.get("statementRelation")
        require(
            relation in STATEMENT_RELATIONS,
            errors,
            f"{prefix}.statementRelation is required and must be valid",
        )
        states = item.get("states")
        require(isinstance(states, dict), errors, f"{prefix}.states must be an object")
        if isinstance(states, dict):
            source_aligned = states.get("sourceAligned")
            require(
                isinstance(source_aligned, bool),
                errors,
                f"{prefix}.states.sourceAligned must be boolean",
            )
            if source_aligned:
                require(
                    relation in {"exact", "equivalent"},
                    errors,
                    f"{prefix}: sourceAligned true requires exact or equivalent relation",
                )
            if relation in {"interface_only", "different", "unresolved"}:
                require(
                    source_aligned is False,
                    errors,
                    f"{prefix}: {relation} requires sourceAligned false",
                )

        boundary = item.get("proofBoundary")
        require(
            isinstance(boundary, dict), errors, f"{prefix}.proofBoundary must be an object"
        )
        if isinstance(boundary, dict):
            kind = boundary.get("kind")
            reason = boundary.get("reason")
            require(kind in PROOF_KINDS, errors, f"{prefix}: invalid proofBoundary.kind")
            if kind == "conjecture":
                require(
                    reason == "source_explicitly_unknown",
                    errors,
                    f"{prefix}: conjecture requires source_explicitly_unknown",
                )
                require(
                    bool(boundary.get("evidence")),
                    errors,
                    f"{prefix}: conjecture requires source evidence",
                )
            elif kind == "axiom":
                require(
                    reason == "external_book_citation_verified",
                    errors,
                    f"{prefix}: axiom requires external_book_citation_verified",
                )
                require(
                    bool(boundary.get("evidence")),
                    errors,
                    f"{prefix}: axiom requires external evidence",
                )
            elif kind == "admit":
                require(
                    reason == "book_proof_omitted",
                    errors,
                    f"{prefix}: admit requires book_proof_omitted",
                )
            elif kind == "sorry":
                require(
                    reason in {
                        "automation_exhausted",
                        "external_reference_unresolved",
                        "source_gap",
                    },
                    errors,
                    f"{prefix}: invalid sorry reason",
                )
            evidence_text = " ".join(str(entry) for entry in boundary.get("evidence", []))
            if re.search(r"interface[-_ ]only", evidence_text, flags=re.IGNORECASE):
                require(
                    relation == "interface_only" and item.get("states", {}).get("sourceAligned") is False,
                    errors,
                    f"{prefix}: interface-only evidence requires relation interface_only and sourceAligned false",
                )

        risk = item.get("risk")
        require(isinstance(risk, dict), errors, f"{prefix}.risk must be an object")
        if isinstance(risk, dict):
            require(risk.get("level") in RISK_LEVELS, errors, f"{prefix}: invalid risk")
            require(
                isinstance(risk.get("reasons"), list),
                errors,
                f"{prefix}.risk.reasons must be a list",
            )

        cycle = item.get("currentRevisionCycle")
        require(
            isinstance(cycle, dict),
            errors,
            f"{prefix}.currentRevisionCycle must be an object",
        )
        if isinstance(cycle, dict):
            attempts_used = cycle.get("attemptsUsed")
            threshold_lifted = cycle.get("thresholdLifted", False)
            require(
                isinstance(attempts_used, int) and attempts_used >= 0,
                errors,
                f"{prefix}: attemptsUsed must be a nonnegative integer",
            )
            if isinstance(attempts_used, int) and not threshold_lifted:
                require(
                    attempts_used <= 10,
                    errors,
                    f"{prefix}: attemptsUsed above 10 requires thresholdLifted",
                )
            attempts = cycle.get("attempts")
            require(isinstance(attempts, list), errors, f"{prefix}.attempts must be a list")
            if isinstance(attempts, list) and isinstance(attempts_used, int):
                require(
                    len(attempts) == attempts_used,
                    errors,
                    f"{prefix}: attemptsUsed must equal attempts length",
                )

        reviews = item.get("reviews")
        require(isinstance(reviews, dict), errors, f"{prefix}.reviews must be an object")
        if isinstance(reviews, dict):
            require(
                set(reviews) == REVIEW_DIMENSIONS,
                errors,
                f"{prefix}: reviews must contain exactly the five dimensions",
            )
            for dimension, review in reviews.items():
                review_prefix = f"{prefix}.reviews.{dimension}"
                require(
                    isinstance(review, dict), errors, f"{review_prefix} must be an object"
                )
                if not isinstance(review, dict):
                    continue
                status = review.get("status")
                require(status in REVIEW_STATUSES, errors, f"{review_prefix}: invalid status")
                if status == "humanApproved":
                    for field in ("reviewer", "reviewedAt", "contentSha256"):
                        require(
                            bool(review.get(field)),
                            errors,
                            f"{review_prefix}.{field} is required for approval",
                        )
    return errors


def validate_policy(path: Path, data: Any) -> list[str]:
    errors: list[str] = []
    require(isinstance(data, dict), errors, "root must be an object")
    if not isinstance(data, dict):
        return errors
    require(data.get("schemaVersion") == 1, errors, "schemaVersion must be 1")
    modules = data.get("modules")
    require(isinstance(modules, list), errors, "modules must be a list")
    if not isinstance(modules, list):
        return errors
    seen: set[str] = set()
    for position, module in enumerate(modules):
        prefix = f"modules[{position}]"
        require(isinstance(module, dict), errors, f"{prefix} must be an object")
        if not isinstance(module, dict):
            continue
        name = module.get("module")
        require(isinstance(name, str) and bool(name), errors, f"{prefix}.module is required")
        if isinstance(name, str):
            require(name not in seen, errors, f"{prefix}: duplicate module {name}")
            seen.add(name)
        require(module.get("layer") in LAYERS, errors, f"{prefix}: invalid layer")
        require(bool(module.get("concept")), errors, f"{prefix}.concept is required")
        require(isinstance(module.get("owns"), list), errors, f"{prefix}.owns must be a list")
        require(
            isinstance(module.get("allowedImportLayers"), list),
            errors,
            f"{prefix}.allowedImportLayers must be a list",
        )
        require(
            isinstance(module.get("stableFacade"), bool),
            errors,
            f"{prefix}.stableFacade must be boolean",
        )
        split_review = module.get("splitReview")
        require(
            isinstance(split_review, dict), errors, f"{prefix}.splitReview must be an object"
        )
        if isinstance(split_review, dict):
            require(
                split_review.get("status") in {
                    "accepted",
                    "deferred",
                    "not_applicable",
                },
                errors,
                f"{prefix}.splitReview.status is invalid",
            )
            require(
                bool(split_review.get("reason")),
                errors,
                f"{prefix}.splitReview.reason is required",
            )
    return errors


def classify(path: Path, data: Any) -> str:
    if isinstance(data, dict) and "items" in data:
        return "review"
    if isinstance(data, dict) and "modules" in data:
        return "policy"
    raise ValueError("cannot classify JSON as review ledger or module policy")


def main() -> int:
    args = parse_args()
    failures = 0
    for path in args.paths:
        try:
            data = load_json(path)
            kind = classify(path, data)
            errors = validate_review(path, data) if kind == "review" else validate_policy(path, data)
        except ValueError as exc:
            errors = [str(exc)]
        if errors:
            failures += 1
            print(f"FAIL {path}")
            for error in errors:
                print(f"- {error}")
        else:
            print(f"PASS {path}")
    return 1 if failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
