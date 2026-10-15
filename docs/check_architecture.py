#!/usr/bin/env python3
"""Validate the tracked module policy for the book formalization.

The policy records stable import paths, mathematical ownership, exact imports,
book-item ownership through the chapter maps, and reviewed reasons for keeping
cohesive large modules intact.  This is a structural check; Lean remains the
authority for elaborated declarations and theorem dependencies.
"""

from __future__ import annotations

from collections import defaultdict
import json
from pathlib import Path
import re
import sys
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
POLICY_PATH = ROOT / "architecture" / "module-policy.json"
LAYERS = {"foundation", "core", "book", "reader", "facade"}
SPLIT_STATES = {"accepted", "deferred", "not_applicable"}
IMPORT_RE = re.compile(r"^\s*import\s+([^\s]+)", re.MULTILINE)


def module_for_path(path: Path) -> str:
    return ".".join(path.relative_to(ROOT).with_suffix("").parts)


def path_for_module(module: str) -> Path:
    return ROOT.joinpath(*module.split(".")).with_suffix(".lean")


def imports_for(path: Path) -> list[str]:
    return IMPORT_RE.findall(path.read_text(encoding="utf-8"))


def discovered_paths(chapters: list[int], extra_paths: list[str]) -> set[str]:
    paths: set[str] = set()
    for chapter in chapters:
        entry = ROOT / f"Practice/DomainTheory/Chapter{chapter:02}.lean"
        directory = ROOT / f"Practice/DomainTheory/Chapter{chapter:02}"
        if entry.is_file():
            paths.add(str(entry.relative_to(ROOT)))
        if directory.is_dir():
            paths.update(str(path.relative_to(ROOT)) for path in directory.rglob("*.lean"))
    paths.update(extra_paths)
    return paths


def mapped_book_items(chapters: list[int]) -> dict[str, list[str]]:
    by_module: dict[str, list[str]] = defaultdict(list)
    for chapter in chapters:
        map_path = ROOT / "docs" / f"chapter{chapter}-map.json"
        data = json.loads(map_path.read_text(encoding="utf-8"))
        for item in data.get("items", []):
            relative = item.get("leanFile", data.get("leanFile"))
            if not isinstance(relative, str) or not relative:
                raise ValueError(f"{map_path.name}: {item.get('id')} has no leanFile")
            lean_path = (map_path.parent / relative).resolve()
            if ROOT not in lean_path.parents:
                raise ValueError(f"{map_path.name}: {item.get('id')} escapes the repository")
            by_module[module_for_path(lean_path)].append(str(item["id"]))
    return by_module


def find_cycle(graph: dict[str, set[str]]) -> list[str] | None:
    state: dict[str, int] = {}
    stack: list[str] = []

    def visit(node: str) -> list[str] | None:
        state[node] = 1
        stack.append(node)
        for target in sorted(graph[node]):
            if state.get(target, 0) == 0:
                cycle = visit(target)
                if cycle:
                    return cycle
            elif state.get(target) == 1:
                start = stack.index(target)
                return stack[start:] + [target]
        stack.pop()
        state[node] = 2
        return None

    for node in sorted(graph):
        if state.get(node, 0) == 0:
            cycle = visit(node)
            if cycle:
                return cycle
    return None


def require_type(
    errors: list[str], module: str, entry: dict[str, Any], key: str, expected: type
) -> None:
    if not isinstance(entry.get(key), expected):
        errors.append(f"{module}: {key} must be {expected.__name__}")


def main() -> int:
    errors: list[str] = []
    warnings: list[str] = []
    try:
        policy = json.loads(POLICY_PATH.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        print(f"architecture policy error: {exc}", file=sys.stderr)
        return 1

    if policy.get("schemaVersion") != 1:
        errors.append("schemaVersion must be 1")
    scope = policy.get("scope", {})
    chapters = scope.get("chapters")
    if not isinstance(chapters, list) or not chapters or not all(isinstance(c, int) for c in chapters):
        errors.append("scope.chapters must be a nonempty integer list")
        chapters = []
    extra_paths = scope.get("extraPaths", [])
    if not isinstance(extra_paths, list) or not all(isinstance(path, str) for path in extra_paths):
        errors.append("scope.extraPaths must be a string list")
        extra_paths = []
    if policy.get("activeMigrations") != []:
        errors.append("activeMigrations must be empty before architecture validation passes")

    raw_modules = policy.get("modules")
    if not isinstance(raw_modules, list):
        errors.append("modules must be an array")
        raw_modules = []

    modules: dict[str, dict[str, Any]] = {}
    paths: dict[str, str] = {}
    owners: dict[str, str] = {}
    for position, raw in enumerate(raw_modules):
        if not isinstance(raw, dict):
            errors.append(f"modules[{position}] must be an object")
            continue
        module = raw.get("module")
        path = raw.get("path")
        if not isinstance(module, str) or not module:
            errors.append(f"modules[{position}].module must be a nonempty string")
            continue
        if module in modules:
            errors.append(f"duplicate module registration: {module}")
            continue
        modules[module] = raw
        if not isinstance(path, str) or not path:
            errors.append(f"{module}: path must be a nonempty string")
        elif path in paths:
            errors.append(f"duplicate path registration: {path} ({paths[path]}, {module})")
        else:
            paths[path] = module

        if raw.get("layer") not in LAYERS:
            errors.append(f"{module}: invalid layer {raw.get('layer')!r}")
        require_type(errors, module, raw, "concept", str)
        if isinstance(raw.get("concept"), str) and not raw["concept"].strip():
            errors.append(f"{module}: concept must not be empty")
        for key in ("owns", "allowedImports", "allowedImportLayers", "publicConsumers"):
            require_type(errors, module, raw, key, list)
        require_type(errors, module, raw, "stableFacade", bool)
        split = raw.get("splitReview")
        if not isinstance(split, dict):
            errors.append(f"{module}: splitReview must be an object")
        else:
            if split.get("status") not in SPLIT_STATES:
                errors.append(f"{module}: invalid splitReview status {split.get('status')!r}")
            if not isinstance(split.get("reason"), str) or not split["reason"].strip():
                errors.append(f"{module}: splitReview.reason must be nonempty")
            if split.get("status") == "deferred":
                warnings.append(f"{module}: split review remains deferred")

        for owner in raw.get("owns", []) if isinstance(raw.get("owns"), list) else []:
            if not isinstance(owner, str) or not owner:
                errors.append(f"{module}: owns entries must be nonempty strings")
            elif owner in owners:
                errors.append(f"public owner {owner} is claimed by both {owners[owner]} and {module}")
            else:
                owners[owner] = module

    expected_paths = discovered_paths(chapters, extra_paths)
    registered_paths = set(paths)
    for path in sorted(expected_paths - registered_paths):
        errors.append(f"unregistered governed module: {path}")
    for path in sorted(registered_paths - expected_paths):
        errors.append(f"registered path is outside or missing from the governed scope: {path}")

    graph: dict[str, set[str]] = {module: set() for module in modules}
    for module, entry in modules.items():
        path_value = entry.get("path")
        if not isinstance(path_value, str):
            continue
        path = ROOT / path_value
        if not path.is_file():
            errors.append(f"{module}: file does not exist: {path_value}")
            continue
        if module_for_path(path) != module:
            errors.append(f"{module}: path resolves to module {module_for_path(path)}")
        actual_imports = imports_for(path)
        expected_imports = entry.get("allowedImports", [])
        if isinstance(expected_imports, list) and set(actual_imports) != set(expected_imports):
            missing = sorted(set(actual_imports) - set(expected_imports))
            stale = sorted(set(expected_imports) - set(actual_imports))
            errors.append(f"{module}: import policy mismatch; unregistered={missing}, stale={stale}")
        allowed_layers = set(entry.get("allowedImportLayers", []))
        unknown_layers = allowed_layers - LAYERS
        if unknown_layers:
            errors.append(f"{module}: invalid allowed import layers {sorted(unknown_layers)}")
        for imported in actual_imports:
            if imported not in modules:
                continue
            graph[module].add(imported)
            imported_layer = modules[imported].get("layer")
            if imported_layer not in allowed_layers:
                errors.append(
                    f"{module}: import of {imported} ({imported_layer}) is outside allowedImportLayers"
                )
            if entry.get("layer") == "core" and imported_layer in {"book", "facade"}:
                errors.append(f"{module}: core module imports {imported_layer} module {imported}")

        for consumer in entry.get("publicConsumers", []):
            if not isinstance(consumer, str) or not consumer:
                errors.append(f"{module}: publicConsumers entries must be nonempty strings")
                continue
            consumer_path = path_for_module(consumer)
            if not consumer_path.is_file():
                errors.append(f"{module}: public consumer does not exist: {consumer}")
            elif module not in imports_for(consumer_path):
                errors.append(f"{module}: declared public consumer {consumer} does not import it")

        line_count = len(path.read_text(encoding="utf-8").splitlines())
        if line_count > 1000:
            split = entry.get("splitReview", {})
            warnings.append(
                f"{module}: {line_count} lines; split review {split.get('status', 'missing')}"
            )

    cycle = find_cycle(graph)
    if cycle:
        errors.append("governed import cycle: " + " -> ".join(cycle))

    try:
        map_items = mapped_book_items(chapters)
    except (OSError, json.JSONDecodeError, KeyError, ValueError) as exc:
        errors.append(f"cannot resolve book-item ownership: {exc}")
        map_items = {}
    for mapped_module in sorted(map_items):
        if mapped_module not in modules:
            errors.append(f"mapped book items target unregistered module: {mapped_module}")
    for module, entry in modules.items():
        configured = entry.get("bookItems")
        actual = map_items.get(module, [])
        if configured == "from-map":
            if not actual:
                errors.append(f"{module}: bookItems is from-map but no item maps to this module")
        elif isinstance(configured, list):
            if configured != actual:
                errors.append(
                    f"{module}: bookItems mismatch; policy={configured}, map={actual}"
                )
        else:
            errors.append(f"{module}: bookItems must be an array or 'from-map'")

    print(
        f"Architecture policy: {len(modules)} modules, "
        f"{sum(len(ids) for ids in map_items.values())} mapped items, "
        f"{sum(len(targets) for targets in graph.values())} governed imports."
    )
    for warning in warnings:
        print(f"warning: {warning}")
    if errors:
        for error in errors:
            print(f"error: {error}", file=sys.stderr)
        return 1
    print("Architecture policy check passed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
