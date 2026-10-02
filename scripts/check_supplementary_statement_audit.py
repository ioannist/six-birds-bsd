#!/usr/bin/env python3
"""Check coverage and freshness of the supplementary manual assessments.

This checks the audit record, not the truth of its mathematical assessments.
The separate semantic alignment checker covers the theorem manifest entries.
"""
from __future__ import annotations

import argparse
import json
import tomllib

import check_semantic_alignment as alignment


AUDIT = alignment.TRACEABILITY_DIR / "supplementary_statement_audit.json"


def expected_items() -> dict[str, dict]:
    records, _, _ = alignment.collect_records()
    theorem_labels = {item["latex_label"] for item in alignment.theorem_items()}
    declarations = {}
    for axis in ("apparatus", "closure"):
        path = alignment.ROOT / "lean" / "manifests" / f"{axis}_manifest.toml"
        with path.open("rb") as handle:
            manifest = tomllib.load(handle)
        declarations.update({item["paper_label"]: item["lean_decl"]
                             for kind in ("claim", "definition")
                             for item in manifest.get(kind, [])})
    return {record["latex_label"]: {
        **record, "lean_decl": declarations.get(record["latex_label"], "")
    } for record in records if record["latex_label"] not in theorem_labels}


def validate(data: dict) -> list[str]:
    errors = []
    expected = expected_items()
    if not expected:
        return ["no supplementary statements selected; refusing an empty audit"]
    if data.get("lean_context_hash") != alignment.lean_context_hash():
        errors.append("supplementary audit lean_context_hash is stale")
    entries = data.get("items")
    if not isinstance(entries, list):
        return errors + ["supplementary audit items must be a list"]
    seen = set()
    for entry in entries:
        if not isinstance(entry, dict):
            errors.append("supplementary audit entry must be an object")
            continue
        label = entry.get("latex_label")
        if not isinstance(label, str):
            errors.append("supplementary audit entry has no string label")
            continue
        if label in seen:
            errors.append(f"duplicate supplementary label {label}")
        seen.add(label)
        if label not in expected:
            errors.append(f"unexpected supplementary label {label}")
            continue
        for key in ("env_kind", "source_file", "line_start", "statement_hash", "lean_decl"):
            if entry.get(key) != expected[label][key]:
                errors.append(f"{label} supplementary {key} is stale")
        for key in ("assessment", "notes"):
            if not isinstance(entry.get(key), str) or not entry[key].strip():
                errors.append(f"{label} supplementary {key} is missing")
    for label in sorted(set(expected) - seen):
        errors.append(f"missing supplementary label {label}")
    return errors


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="check the manual audit snapshot")
    parser.parse_args()
    try:
        data = json.loads(AUDIT.read_text())
        if not isinstance(data, dict):
            raise ValueError("supplementary audit must be an object")
        errors = validate(data)
    except (OSError, ValueError) as exc:
        errors = [str(exc)]
    if errors:
        for error in errors:
            print(f"ERROR: {error}")
        return 1
    print(f"supplementary audit coverage check passed: {len(expected_items())} "
          "current statements; mathematical conclusions remain manual assessments")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
