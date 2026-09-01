#!/usr/bin/env python3
"""Validate the statements-of-record registry for the BSD paper.

The registry binds every paper-facing label to its target paper,
destination, proof-presentation mode, Lean coverage, and Lean declaration.
This validator cross-checks that registry against the Lean manifests and
paper inventories so drafting cannot silently drift from the mechanized
corpus or from the Phase 0 source inventory.
"""

from __future__ import annotations

import argparse
from collections import Counter
import re
import sys
from pathlib import Path

try:  # Python 3.11+
    import tomllib  # type: ignore[import-not-found]
except ModuleNotFoundError:  # Python 3.10 in the current repo image.
    import tomli as tomllib  # type: ignore[no-redef]

import yaml


ROOT = Path(__file__).resolve().parents[1]
STATEMENTS = ROOT / "paper" / "notes" / "statements-of-record.yml"
MANIFESTS = {
    "apparatus": ROOT / "lean" / "manifests" / "apparatus_manifest.toml",
    "closure": ROOT / "lean" / "manifests" / "closure_manifest.toml",
}
INVENTORIES = {
    "apparatus": ROOT / "formalization" / "inventory" / "apparatus_paper_inventory.toml",
    "closure": ROOT / "formalization" / "inventory" / "closure_paper_inventory.toml",
}

TOP_LEVEL_KEYS = {
    "schema_version",
    "status",
    "total_rows",
    "target_paper_counts",
    "target_destination_counts",
    "proof_presentation_counts",
    "lean_coverage_counts",
    "semantic_alignment_counts",
    "rows",
}
ROW_FIELDS = {
    "paper_label",
    "env_kind",
    "source_file",
    "source_line",
    "source_section",
    "theorem_title",
    "target_paper",
    "target_destination",
    "target_section_hint",
    "proof_presentation",
    "lean_coverage",
    "lean_decl",
    "semantic_alignment",
    "notes",
}
COUNT_BUCKETS = {
    "target_paper_counts": "target_paper",
    "target_destination_counts": "target_destination",
    "proof_presentation_counts": "proof_presentation",
    "lean_coverage_counts": "lean_coverage",
    "semantic_alignment_counts": "semantic_alignment",
}
ALLOWED_TARGET_PAPERS = {"apparatus", "closure", "dropped"}
ALLOWED_DESTINATIONS = {"body", "appendix", "source_only", "evidence_pack_only"}
ALLOWED_PROOF_PRESENTATIONS = {
    "body_full",
    "body_sketch",
    "appendix_only",
    "lean_substantive",
    "lean_traceability_only",
    "standard_reference",
    "definition_entry",
}
ALLOWED_LEAN_COVERAGE = {
    "theorem",
    "partial",
    "definition",
    "not_mechanized",
    # `recognition_source` — typed structure carrier; not a Lean
    # theorem/definition entry.
    "recognition_source",
    # `obligation` — manifest-only obligation.
    "obligation",
}
ALLOWED_SEMANTIC_ALIGNMENT = {
    "faithful",
    "narrowed_surrogate",
    "weakened_genericized",
    "needs_strengthening",
    "projection_packaged",
    "not_applicable",
}
# Allowed source_file values per target_paper. For this project, the source-of-
# record is the math artifact at anti_loc/extracted_math/, not LaTeX. Once
# paper LaTeX is drafted under a future post-prep workflow, the LaTeX path will
# also become an allowed value.
EXPECTED_SOURCE_FILES = {
    "apparatus": {
        "anti_loc/extracted_math/apparatus_master.md",
        "paper/apparatus/main.tex",
    },
    "closure": {
        "anti_loc/extracted_math/closure_master.md",
        "paper/closure/main.tex",
    },
    "dropped": {
        "anti_loc/extracted_math/apparatus_master.md",
        "paper/apparatus/main.tex",
        "anti_loc/extracted_math/closure_master.md",
        "paper/closure/main.tex",
    },
}
LEAN_DECL_RE = re.compile(r"^SixBirdsBSD(?:\.[A-Za-z0-9_']+){2,}$")


def rel(path: Path) -> str:
    return path.resolve().relative_to(ROOT).as_posix()


def load_yaml(path: Path) -> tuple[dict, list[str]]:
    errors: list[str] = []
    if not path.exists():
        return {}, [f"missing {rel(path)}"]
    try:
        data = yaml.safe_load(path.read_text(encoding="utf-8"))
    except yaml.YAMLError as exc:
        return {}, [f"{rel(path)}: YAML parse failed: {exc}"]
    if not isinstance(data, dict):
        errors.append(f"{rel(path)}: top-level YAML object must be a mapping")
        return {}, errors
    return data, errors


def load_toml(path: Path) -> tuple[dict, list[str]]:
    if not path.exists():
        return {}, [f"missing {rel(path)}"]
    try:
        with path.open("rb") as handle:
            data = tomllib.load(handle)
    except tomllib.TOMLDecodeError as exc:
        return {}, [f"{rel(path)}: TOML parse failed: {exc}"]
    if not isinstance(data, dict):
        return {}, [f"{rel(path)}: top-level TOML object must be a mapping"]
    return data, []


def manifest_entries(path: Path) -> tuple[list[dict], list[str]]:
    data, errors = load_toml(path)
    if errors:
        return [], errors
    entries: list[dict] = []
    for table in ("definition", "claim"):
        values = data.get(table, [])
        if not isinstance(values, list):
            errors.append(f"{rel(path)}: [[{table}]] table must parse as a list")
            continue
        for value in values:
            if not isinstance(value, dict):
                errors.append(f"{rel(path)}: [[{table}]] entry must be a table")
                continue
            entries.append(value)
    return entries, errors


def inventory_entries(path: Path) -> tuple[list[dict], list[str]]:
    data, errors = load_toml(path)
    if errors:
        return [], errors
    values = data.get("entry", [])
    if not isinstance(values, list):
        return [], [f"{rel(path)}: [[entry]] table must parse as a list"]
    entries: list[dict] = []
    for value in values:
        if not isinstance(value, dict):
            errors.append(f"{rel(path)}: [[entry]] entry must be a table")
            continue
        entries.append(value)
    return entries, errors


def check_schema(data: dict) -> list[str]:
    errors: list[str] = []
    missing = sorted(TOP_LEVEL_KEYS - set(data))
    if missing:
        errors.append(f"schema integrity: missing top-level keys: {', '.join(missing)}")
    rows = data.get("rows", [])
    if not isinstance(rows, list):
        errors.append("schema integrity: `rows` must be a list")
        return errors
    total_rows = data.get("total_rows")
    if total_rows != len(rows):
        errors.append(
            f"schema integrity: total_rows={total_rows!r} but len(rows)={len(rows)}"
        )
    labels: list[str] = []
    for index, row in enumerate(rows, start=1):
        if not isinstance(row, dict):
            errors.append(f"schema integrity: row #{index} must be a mapping")
            continue
        label = str(row.get("paper_label", f"<row #{index}>"))
        labels.append(label)
        row_missing = sorted(ROW_FIELDS - set(row))
        if row_missing:
            errors.append(
                f"schema integrity: row {label}: missing fields: {', '.join(row_missing)}"
            )
        null_fields = sorted(field for field in ROW_FIELDS if row.get(field) is None)
        if null_fields:
            errors.append(
                f"schema integrity: row {label}: null fields are not allowed: "
                f"{', '.join(null_fields)}"
            )
        if not isinstance(row.get("source_line"), int):
            errors.append(f"schema integrity: row {label}: source_line must be an integer")
    duplicate_labels = sorted(label for label, count in Counter(labels).items() if count > 1)
    if duplicate_labels:
        errors.append(
            f"schema integrity: duplicate paper_label values: {', '.join(duplicate_labels)}"
        )
    for bucket, field in COUNT_BUCKETS.items():
        counts = data.get(bucket)
        if not isinstance(counts, dict):
            errors.append(f"schema integrity: {bucket} must be a mapping")
            continue
        if sum(counts.values()) != total_rows:
            errors.append(
                f"schema integrity: {bucket} sums to {sum(counts.values())}, "
                f"expected total_rows={total_rows}"
            )
        actual = Counter(str(row.get(field, "")) for row in rows if isinstance(row, dict))
        expected = Counter({str(key): int(value) for key, value in counts.items()})
        if actual != expected:
            errors.append(
                f"schema integrity: {bucket} does not match row data "
                f"(expected {dict(expected)}, actual {dict(actual)})"
            )
    return errors


def check_field_values(rows: list[dict]) -> list[str]:
    errors: list[str] = []
    checks = [
        ("target_paper", ALLOWED_TARGET_PAPERS),
        ("target_destination", ALLOWED_DESTINATIONS),
        ("proof_presentation", ALLOWED_PROOF_PRESENTATIONS),
        ("lean_coverage", ALLOWED_LEAN_COVERAGE),
        ("semantic_alignment", ALLOWED_SEMANTIC_ALIGNMENT),
    ]
    for row in rows:
        label = str(row.get("paper_label", "<unlabeled>"))
        for field, allowed in checks:
            value = row.get(field)
            if value not in allowed:
                errors.append(
                    f"field value sets: row {label}: invalid {field}={value!r} "
                    f"(allowed: {sorted(allowed)})"
                )
    return errors


def check_cross_row_invariants(rows: list[dict]) -> list[str]:
    """Validate per-row cross-field invariants.

    Coverages that do NOT require a `lean_decl`:
    - `not_mechanized`: nonclaim metadata, no Lean entry.
    - `obligation`: manifest-only obligation.

    Coverages that DO require a non-empty `lean_decl`:
    - `theorem`, `partial`, `definition`, `recognition_source`.
    """
    EMPTY_DECL_COVERAGES = {"not_mechanized", "obligation"}
    NON_LEAN_DECL_COVERAGES = EMPTY_DECL_COVERAGES  # alias for clarity
    errors: list[str] = []
    for row in rows:
        label = str(row.get("paper_label", "<unlabeled>"))
        target_paper = row.get("target_paper")
        target_destination = row.get("target_destination")
        # `target_paper == 'dropped'` requires `target_destination ==
        # 'source_only'` but NOT vice versa: a row may live in
        # `source_only` while remaining a valid axis target_paper.
        if target_paper == "dropped" and target_destination != "source_only":
            errors.append(
                f"cross-row invariants: row {label}: target_paper='dropped' "
                "requires target_destination='source_only'"
            )
        lean_coverage = row.get("lean_coverage")
        lean_decl = row.get("lean_decl")
        if (lean_coverage in EMPTY_DECL_COVERAGES) != (lean_decl == ""):
            errors.append(
                f"cross-row invariants: row {label}: lean_coverage in "
                f"{sorted(EMPTY_DECL_COVERAGES)} iff lean_decl is empty failed"
            )
        if lean_coverage not in NON_LEAN_DECL_COVERAGES:
            if not lean_decl:
                errors.append(
                    f"cross-row invariants: row {label}: lean-bound row has empty lean_decl"
                )
            elif not isinstance(lean_decl, str) or not LEAN_DECL_RE.match(lean_decl):
                errors.append(
                    f"cross-row invariants: row {label}: lean_decl {lean_decl!r} "
                    "does not match SixBirdsBSD.<...>.<...>"
                )
    return errors


def labels_by_path(entries_by_path: dict[str, list[dict]]) -> dict[str, dict]:
    out: dict[str, dict] = {}
    for source, entries in entries_by_path.items():
        for entry in entries:
            label = entry.get("paper_label")
            if not isinstance(label, str) or not label:
                continue
            if label in out:
                out[label]["_duplicate_sources"].append(source)
            else:
                copied = dict(entry)
                copied["_source"] = source
                copied["_duplicate_sources"] = [source]
                out[label] = copied
    return out


def check_manifest_consistency(rows: list[dict], manifests: dict[str, list[dict]]) -> list[str]:
    errors: list[str] = []
    manifest_by_label = labels_by_path(manifests)
    for label, entry in manifest_by_label.items():
        if len(entry["_duplicate_sources"]) > 1:
            errors.append(
                f"manifest consistency: duplicate manifest paper_label {label!r} in "
                f"{', '.join(entry['_duplicate_sources'])}"
            )
    rows_by_label = {str(row["paper_label"]): row for row in rows}
    # The `recognition_source` and `obligation` coverages are intentionally
    # not represented as manifest entries — the recognition source is a typed
    # carrier but is not a definition/claim entry, and obligations are
    # manifest-only metadata tracked at the inventory level. Skip
    # manifest-consistency for these.
    NON_MANIFEST_COVERAGE = {"not_mechanized", "recognition_source", "obligation"}
    for row in rows:
        label = str(row["paper_label"])
        if row["lean_coverage"] in NON_MANIFEST_COVERAGE:
            continue
        manifest = manifest_by_label.get(label)
        if manifest is None:
            errors.append(
                f"manifest consistency: YAML mechanized row {label!r} has no manifest entry"
            )
            continue
        if manifest.get("lean_decl") != row["lean_decl"]:
            errors.append(
                f"manifest consistency: row {label}: lean_decl mismatch "
                f"(YAML {row['lean_decl']!r}, manifest {manifest.get('lean_decl')!r})"
            )
        if manifest.get("status") != row["lean_coverage"]:
            errors.append(
                f"manifest consistency: row {label}: status mismatch "
                f"(YAML {row['lean_coverage']!r}, manifest {manifest.get('status')!r})"
            )
    for label in sorted(manifest_by_label):
        if label not in rows_by_label:
            errors.append(
                f"manifest consistency: manifest paper_label {label!r} is missing from YAML"
            )
    return errors


def check_inventory_consistency(rows: list[dict], inventories: dict[str, list[dict]]) -> list[str]:
    errors: list[str] = []
    inventory_by_label = labels_by_path(inventories)
    for label, entry in inventory_by_label.items():
        if len(entry["_duplicate_sources"]) > 1:
            errors.append(
                f"inventory consistency: duplicate inventory paper_label {label!r} in "
                f"{', '.join(entry['_duplicate_sources'])}"
            )
    row_labels = {str(row["paper_label"]) for row in rows}
    inventory_labels = set(inventory_by_label)
    missing_inventory = sorted(row_labels - inventory_labels)
    for label in missing_inventory:
        errors.append(
            f"inventory consistency: YAML row {label!r} is missing from paper inventories"
        )
    missing_yaml = sorted(inventory_labels - row_labels)
    for label in missing_yaml:
        errors.append(
            f"inventory consistency: inventory paper_label {label!r} is missing from YAML"
        )
    return errors


def check_source_line_sanity(rows: list[dict]) -> list[str]:
    errors: list[str] = []
    for row in rows:
        label = str(row.get("paper_label", "<unlabeled>"))
        target_paper = str(row.get("target_paper", ""))
        expected_source = EXPECTED_SOURCE_FILES.get(target_paper)
        if expected_source is None:
            continue
        source_file = str(row.get("source_file") or "")
        # Accept the curated allowlist (math artifact / main.tex) or any file
        # in the modular paper tree (sections/ + appendices/) for the row's
        # target paper(s).
        axes = ["apparatus", "closure"] if target_paper == "dropped" else [target_paper]
        in_paper_tree = any(source_file.startswith(f"paper/{a}/") for a in axes)
        if source_file not in expected_source and not in_paper_tree:
            errors.append(
                f"source sanity: row {label}: source_file={source_file!r}, "
                f"expected the math artifact, main.tex, or a paper/{target_paper}/ "
                f"section/appendix file"
            )
        source_line = row.get("source_line")
        env_kind = str(row.get("env_kind", ""))
        # Nonclaim rows are inventory-metadata-only; they describe scope-fence
        # discipline and have no positional source line in the math artifact.
        # All other rows must have a positive integer source_line.
        if env_kind == "nonclaim":
            if not isinstance(source_line, int) or source_line < 0:
                errors.append(
                    f"source sanity: row {label}: source_line must be a non-negative "
                    f"integer for nonclaim rows (got {source_line!r})"
                )
        else:
            if not isinstance(source_line, int) or source_line <= 0:
                errors.append(
                    f"source sanity: row {label}: source_line must be a positive integer "
                    f"(got {source_line!r})"
                )
    return errors


def run_check() -> tuple[list[str], dict[str, object]]:
    errors: list[str] = []
    data, yaml_errors = load_yaml(STATEMENTS)
    errors.extend(yaml_errors)
    if errors:
        return errors, {}

    rows = data.get("rows", [])
    if not isinstance(rows, list):
        rows = []

    errors.extend(check_schema(data))
    if all(isinstance(row, dict) for row in rows):
        errors.extend(check_field_values(rows))
        errors.extend(check_cross_row_invariants(rows))
        errors.extend(check_source_line_sanity(rows))

    manifests: dict[str, list[dict]] = {}
    inventories: dict[str, list[dict]] = {}
    for axis, path in MANIFESTS.items():
        entries, manifest_errors = manifest_entries(path)
        manifests[axis] = entries
        errors.extend(manifest_errors)
    for axis, path in INVENTORIES.items():
        entries, inventory_errors = inventory_entries(path)
        inventories[axis] = entries
        errors.extend(inventory_errors)

    if all(isinstance(row, dict) for row in rows):
        errors.extend(check_manifest_consistency(rows, manifests))
        errors.extend(check_inventory_consistency(rows, inventories))

    summary = {
        "rows": rows,
        "manifests": manifests,
        "inventories": inventories,
    }
    return errors, summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="(accepted for consistency with other BSD validators; same behavior as default)",
    )
    parser.parse_args()

    errors, summary = run_check()
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1

    rows: list[dict] = summary["rows"]  # type: ignore[assignment]
    manifests: dict[str, list[dict]] = summary["manifests"]  # type: ignore[assignment]
    inventories: dict[str, list[dict]] = summary["inventories"]  # type: ignore[assignment]
    target_counts = Counter(str(row["target_paper"]) for row in rows)
    mechanized = sum(1 for row in rows if row["lean_coverage"] != "not_mechanized")
    not_mechanized = sum(1 for row in rows if row["lean_coverage"] == "not_mechanized")

    print("statements-of-record.yml check passed:")
    target_summary = ", ".join(
        f"{paper}:{target_counts[paper]}"
        for paper in sorted(ALLOWED_TARGET_PAPERS)
    )
    print(
        "  rows={rows}, target_paper={{{targets}}}, mechanized={mechanized}, "
        "not_mechanized={not_mechanized}".format(
            rows=len(rows),
            targets=target_summary,
            mechanized=mechanized,
            not_mechanized=not_mechanized,
        )
    )
    print(
        "  manifest cross-check: "
        + ", ".join(f"{axis}={len(manifests[axis])}" for axis in sorted(manifests))
        + " (matches)"
    )
    print(
        "  inventory cross-check: "
        + ", ".join(f"{axis}={len(inventories[axis])}" for axis in sorted(inventories))
        + " (matches)"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
