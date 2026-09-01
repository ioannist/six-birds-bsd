#!/usr/bin/env python3
"""Build the per-axis BSD paper inventory TOMLs and mechanization queue CSVs.

Reads source_items.jsonl plus an inlined status mapping (curated below)
and emits, for each paper axis (apparatus, closure):
- formalization/inventory/<axis>_paper_inventory.toml
- formalization/traceability/queue_<axis>.csv

Run with `--check` to validate that the committed files match what
the script would generate (used by Phase A's seal step and any
downstream CI).

Status field allowlist:
  mechanize_now, obligation, out_of_scope_recognition_source,
  out_of_scope_meta, support_only, nonclaim
"""

from __future__ import annotations

import argparse
import csv
import io
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
INVENTORY_DIR = ROOT / "formalization" / "inventory"
TRACEABILITY_DIR = ROOT / "formalization" / "traceability"
SOURCE_ITEMS = INVENTORY_DIR / "source_items.jsonl"

AXES = ["apparatus", "closure"]
AXIS_TOML = {a: INVENTORY_DIR / f"{a}_paper_inventory.toml" for a in AXES}
AXIS_QUEUE = {a: TRACEABILITY_DIR / f"queue_{a}.csv" for a in AXES}


# Modular section-file stem → Lean-module leaf name, per axis. The leaf
# names are the keys of the [<axis>] table in
# lean/manifests/section_module_map.toml. With the modular paper tree
# (paper/<axis>/sections/sec_NN_<slug>.tex), a statement's section is its
# source file — robust to line-number shifts (no line ranges). Sections
# with no mechanized statements (intro/scope/discussion/conclusion) are
# absent here by design.
AXIS_SECTIONS: dict[str, dict[str, str]] = {
    "apparatus": {
        "sec_02_decomposition": "Decomposition",
        "sec_03_height_regulator": "HeightRegulator",
        "sec_04_analytic_period": "AnalyticPeriod",
        "sec_05_finite_source": "FiniteSource",
        "sec_06_p_adic": "PAdic",
        "sec_07_det_assembly": "DetAssembly",
        "sec_08_comparison": "Comparison",
        "sec_09_higher_rank_no_go": "HigherRankNoGo",
        "sec_10_global_audit_no_go": "GlobalAuditNoGo",
        "sec_11_support_prime_no_go": "SupportPrimeNoGo",
        "sec_12_vsrc": "Vsrc",
        "sec_13_kappa_normalization": "KappaNormalization",
    },
    "closure": {
        "sec_02_imports": "Imports",
        "sec_03_recognition_sources": "RecognitionSources",
        "sec_04_shell_readout": "SelShell",
        "sec_05_chi_ct_p": "ChiCTp",
        "sec_06_eta_formula": "EtaFormula",
        "sec_07_t_cascade": "TCascade",
        "sec_08_obstructions": "Obstructions",
        "sec_09_landing": "Landing",
        "sec_10_aor_instance": "AORInstance",
    },
}


# Curated intended_status per paper_label. Defaults applied by kind below for any
# label not listed here (def/thm/lem/prop/cor → mechanize_now; obligation →
# obligation; remark/warning/nonclaim → nonclaim). Overrides encode the
# support_only / out_of_scope_recognition_source intents recorded in the
# per-axis master artifacts (see anti_loc/extracted_math/*_master.md
# "intended_status summary"). Keyed by full paper_label (axis-qualified).
STATUS_OVERRIDES: dict[str, str] = {
    # Apparatus axis — five refined external transports (typed carriers in
    # Lean; never axioms).
    "obl:apparatus:rho-ht-reg-transport": "out_of_scope_recognition_source",
    "obl:apparatus:rho-an-period-transport": "out_of_scope_recognition_source",
    "obl:apparatus:rho-finite-transport": "out_of_scope_recognition_source",
    "obl:apparatus:rho-p-transport": "out_of_scope_recognition_source",
    "obl:apparatus:rho-det-assembly": "out_of_scope_recognition_source",
    # Apparatus axis — audit / ledger / interpretation items (not mechanized).
    "rmk:apparatus:five-column-literature-gap": "support_only",
    "rmk:apparatus:support-prime-atlas": "support_only",
    "rmk:apparatus:vsrc-no-licensed-descent": "support_only",
    "rmk:apparatus:vsrc-rank-r-stronger": "support_only",
    # Closure axis — typed no-gos (audit results) and audit/interpretation
    # remarks are recorded, not mechanized as derivations.
    "thm:closure:t-e12-no-go": "support_only",
    "thm:closure:t-bad-no-go": "support_only",
    "rmk:closure:mode-b-residuals": "support_only",
    "rmk:closure:aor-partial-status": "support_only",
}


def find_section(axis: str, source_file: str) -> str:
    stem = Path(source_file).stem
    return AXIS_SECTIONS.get(axis, {}).get(stem, "<unknown>")


def default_status(env_kind: str) -> str:
    if env_kind == "nonclaim":
        return "nonclaim"
    if env_kind == "remark":
        return "nonclaim"
    if env_kind == "warning":
        return "nonclaim"
    if env_kind == "obligation":
        return "obligation"
    return "mechanize_now"


def intended_status(label: str, env_kind: str) -> str:
    if label in STATUS_OVERRIDES:
        return STATUS_OVERRIDES[label]
    return default_status(env_kind)


def toml_string(value: str) -> str:
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


AXIS_PRETTY_NAMES = {
    "apparatus": "apparatus",
    "closure": "closure",
}


def render_toml(axis: str, entries: list[dict]) -> str:
    pretty = AXIS_PRETTY_NAMES.get(axis, axis)
    lines = [
        f"# Per-axis paper inventory for the {pretty} paper.",
        "# Generated by scripts/build_paper_inventories.py from source_items.jsonl.",
        "#",
        "# Schema (per entry):",
        f"#   paper_label    = \"<kind>:{axis}:<short-name>\"",
        "#   kind           = definition | theorem | lemma | proposition | corollary",
        "#                  | nonclaim | obligation | remark | warning",
        "#   section        = \"<section title verbatim>\"",
        "#   intended_status = mechanize_now | obligation | out_of_scope_recognition_source",
        "#                   | out_of_scope_meta | support_only | nonclaim",
        "#   required       = true | false",
        "#   line_start     = <int>",
        "#   line_end       = <int>",
        f"#   source_file    = \"anti_loc/extracted_math/{axis}_master.md\"",
        "#   statement_hash = \"<short hash>\"",
        "#   duplicate_of   = \"\"              # empty unless this row dedupes another",
        "",
    ]
    for entry in entries:
        lines.append("[[entry]]")
        lines.append(f"paper_label = {toml_string(entry['paper_label'])}")
        lines.append(f"kind = {toml_string(entry['kind'])}")
        lines.append(f"section = {toml_string(entry['section'])}")
        lines.append(f"intended_status = {toml_string(entry['intended_status'])}")
        lines.append(f"required = {'true' if entry['required'] else 'false'}")
        lines.append(f"line_start = {entry['line_start']}")
        lines.append(f"line_end = {entry['line_end']}")
        lines.append(f"source_file = {toml_string(entry['source_file'])}")
        lines.append(f"statement_hash = {toml_string(entry['statement_hash'])}")
        lines.append(f"duplicate_of = {toml_string('')}")
        lines.append("")
    return "\n".join(lines)


def write_toml(path: Path, axis: str, entries: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(render_toml(axis, entries), encoding="utf-8")


def render_queue(entries: list[dict]) -> str:
    queue_entries = [e for e in entries if e["intended_status"] == "mechanize_now"]
    buffer = io.StringIO()
    writer = csv.writer(buffer, lineterminator="\n")
    writer.writerow(["order", "paper_label", "kind", "section", "line_start", "source_file"])
    for order, entry in enumerate(queue_entries, start=1):
        writer.writerow(
            [
                order,
                entry["paper_label"],
                entry["kind"],
                entry["section"],
                entry["line_start"],
                entry["source_file"],
            ]
        )
    return buffer.getvalue()


def write_queue(path: Path, entries: list[dict]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(render_queue(entries), encoding="utf-8")


def collect_entries() -> dict[str, list[dict]]:
    """Group source_items records into per-axis entry lists keyed by paper_axis."""
    records = [
        json.loads(line)
        for line in SOURCE_ITEMS.read_text(encoding="utf-8").splitlines()
        if line.strip()
    ]
    per_axis: dict[str, list[dict]] = {a: [] for a in AXES}
    for record in sorted(records, key=lambda r: (r["paper_axis"], r["line_start"])):
        label = str(record["latex_label"])
        kind = str(record["env_kind"])
        axis = str(record["paper_axis"])
        line = int(record["line_start"])
        entry = {
            "paper_label": label,
            "kind": kind,
            "section": find_section(axis, str(record["source_file"])),
            "intended_status": intended_status(label, kind),
            "required": True,
            "line_start": line,
            "line_end": int(record["line_end"]),
            "source_file": str(record["source_file"]),
            "statement_hash": str(record["statement_hash"]),
        }
        per_axis.setdefault(axis, []).append(entry)
    return per_axis


def check() -> int:
    """Validate the committed inventory TOMLs and queue CSVs match what we
    would generate from the current source_items.jsonl."""
    errors: list[str] = []
    per_axis = collect_entries()
    for axis in AXES:
        entries = per_axis.get(axis, [])
        toml_path = AXIS_TOML[axis]
        queue_path = AXIS_QUEUE[axis]
        if not toml_path.exists():
            errors.append(f"missing {toml_path.relative_to(ROOT)}; rerun build_paper_inventories")
        elif toml_path.read_text(encoding="utf-8") != render_toml(axis, entries):
            errors.append(f"{toml_path.relative_to(ROOT)} is stale; rerun build_paper_inventories")
        if not queue_path.exists():
            errors.append(f"missing {queue_path.relative_to(ROOT)}; rerun build_paper_inventories")
        elif queue_path.read_text(encoding="utf-8") != render_queue(entries):
            errors.append(f"{queue_path.relative_to(ROOT)} is stale; rerun build_paper_inventories")
    # Surface any records whose paper_axis is not a known axis.
    for axis in sorted(set(per_axis) - set(AXES)):
        errors.append(f"source_items.jsonl has rows with unknown paper_axis {axis!r}")
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1
    print("paper inventories and queues are current")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--check",
        action="store_true",
        help="validate committed inventory TOMLs and queue CSVs against current source_items.jsonl",
    )
    args = parser.parse_args()
    if args.check:
        return check()

    per_axis = collect_entries()
    print("Status breakdown:")
    for axis in AXES:
        entries = per_axis.get(axis, [])
        write_toml(AXIS_TOML[axis], axis, entries)
        write_queue(AXIS_QUEUE[axis], entries)
        n_queue = sum(1 for e in entries if e["intended_status"] == "mechanize_now")
        print(f"wrote {len(entries)} {axis} entries → {AXIS_TOML[axis].relative_to(ROOT)}")
        print(f"wrote {axis} queue ({n_queue} items) → {AXIS_QUEUE[axis].relative_to(ROOT)}")
        counts: dict[str, int] = {}
        for e in entries:
            counts[e["intended_status"]] = counts.get(e["intended_status"], 0) + 1
        print(f"  {axis}: " + ", ".join(f"{k}={v}" for k, v in sorted(counts.items())))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
