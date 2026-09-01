#!/usr/bin/env python3
"""Seed paper/notes/statements-of-record.yml from the per-axis paper inventories.

Emits the pre-mechanization statements-of-record registry: one row per
inventory label, all at `lean_coverage = not_mechanized` (nothing is in Lean
yet), `lean_decl = ""`, `semantic_alignment = not_applicable`. As declarations
are accepted, rows are updated by hand (bump
lean_coverage → definition/theorem/partial, fill lean_decl, set
semantic_alignment, and add the matching manifest entry).

This is a one-time seed/refresh tool for the PRE-mechanization state; it is not
part of the validator chain (scripts/check_statements_of_record.py validates the
committed file). Re-running it overwrites manual per-row updates, so only run it
before mechanization begins on an axis.

Usage:
  python3 scripts/build_statements_of_record.py            # write the file
  python3 scripts/build_statements_of_record.py --check    # diff against committed
"""

from __future__ import annotations

import argparse
import sys
from collections import Counter
from pathlib import Path

try:  # Python 3.11+
    import tomllib  # type: ignore[import-not-found]
except ModuleNotFoundError:  # 3.10 image
    import tomli as tomllib  # type: ignore[no-redef]

ROOT = Path(__file__).resolve().parents[1]
INVENTORY_DIR = ROOT / "formalization" / "inventory"
STATEMENTS = ROOT / "paper" / "notes" / "statements-of-record.yml"

AXES = ["apparatus", "closure"]
INVENTORIES = {a: INVENTORY_DIR / f"{a}_paper_inventory.toml" for a in AXES}
MANIFESTS = {a: ROOT / "lean" / "manifests" / f"{a}_manifest.toml" for a in AXES}
SCHEMA_VERSION = 1

# manifest status -> SoR lean_coverage
COVERAGE_FROM_STATUS = {
    "definition": "definition",
    "theorem": "theorem",
    "partial": "partial",
    "unformalized": "not_mechanized",
}
# Labels whose Lean realization is a typed recognition-source carrier: the
# `structure` is a real Lean definition (manifest status `definition`), but the
# SoR discloses it as `recognition_source` coverage because its arithmetic
# `Prop` content is a carried hypothesis, not a derivation (see the closure
# axis master, intended_status summary).
RECOGNITION_SOURCE_LABELS: set[str] = {
    "def:closure:gamma-padic-descent",
    "def:closure:gamma-sha-persistence",
    "def:closure:gamma-higher-gz-fixity",
}

# Per-label semantic_alignment override (default "faithful" for mechanized
# rows; set here when a reviewed row is narrowed/projection-packaged/etc.).
SEMANTIC_ALIGNMENT_OVERRIDES: dict[str, str] = {
    # The exterior-product relations (J_i^2=0, anticommutativity) are
    # represented structurally (2^r coordinate space + wedge→J12), not
    # fully axiomatized; the dim/calibration content is faithful.
    "def:apparatus:vsrc-algebra": "narrowed_surrogate",
    "thm:apparatus:vsrc-stage-i-consistency": "narrowed_surrogate",
    # Closure axis — recognition-source carriers: the typed structure is a
    # narrowed surrogate for the full arithmetic recognition source (the
    # Prop content is a hypothesis, not derived).
    "def:closure:gamma-padic-descent": "narrowed_surrogate",
    "def:closure:gamma-sha-persistence": "narrowed_surrogate",
    "def:closure:gamma-higher-gz-fixity": "narrowed_surrogate",
    # Closure axis — conditional theorems that project their conclusion from
    # carried import / combinator hypotheses (deep arithmetic imported, not
    # derived): disclose as projection_packaged, never silently faithful.
    "thm:closure:chi-ct-p-comparison": "projection_packaged",
    "thm:closure:oc-eta-formula": "projection_packaged",
    "thm:closure:t-cascade-rank-le-1": "projection_packaged",
    "thm:closure:strong-bsd-conditional": "projection_packaged",
    # composite-signature projects the Stage-6 trace + Stage-5 hardening from
    # the shell/gamma records; disclose as projection_packaged (not faithful).
    "thm:closure:composite-signature": "projection_packaged",
    # Closure axis — AOR membership is the local syntactic RefStableAOR
    # predicate, a narrowed surrogate for the full TsiokosAOR2026 meta-theory.
    "thm:closure:aor-instance": "narrowed_surrogate",
}


def target_destination(intended_status: str) -> str:
    return "body" if intended_status == "mechanize_now" else "appendix"


def proof_presentation(kind: str, intended_status: str) -> str:
    if intended_status != "mechanize_now":
        return "appendix_only"
    if kind == "definition":
        return "definition_entry"
    return "lean_substantive"


def short_name(label: str) -> str:
    parts = label.split(":")
    return parts[-1] if parts else label


def load_entries(path: Path) -> list[dict]:
    if not path.exists():
        return []
    with path.open("rb") as handle:
        data = tomllib.load(handle)
    entries = data.get("entry", [])
    return [e for e in entries if isinstance(e, dict)]


def load_manifest(path: Path) -> dict[str, dict]:
    """label -> {status, lean_decl} from a manifest's [[definition]]/[[claim]] tables."""
    if not path.exists():
        return {}
    with path.open("rb") as handle:
        data = tomllib.load(handle)
    out: dict[str, dict] = {}
    for table in ("definition", "claim"):
        for e in data.get(table, []):
            if isinstance(e, dict) and e.get("paper_label"):
                out[str(e["paper_label"])] = {
                    "status": str(e.get("status", "")),
                    "lean_decl": str(e.get("lean_decl", "")),
                }
    return out


# Map the inventory `section` (Lean-module leaf name) to the paper section
# label used by the modular sections/sec_NN_*.tex scaffold. `target_section_hint`
# carries the paper-side sec: label (scripts/paper_lint.sh matches it against each
# section file's \label{sec:...}); `section`/`source_section` stay the Lean leaf
# (keyed by section_module_map.toml / check_manifests).
SECTION_LABELS: dict[str, dict[str, str]] = {
    "apparatus": {
        "Decomposition": "sec:decomposition",
        "HeightRegulator": "sec:height-regulator",
        "AnalyticPeriod": "sec:analytic-period",
        "FiniteSource": "sec:finite-source",
        "PAdic": "sec:p-adic",
        "DetAssembly": "sec:det-assembly",
        "Comparison": "sec:comparison",
        "HigherRankNoGo": "sec:higher-rank-no-go",
        "GlobalAuditNoGo": "sec:global-audit-no-go",
        "SupportPrimeNoGo": "sec:support-prime-no-go",
        "Vsrc": "sec:vsrc",
        "KappaNormalization": "sec:kappa-normalization",
    },
    "closure": {
        "Imports": "sec:imports",
        "RecognitionSources": "sec:recognition-sources",
        "SelShell": "sec:shell-readout",
        "ChiCTp": "sec:chi-ct-p",
        "EtaFormula": "sec:eta-formula",
        "TCascade": "sec:t-cascade",
        "Obstructions": "sec:obstructions",
        "Landing": "sec:landing",
        "AORInstance": "sec:aor-instance",
    },
}


def build_rows() -> list[dict]:
    rows: list[dict] = []
    for axis in AXES:
        manifest = load_manifest(MANIFESTS[axis])
        for e in load_entries(INVENTORIES[axis]):
            label = str(e["paper_label"])
            kind = str(e["kind"])
            section = str(e.get("section", "<unknown>"))
            status = str(e.get("intended_status", "mechanize_now"))
            # Default pre-mechanization state.
            lean_coverage = "not_mechanized"
            lean_decl = ""
            semantic_alignment = "not_applicable"
            # If the label has been mechanized, reflect the manifest entry.
            m = manifest.get(label)
            if m is not None:
                cov = COVERAGE_FROM_STATUS.get(m["status"], "not_mechanized")
                # Recognition-source carriers are Lean definitions in the
                # manifest, but the SoR records them as recognition_source.
                if cov == "definition" and label in RECOGNITION_SOURCE_LABELS:
                    cov = "recognition_source"
                if cov != "not_mechanized" and m["lean_decl"]:
                    lean_coverage = cov
                    lean_decl = m["lean_decl"]
                    semantic_alignment = SEMANTIC_ALIGNMENT_OVERRIDES.get(label, "faithful")
            rows.append(
                {
                    "paper_label": label,
                    "env_kind": kind,
                    "source_file": str(e.get("source_file", "")),
                    "source_line": int(e.get("line_start", 0)),
                    "source_section": section,
                    "theorem_title": short_name(label),
                    "target_paper": axis,
                    "target_destination": target_destination(status),
                    "target_section_hint": SECTION_LABELS.get(axis, {}).get(section, section),
                    "proof_presentation": proof_presentation(kind, status),
                    "lean_coverage": lean_coverage,
                    "lean_decl": lean_decl,
                    "semantic_alignment": semantic_alignment,
                    "notes": "",
                }
            )
    return rows


def yaml_str(value: str) -> str:
    # Always quote to keep colons / special chars safe.
    return '"' + value.replace("\\", "\\\\").replace('"', '\\"') + '"'


def render(rows: list[dict]) -> str:
    def counts(field: str) -> Counter:
        return Counter(str(r[field]) for r in rows)

    lines: list[str] = []
    lines.append("# Statements-of-record registry (generated seed; see")
    lines.append("# scripts/build_statements_of_record.py). One row per paper-inventory")
    lines.append("# label. top-level status: pre_mechanization | in_progress | current")
    lines.append("# (current = every mechanize_now label is mechanized).")
    mechanized = any(r["lean_coverage"] != "not_mechanized" for r in rows)
    # A body-destined row is a mechanize_now label; "current" means every
    # such label is mechanized (the remaining not_mechanized rows are
    # support_only / nonclaim / obligation, intentionally not in Lean).
    pending = [
        r for r in rows
        if r["target_destination"] == "body" and r["lean_coverage"] == "not_mechanized"
    ]
    status = "pre_mechanization" if not mechanized else ("in_progress" if pending else "current")
    lines.append(f"schema_version: {SCHEMA_VERSION}")
    lines.append(f'status: "{status}"')
    lines.append(f"total_rows: {len(rows)}")
    for bucket, field in [
        ("target_paper_counts", "target_paper"),
        ("target_destination_counts", "target_destination"),
        ("proof_presentation_counts", "proof_presentation"),
        ("lean_coverage_counts", "lean_coverage"),
        ("semantic_alignment_counts", "semantic_alignment"),
    ]:
        lines.append(f"{bucket}:")
        for key, value in sorted(counts(field).items()):
            lines.append(f"  {key}: {value}")
    lines.append("rows:")
    for r in rows:
        lines.append(f"  - paper_label: {yaml_str(r['paper_label'])}")
        lines.append(f"    env_kind: {yaml_str(r['env_kind'])}")
        lines.append(f"    source_file: {yaml_str(r['source_file'])}")
        lines.append(f"    source_line: {r['source_line']}")
        lines.append(f"    source_section: {yaml_str(r['source_section'])}")
        lines.append(f"    theorem_title: {yaml_str(r['theorem_title'])}")
        lines.append(f"    target_paper: {yaml_str(r['target_paper'])}")
        lines.append(f"    target_destination: {yaml_str(r['target_destination'])}")
        lines.append(f"    target_section_hint: {yaml_str(r['target_section_hint'])}")
        lines.append(f"    proof_presentation: {yaml_str(r['proof_presentation'])}")
        lines.append(f"    lean_coverage: {yaml_str(r['lean_coverage'])}")
        lines.append(f"    lean_decl: {yaml_str(r['lean_decl'])}")
        lines.append(f"    semantic_alignment: {yaml_str(r['semantic_alignment'])}")
        lines.append(f"    notes: {yaml_str(r['notes'])}")
    return "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="diff against committed file")
    args = parser.parse_args()
    rows = build_rows()
    rendered = render(rows)
    if args.check:
        if not STATEMENTS.exists():
            print(f"ERROR: missing {STATEMENTS.relative_to(ROOT)}", file=sys.stderr)
            return 1
        if STATEMENTS.read_text(encoding="utf-8") != rendered:
            print(
                f"ERROR: {STATEMENTS.relative_to(ROOT)} differs from generated seed "
                "(expected if rows were hand-updated during Phase E)",
                file=sys.stderr,
            )
            return 1
        print("statements-of-record seed is current")
        return 0
    STATEMENTS.parent.mkdir(parents=True, exist_ok=True)
    STATEMENTS.write_text(rendered, encoding="utf-8")
    print(f"wrote {len(rows)} rows → {STATEMENTS.relative_to(ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
