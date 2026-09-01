#!/usr/bin/env python3
"""Build-check the repo-local BSD Lean project.

Adapted for six-birds-bsd from six-birds-math-usefulness'
check_sau_lean.py. Runs:

1. Structural prechecks: required files exist; no forbidden Lean
   tokens (sorry, admit, axiom, opaque, constant); no external path
   references in active source files.
2. Phase A python validators chain: extract inventory, audit
   foundations deps (skip-validation/skip-probe by default), check
   provenance, semantic alignment, paper inventories,
   imported-foundations canary.
3. `lake build` in `lean/`.

Use --skip-prechecks to run only the lake build (e.g. inside a
top-level verifier). Use --skip-build to run only the prechecks
(e.g. when `lake` isn't available in PATH).
"""

from __future__ import annotations

import argparse
import re
import shutil
import subprocess
import sys
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
LEAN_DIR = ROOT / "lean"
VENDOR_DIR = ROOT / "vendor" / "foundations"

STATIC_BUILD_ARTIFACTS = (
    LEAN_DIR / ".lake",
    LEAN_DIR / "lake-manifest.json",
    VENDOR_DIR / "six-birds-theory" / "formal" / ".lake",
    VENDOR_DIR / "six-birds-theory" / "formal" / "lake-manifest.json",
    VENDOR_DIR / "six-birds-foundations-ii" / "lean" / "full" / ".lake",
    VENDOR_DIR / "six-birds-foundations-ii" / "lean" / "full" / "lake-manifest.json",
    VENDOR_DIR / "six-birds-foundations-iii" / "lean" / "full" / ".lake",
    VENDOR_DIR / "six-birds-foundations-iii" / "lean" / "full" / "lake-manifest.json",
)
FORBIDDEN_LEAN_TOKENS = re.compile(r"\b(sorry|admit|axiom|opaque|constant)\b")
FORBIDDEN_EXTERNAL_REFS = (
    "../" + "six-birds-",
    "/home" + "/repos/",
)


def rel(path: Path) -> str:
    return path.resolve().relative_to(ROOT).as_posix()


def run(command: list[str], *, cwd: Path) -> tuple[int, str]:
    result = subprocess.run(
        command,
        cwd=cwd,
        text=True,
        stdout=subprocess.PIPE,
        stderr=subprocess.STDOUT,
    )
    return result.returncode, result.stdout


def build_artifacts() -> list[Path]:
    artifacts = list(STATIC_BUILD_ARTIFACTS)
    artifacts.extend(LEAN_DIR.glob("**/*.olean"))
    artifacts.extend(LEAN_DIR.glob("**/*.ilean"))
    return sorted({path for path in artifacts if path.exists()})


def cleanup() -> None:
    for artifact in build_artifacts():
        if artifact.is_dir():
            shutil.rmtree(artifact)
        elif artifact.exists():
            artifact.unlink()


REQUIRED_FILES = [
    LEAN_DIR / "lean-toolchain",
    LEAN_DIR / "lakefile.toml",
    LEAN_DIR / "README.md",
    LEAN_DIR / "SixBirdsBSD.lean",
    LEAN_DIR / "SixBirdsBSD" / "ImportedFoundations.lean",
    LEAN_DIR / "SixBirdsBSD" / "FoundationsICompat.lean",
    LEAN_DIR / "SixBirdsBSD" / "Terminology.lean",
    LEAN_DIR / "SixBirdsBSD" / "Apparatus.lean",
    LEAN_DIR / "SixBirdsBSD" / "Closure.lean",
]
# Per-section module files are not in REQUIRED_FILES. The
# manifest-validator (scripts/check_manifests.py) verifies that every
# manifest entry's lean_module file exists.


def check_required_files() -> list[str]:
    return [f"missing {rel(path)}" for path in REQUIRED_FILES if not path.exists()]


def lean_source_files() -> list[Path]:
    files: list[Path] = []
    files.extend(sorted((LEAN_DIR / "SixBirdsBSD").rglob("*.lean")))
    files.append(LEAN_DIR / "SixBirdsBSD.lean")
    return [path for path in files if path.exists()]


def active_source_files() -> list[Path]:
    files = lean_source_files() + [
        LEAN_DIR / "lakefile.toml",
        LEAN_DIR / "lean-toolchain",
        ROOT / "scripts" / "check_lean.py",
        ROOT / "scripts" / "extract_latex_inventory.py",
        ROOT / "scripts" / "audit_foundations_dependencies.py",
        ROOT / "scripts" / "check_foundations_provenance.py",
        ROOT / "scripts" / "check_semantic_alignment.py",
        ROOT / "scripts" / "build_paper_inventories.py",
        ROOT / "scripts" / "generate_imported_foundations.py",
        ROOT / "scripts" / "check_manifests.py",
        ROOT / "scripts" / "test_check_manifests.py",
        LEAN_DIR / "manifests" / "section_module_map.toml",
    ]
    return [path for path in files if path.exists()]


BLOCK_COMMENT_RE = re.compile(r"/-.*?-/", re.DOTALL)


def mask_lean_comments(text: str) -> str:
    """Mask Lean comments so token scans skip prose.

    Non-newline characters inside `/- ... -/` block comments (including
    `/-! ... -/` doc comments) become spaces so line/column positions
    are preserved for error reporting. Line comments (`-- ...`) are
    stripped per-line by the caller.

    The regex is non-nested. Lean supports nested block comments, but
    for the validator's purpose a nested block containing a forbidden
    token will still be flagged — that's a conservative false positive
    we accept.
    """
    def _mask(match: re.Match[str]) -> str:
        return "".join(ch if ch == "\n" else " " for ch in match.group(0))
    return BLOCK_COMMENT_RE.sub(_mask, text)


def check_no_forbidden_lean_tokens() -> list[str]:
    errors: list[str] = []
    for path in lean_source_files():
        raw = path.read_text(encoding="utf-8")
        masked = mask_lean_comments(raw)
        for lineno, line in enumerate(masked.splitlines(), start=1):
            stripped = line.split("--", 1)[0]
            match = FORBIDDEN_LEAN_TOKENS.search(stripped)
            if match:
                errors.append(f"{rel(path)}:{lineno}: forbidden Lean token `{match.group(1)}`")
    return errors


def check_no_external_refs() -> list[str]:
    errors: list[str] = []
    for path in active_source_files():
        text = path.read_text(encoding="utf-8")
        for ref in FORBIDDEN_EXTERNAL_REFS:
            if ref in text:
                errors.append(f"{rel(path)} contains forbidden external reference `{ref}`")
    return errors


# Lean files whose namespace declaration deliberately differs from their
# file-path-derived name. The alignment trio declares aliases in the
# umbrella `SixBirdsBSD` namespace (matching SAU's pattern). Umbrella
# files (top-level + axis umbrella + ImportedFoundations) have no
# namespace declaration; they are import-only.
_UMBRELLA_NAMESPACE_FILES = {
    "SixBirdsBSD/FoundationsICompat.lean": "SixBirdsBSD",
    "SixBirdsBSD/Terminology.lean": "SixBirdsBSD",
}
_NO_NAMESPACE_FILES = {
    "SixBirdsBSD.lean",
    "SixBirdsBSD/Apparatus.lean",
    "SixBirdsBSD/Closure.lean",
    "SixBirdsBSD/ImportedFoundations.lean",
}
_NAMESPACE_RE = re.compile(r"^\s*namespace\s+(\S+)\s*$", re.MULTILINE)
_END_RE = re.compile(r"^\s*end\s+(\S+)\s*$", re.MULTILINE)


def _file_path_namespace(rel_path: str) -> str:
    """Derive the expected namespace from a `SixBirdsBSD/...` relative path."""
    without_ext = rel_path[: -len(".lean")] if rel_path.endswith(".lean") else rel_path
    return without_ext.replace("/", ".")


def check_lean_namespaces() -> list[str]:
    """Each Lean module under lean/SixBirdsBSD/ must declare a namespace
    matching its file path, or be one of the documented exceptions
    (umbrella imports / alignment-trio alias hubs)."""
    errors: list[str] = []
    for path in lean_source_files():
        rel_to_lean = path.resolve().relative_to(LEAN_DIR).as_posix()
        text = path.read_text(encoding="utf-8")
        ns_decls = _NAMESPACE_RE.findall(text)
        end_decls = _END_RE.findall(text)

        if rel_to_lean in _NO_NAMESPACE_FILES:
            if ns_decls or end_decls:
                errors.append(
                    f"{rel(path)}: umbrella file must have no `namespace` / `end` declaration "
                    f"(got namespaces={ns_decls}, ends={end_decls})"
                )
            continue

        expected = _UMBRELLA_NAMESPACE_FILES.get(rel_to_lean) or _file_path_namespace(rel_to_lean)
        if expected not in ns_decls:
            errors.append(
                f"{rel(path)}: expected `namespace {expected}` declaration "
                f"(got {ns_decls})"
            )
        if expected not in end_decls:
            errors.append(
                f"{rel(path)}: expected matching `end {expected}` declaration "
                f"(got {end_decls})"
            )
        if len(ns_decls) > 1 or len(end_decls) > 1:
            errors.append(
                f"{rel(path)}: multiple namespace/end pairs not supported "
                f"(namespaces={ns_decls}, ends={end_decls})"
            )
    return errors


def validator_chain(skip_probe: bool) -> list[list[str]]:
    """Phase A + Phase C validators, in chain order.

    `skip_probe` is forwarded only to validators that accept it (audit
    foundations deps, check manifests). The other validators are
    probe-free.
    """
    audit_args = ["scripts/audit_foundations_dependencies.py", "--check", "--skip-validation"]
    if skip_probe:
        audit_args.append("--skip-probe")
    manifests_args = ["scripts/check_manifests.py", "--check"]
    if skip_probe:
        manifests_args.append("--skip-probe")
    # The LaTeX-extraction validators (extract_latex_inventory,
    # build_paper_inventories) are needles-leftover tooling that
    # presumes inventory is derived from .tex sources. This project
    # populates the inventory directly from markdown math artifacts
    # in anti_loc/extracted_math/, so those validators are not
    # invoked here. The inventory + queue + section_module_map are
    # validated by check_manifests.
    return [
        audit_args,
        ["scripts/check_foundations_provenance.py", "--check"],
        ["scripts/check_semantic_alignment.py", "--check"],
        ["scripts/generate_imported_foundations.py", "--check"],
        manifests_args,
    ]


def run_validator_chain(skip_probe: bool) -> int:
    for args in validator_chain(skip_probe):
        code, output = run([sys.executable] + args, cwd=ROOT)
        if code != 0:
            print(output, end="")
            return code
    return 0


def check(
    *, clean: bool, skip_prechecks: bool, skip_build: bool, skip_probe: bool
) -> int:
    errors = check_required_files()
    errors.extend(check_no_forbidden_lean_tokens())
    errors.extend(check_no_external_refs())
    errors.extend(check_lean_namespaces())
    if errors:
        for error in errors:
            print(f"ERROR: {error}", file=sys.stderr)
        return 1

    if not skip_prechecks:
        # If --skip-build is set we assume no Lean toolchain; force --skip-probe
        # too so the validator chain doesn't try to invoke `lake`.
        effective_skip_probe = skip_probe or skip_build
        code = run_validator_chain(effective_skip_probe)
        if code != 0:
            return code

    if not skip_build:
        code, output = run(["lake", "build"], cwd=LEAN_DIR)
        print(output, end="")
        if clean:
            cleanup()
            remaining = build_artifacts()
            if remaining:
                for artifact in remaining:
                    print(f"ERROR: cleanup left build artifact {rel(artifact)}", file=sys.stderr)
                return 1
        if code != 0:
            return code

    print("BSD Lean build passed" if not skip_build else "BSD Lean prechecks passed")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--cleanup", action="store_true", help="remove local Lake build artifacts after checking")
    parser.add_argument(
        "--skip-prechecks",
        action="store_true",
        help="skip the Phase A+C python validator chain (run only structural checks + lake build)",
    )
    parser.add_argument(
        "--skip-build",
        action="store_true",
        help="skip `lake build` (useful when the Lean toolchain isn't installed). Implies --skip-probe.",
    )
    parser.add_argument(
        "--skip-probe",
        action="store_true",
        help="forward to audit and manifest validators: skip lake env lean probes",
    )
    args = parser.parse_args()
    return check(
        clean=args.cleanup,
        skip_prechecks=args.skip_prechecks,
        skip_build=args.skip_build,
        skip_probe=args.skip_probe,
    )


if __name__ == "__main__":
    raise SystemExit(main())
