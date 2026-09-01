#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

FAILURES=0

warn() {
  printf 'WARN: %s\n' "$*" >&2
}

error() {
  printf 'ERROR: %s\n' "$*" >&2
  FAILURES=$((FAILURES + 1))
}

die() {
  error "$*"
  exit 1
}

usage() {
  printf 'usage: scripts/paper_lint.sh paper/<paper>\n' >&2
}

record_grep_failures() {
  local file="$1"
  local description="$2"
  local pattern="$3"
  local hits

  hits="$(grep -nE "$pattern" "$file" || true)"
  if [[ -n "$hits" ]]; then
    error "$description in $file:"
    printf '%s\n' "$hits" >&2
  fi
}

section_files() {
  find "$PAPER_DIR/sections" -maxdepth 1 -type f -name '*.tex' | sort
}

check_argument() {
  if [[ $# -ne 1 ]]; then
    usage
    exit 1
  fi

  PAPER_DIR="${1%/}"
  if [[ ! -d "$PAPER_DIR" ]]; then
    die "paper directory does not exist: $PAPER_DIR"
  fi
}

check_structure() {
  if [[ ! -f "$PAPER_DIR/main.tex" ]]; then
    error "missing required file: $PAPER_DIR/main.tex"
  fi

  local required_dirs=(sections appendices tables figures includes)
  local dir
  for dir in "${required_dirs[@]}"; do
    if [[ ! -d "$PAPER_DIR/$dir" ]]; then
      error "missing required directory: $PAPER_DIR/$dir"
    fi
  done
}

check_body_prose_tokens() {
  local file
  local body
  local hits

  while IFS= read -r file; do
    # "Body prose" = the section text with comment lines AND \footnote{...} spans
    # removed. Under the companion form (paper/notes/proof-presentation-policy.md)
    # the per-theorem Lean-decl disclosure lives in footnotes (and App D, which is
    # in appendices/ and not linted here); those are the sanctioned channel, so
    # they are exempt from the body-prose token rules below. The perl pass strips
    # \footnote{...} with one level of brace nesting (e.g. \footnote{... \texttt{decl}}).
    body="$(perl -0777 -pe 's/\\footnote\{(?:[^{}]|\{[^{}]*\})*\}//g' "$file" 2>/dev/null | grep -nEv '^[[:space:]]*%' || true)"

    hits="$(printf '%s\n' "$body" | grep -E 'SixBirdsBSD\.[A-Za-z0-9_.'\''`]+\.[A-Za-z0-9_.'\''`]+' || true)"
    if [[ -n "$hits" ]]; then
      error "forbidden Lean module identifier in body prose: $file"
      printf '%s\n' "$hits" >&2
    fi

    hits="$(printf '%s\n' "$body" | grep -E '\.jsonl?\b' | grep -Ev '\\path\{[^}]*\.jsonl?[^}]*\}' || true)"
    if [[ -n "$hits" ]]; then
      error "forbidden JSON path mention in body prose outside \\path{...}: $file"
      printf '%s\n' "$hits" >&2
    fi

    hits="$(printf '%s\n' "$body" | grep -E 'Ticket[[:space:]]*[0-9]+' || true)"
    if [[ -n "$hits" ]]; then
      error "forbidden ticket identifier in body prose: $file"
      printf '%s\n' "$hits" >&2
    fi

    hits="$(printf '%s\n' "$body" | grep -E '[A-Z][A-Z0-9]+(_[A-Z0-9]+){2,}' || true)"
    if [[ -n "$hits" ]]; then
      error "forbidden all-caps verdict token in body prose: $file"
      printf '%s\n' "$hits" >&2
    fi
  done < <(section_files)
}

check_build_log() {
  local log="$PAPER_DIR/build/main.log"

  if [[ ! -f "$log" ]]; then
    warn "build log not found at $log; skipping build-log lint"
    return
  fi

  # FATAL: correctness warnings — undefined references/citations and
  # double-word cleveref artifacts are real defects even in a skeleton.
  record_grep_failures "$log" "undefined LaTeX references" 'LaTeX Warning: Reference .* undefined|There were undefined references'
  record_grep_failures "$log" "undefined LaTeX citations" 'LaTeX Warning: Citation .* undefined|There were undefined citations'
  record_grep_failures "$log" "possible double-word cleveref artifact" 'Section Section|Appendix Appendix|Theorem Theorem|Lemma Lemma|Definition Definition|Table Table|Figure Figure'

  # Report layout warnings here; the top-level release preflight treats them
  # as fatal.
  local layout_hits
  layout_hits="$(grep -nE 'Overfull \\hbox|Underfull \\hbox|LaTeX Warning: Float too large' "$log" || true)"
  if [[ -n "$layout_hits" ]]; then
    warn "layout warnings found in $log (deferred to drafting arc; non-fatal):"
    printf '%s\n' "$layout_hits" >&2
  fi
}

check_label_consistency() {
  python3 - "$PAPER_DIR" <<'PY'
import pathlib
import re
import sys

try:
    import yaml
except ImportError as exc:
    raise SystemExit(f"ERROR: PyYAML is required for statements-of-record label checks: {exc}")

paper_dir = pathlib.Path(sys.argv[1])
record_path = pathlib.Path("paper/notes/statements-of-record.yml")

with record_path.open("r", encoding="utf-8") as handle:
    data = yaml.safe_load(handle)

known_section_hints = {
    row["target_section_hint"]
    for row in data.get("rows", [])
    if row.get("target_section_hint") and row.get("target_section_hint") != "none"
}

failures = []
section_dir = paper_dir / "sections"
for tex_path in sorted(section_dir.glob("*.tex")):
    text = tex_path.read_text(encoding="utf-8")
    labels = re.findall(r"\\label\{(sec:[^}]+)\}", text)
    if not labels:
        failures.append(f"{tex_path}: missing section label matching \\\\label{{sec:...}}")
        continue

    allows_no_rows = "statements-of-record rows resolved here: none" in text
    for label in labels:
        if label in known_section_hints:
            continue
        if allows_no_rows:
            continue
        failures.append(
            f"{tex_path}: section label {label} does not appear as a "
            "target_section_hint in paper/notes/statements-of-record.yml"
        )

if failures:
    for failure in failures:
        print(f"ERROR: {failure}", file=sys.stderr)
    raise SystemExit(1)
PY
}

main() {
  check_argument "$@"
  check_structure

  if [[ "$FAILURES" -eq 0 ]]; then
    check_body_prose_tokens
    check_build_log
    check_label_consistency || FAILURES=$((FAILURES + 1))
  fi

  if [[ "$FAILURES" -ne 0 ]]; then
    printf 'paper lint failed for %s with %d failure(s)\n' "$PAPER_DIR" "$FAILURES" >&2
    exit 1
  fi

  printf 'paper lint passed for %s\n' "$PAPER_DIR"
}

main "$@"
