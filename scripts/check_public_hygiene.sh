#!/usr/bin/env bash
set -euo pipefail

ROOT="$(git rev-parse --show-toplevel)"
cd "$ROOT"

failed=0

report_paths() {
  local title="$1"
  local matches="$2"
  if [[ -n "$matches" ]]; then
    printf 'ERROR: %s:\n%s\n' "$title" "$matches" >&2
    failed=1
  fi
}

tracked_paths="$(git ls-files | grep -Ei '(^|/)(\.env($|\.)|\.codex($|/)|\.claude($|/)|skills?($|/)|memory($|/)|prompts?($|/)|reviews?($|/)|\.codex_thread_id[^/]*)' || true)"
report_paths "operator-only or sensitive paths are tracked" "$tracked_paths"

operator_content="$(git grep -I -n -E '(Codex|Claude Code|\.codex_thread_id|~/\.codex|~/\.claude)' -- . ':!.gitignore' ':!scripts/check_public_hygiene.sh' ':!vendor/**' || true)"
report_paths "operator/session markers occur in tracked content" "$operator_content"

local_paths="$(git grep -I -n -E '(/home/[A-Za-z0-9._-]+/|/Users/[A-Za-z0-9._-]+/)' -- . ':!scripts/check_public_hygiene.sh' ':!vendor/**' || true)"
report_paths "local absolute paths occur in tracked content" "$local_paths"

secret_candidates="$(git grep -I -l -E '(BEGIN (RSA |EC |OPENSSH )?PRIVATE KEY|AKIA[0-9A-Z]{16}|ASIA[0-9A-Z]{16}|ghp_[A-Za-z0-9]{20,}|github_pat_[A-Za-z0-9_]{20,}|sk-[A-Za-z0-9]{20,}|xox[baprs]-[A-Za-z0-9-]{20,}|AIza[0-9A-Za-z_-]{30,})' -- . ':!scripts/check_public_hygiene.sh' ':!vendor/**' || true)"
report_paths "possible credentials occur in tracked content" "$secret_candidates"

if (( failed )); then
  exit 1
fi

printf 'public hygiene check passed\n'
