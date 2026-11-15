#!/usr/bin/env bash
set -euo pipefail

repo_root="$(CDPATH= cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)"
if [[ -f "$repo_root/SplitEntry.lean" ]]; then
  project_dir="$repo_root"
else
  project_dir="$repo_root/problems/108-zeta-odd-autopsy/evidence/L-merge/project"
fi
if [[ ! -f "$project_dir/lean-toolchain" ]]; then
  echo "Cannot find the submitted zeta(5) Lean project: $project_dir" >&2
  exit 2
fi
if ! command -v lake >/dev/null 2>&1 && [[ -x "$HOME/.elan/bin/lake" ]]; then
  export PATH="$HOME/.elan/bin:$PATH"
fi
cd "$project_dir"
exec lake comparator --config "$repo_root/comparator.json" "$@"
