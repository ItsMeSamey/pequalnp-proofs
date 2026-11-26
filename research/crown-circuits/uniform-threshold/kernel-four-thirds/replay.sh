#!/usr/bin/env bash
# Replay local proof files against the pinned project and its installed packages.
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
project=${THRESHOLD_PROJECT:-/workspace/pequalnp-proofs/lean}
work=$(mktemp -d)
cd "$project"
export LEAN_PATH="$work:$project/.lake/build/lib/lean"
for lib in "$project"/.lake/packages/*/.lake/build/lib/lean; do
  export LEAN_PATH="$LEAN_PATH:$lib"
done
lean_cli=${THRESHOLD_LEAN:-$(elan which lean)}
# THRESHOLD_MATHLIB can point to an expanded pinned Mathlib object tree.
if [[ -n "${THRESHOLD_MATHLIB:-}" ]]; then
  export LEAN_PATH="$work:$THRESHOLD_MATHLIB:${LEAN_PATH#*:}"
fi
while IFS=$'\t' read -r module digest path imports; do
  [[ "$module" != module ]] || continue
  path="$here/$path"
  printf '%s  %s\n' "$digest" "$path" | sha256sum -c --status
  case "$module" in PEqualNP.*) continue ;; esac
  rel=${module//./\/}
  mkdir -p "$work/$(dirname "$rel")"
  (cd "$(dirname "$path")" && "$lean_cli" -j1 -o "$work/$rel.olean" "$(basename "$path")")
done < "$here/ThresholdPublicFourThirds-manifest.tsv"
printf 'Verified objects in %s\n' "$work"
