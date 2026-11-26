#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
project="${LEAN_PROJECT:-/workspace/pequalnp-proofs/lean}"
lean="${LEAN_BIN:-$HOME/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean}"
project=$(realpath "$project")
artifacts=$(mktemp -d)
trap 'rm -rf "$artifacts"' EXIT
export LEAN_PATH="$artifacts:$project/.lake/build/lib/lean"
for dependency in "$project"/.lake/packages/*/.lake/build/lib/lean; do
  LEAN_PATH="$LEAN_PATH:$dependency"
done
sha256sum --quiet -c SHA256SUMS
(cd ../../../seed-obstructions/pinned-surplus && "$lean" -j1 -o "$artifacts/GateSurplus.olean" GateSurplus.lean)
for module in ThresholdOrGroups T2OrPartition ThresholdOrExtraction ThresholdOrFrontier ThresholdOrBranch ThresholdOrWeight ThresholdOrMultiplicity ThresholdOrRaw ThresholdOrIncidence ThresholdOrPhysicalBook; do
  "$lean" -j1 -o "$artifacts/$module.olean" "$module.lean"
done
