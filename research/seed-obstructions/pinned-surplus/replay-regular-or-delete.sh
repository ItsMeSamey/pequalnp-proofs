#!/usr/bin/env bash
set -euo pipefail
here=$(cd "$(dirname "$0")" && pwd)
project=${LEAN_PROJECT:-/workspace/pequalnp-proofs/lean}
build_dir=${1:-$(mktemp -d)}
mkdir -p "$build_dir"
build_dir=$(cd "$build_dir" && pwd)
cd "$here"
tool="$HOME/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean"
paths="$build_dir:$project/.lake/build/lib/lean"
for path in "$project"/.lake/packages/*/.lake/build/lib/lean; do
  paths="$paths:$path"
done
export LEAN_PATH="$paths"
while IFS=$'\t' read -r module digest imports; do
  if [[ "$module" == module ]]; then continue; fi
  printf '%s  %s.lean\n' "$digest" "$module" | sha256sum -c --status
  "$tool" -j1 -o "$build_dir/$module.olean" "$module.lean"
done < T2RegularOrDelete-manifest.tsv
