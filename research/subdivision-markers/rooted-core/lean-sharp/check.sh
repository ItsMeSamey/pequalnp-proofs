#!/bin/bash
set -eu
cd "$(dirname "$0")"
project=/workspace/pequalnp-proofs/lean
p="$project/.lake/build/lib/lean"
for d in "$project"/.lake/packages/*/.lake/build/lib/lean; do p="$p:$d"; done
export LEAN_PATH="$p"
exec "$HOME/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean" -j1 SharpOpposite.lean
