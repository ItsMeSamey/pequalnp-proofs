#!/usr/bin/env bash
set -eu
receipt_dir=$(cd "$(dirname "$0")" && pwd)
proof_repo=${PROOF_REPO:-/workspace/pnp-research}
receipt_work=$(mktemp -d "${FRESH_ROOT:-/dev/shm}/review-two-sided-XXXXXX")
read -r revision tree package < <(python - "$receipt_dir/source-lock.json" <<'PY'
import json,sys
a=json.load(open(sys.argv[1]))
print(a['commit'],a['tree'],a['rel'])
PY
)
test "$(git -C "$proof_repo" rev-parse "$revision:$package")" = "$tree"
git -C "$proof_repo" archive "$revision" "$package" | tar -xf - -C "$receipt_work"
printf '%s\n' "$receipt_work" > "$receipt_dir/workdir"
