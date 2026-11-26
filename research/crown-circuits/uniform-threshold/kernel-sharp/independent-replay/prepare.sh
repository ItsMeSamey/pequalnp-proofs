#!/usr/bin/env bash
set -eu
receipt_dir=$(cd "$(dirname "$0")" && pwd)
proof_repo=${PROOF_REPO:-/workspace/pnp-research}
receipt_work=$(mktemp -d "${FRESH_ROOT:-/dev/shm}/review-sharp-XXXXXX")
package=research/crown-circuits/uniform-threshold/kernel-sharp
revision=1a56a0a95098541b3b5425e733a43366533c43b6
test "$(git -C "$proof_repo" rev-parse "$revision:$package")" = 64b51f59a2f65fa30b613efc86c0fa6050cb5ba6
git -C "$proof_repo" archive "$revision" "$package" | tar -xf - -C "$receipt_work"
printf '%s\n' "$receipt_work" > "$receipt_dir/workdir"
