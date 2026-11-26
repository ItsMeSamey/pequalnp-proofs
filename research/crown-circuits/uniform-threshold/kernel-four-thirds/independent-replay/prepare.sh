#!/usr/bin/env bash
set -eu
receipt_dir=$(cd "$(dirname "$0")" && pwd)
proof_repo=${PROOF_REPO:-/workspace/pnp-research}
receipt_work=$(mktemp -d "${FRESH_ROOT:-/dev/shm}/review-four-thirds-XXXXXX")
package=research/crown-circuits/uniform-threshold/kernel-four-thirds
revision=d6ced71c7dbd8b5ee898882f5318ef78acf1050c
test "$(git -C "$proof_repo" rev-parse "$revision:$package")" = 77c29f5e19e0622a04e6bcf124a446e7beed84f6
git -C "$proof_repo" archive "$revision" "$package" | tar -xf - -C "$receipt_work"
printf '%s\n' "$receipt_work" > "$receipt_dir/workdir"
