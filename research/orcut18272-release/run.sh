#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
sha256sum --check --quiet SHA256SUMS
python3 audit.py
mode=${1:-verify}
case "$mode" in
  verify) exit 0 ;;
  controls|producer|independent|full) ;;
  *) echo 'usage ./run.sh [verify|controls|producer|independent|full]' >&2; exit 2 ;;
esac
work=$(mktemp -d)
trap 'rm -rf -- "$work"' EXIT
if [[ $mode == producer || $mode == full ]]; then
  "${CXX:-c++}" -std=c++20 -O2 producer/orcut18272_enum.cpp -o "$work/producer"
  "$work/producer" 0 55 > "$work/producer.log"
  sed -n '/^shard /p' producer/orcut18272-complete.log > "$work/expected.log"
  diff -u "$work/expected.log" "$work/producer.log"
  echo 'Producer replay matched all 55 shard receipts.'
fi
if [[ $mode != producer ]]; then
  "${CXX:-c++}" -std=c++20 -O2 independent/replay.cpp -o "$work/independent"
  "$work/independent" --controls > "$work/controls.log"
  diff -u independent/controls.log "$work/controls.log"
  echo 'Independent startup controls passed.'
fi
if [[ $mode == independent || $mode == full ]]; then
  "$work/independent" 0 55 > "$work/independent.tsv"
  diff -u independent/all-shards.tsv "$work/independent.tsv"
  echo 'Independent chronological replay matched all 55 shard receipts.'
fi
