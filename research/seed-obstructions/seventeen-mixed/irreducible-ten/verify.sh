#!/usr/bin/env bash
set -euo pipefail
base=$(cd "$(dirname "$0")" && pwd)
output=${1:?usage: bash verify.sh OUTPUT_DIRECTORY}
mkdir -p "$output"
out=$(cd "$output" && pwd)
cd "$base"
python3 prepare.py "$out"
c++ -std=c++20 -O3 stream.cpp -o "$out/enumerate"
c++ -std=c++20 -O3 charge_fast.cpp -o "$out/charge"
"$out/enumerate" < "$out/raw.in" | gzip -1 > "$out/families.gz"
digest=$(gzip -dc "$out/families.gz" | sha256sum)
test "${digest%% *}" = 05973885a89ec022aa6f11fc5e06bcb04afc208beac56033b448f73bd63673bd
gzip -dc "$out/families.gz" | LC_ALL=C sort -S 32M -T "$out" | uniq -c |
  awk '{if ($1 != 1) bad++; total++} END {print total, "distinct families,", bad+0, "duplicate rows"; if (bad || total != 1218270) exit 1}'
gzip -dc "$out/families.gz" | "$out/charge" "$out/rel.txt" | python3 histogram.py "$out/low.txt"
python3 refinements.py "$out/low.txt" "$out/refined.txt"
digest=$(sha256sum "$out/refined.txt")
test "${digest%% *}" = 79dc8201da35963df8d1b6fe6055ab16263252c6ba5b159cfaf68505e8596a9f
