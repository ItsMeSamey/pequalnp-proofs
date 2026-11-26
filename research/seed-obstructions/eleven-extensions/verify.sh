#!/usr/bin/env bash
set -euo pipefail
base=$(cd "$(dirname "$0")" && pwd)
ten=$(cd "${1:?supply output of seventeen-final/irreducible-ten/verify.sh}" && pwd)
mkdir -p "${2:?supply output directory}"
out=$(cd "$2" && pwd)
export PYTHONDONTWRITEBYTECODE=1
cd "$base"
test "$(gzip -dc "$ten/families.gz" | sha256sum | cut -d' ' -f1)" = 05973885a89ec022aa6f11fc5e06bcb04afc208beac56033b448f73bd63673bd
test "$(sha256sum nine.txt | cut -d' ' -f1)" = b4a2755543b874f87b00321f803d63a900cef24876bcc0c445cd5020407f7479
for p in singleton_charge tenbasis double_ready tenplus_ready reps mixed11; do c++ -std=c++20 -O3 "$p.cpp" -o "$out/$p"; done
python3 prepare.py "$out"
cp "$ten/rel.txt" "$out/rel.txt"
"$out/singleton_charge" 9 < nine.txt > "$out/singleton.txt"
test "$(awk '$10<=15' "$out/singleton.txt" | wc -l)" = 15
gzip -dc "$ten/families.gz" | "$out/tenbasis" > "$out/tenbase-low.txt"
test "$(wc -l < "$out/tenbase-low.txt")" = 11235
python3 double_inputs.py "$out" | "$out/double_ready" | "$out/reps" "$out/actions.dat" > "$out/nine-reps"
"$out/tenplus_ready" "$out/rel.txt" "$out/tenbase-low.txt" /dev/stdout all | "$out/reps" "$out/actions.dat" > "$out/ten-reps"
test "$(wc -l < "$out/nine-reps")" = 6
test "$(wc -l < "$out/ten-reps")" = 272
cat "$out/nine-reps" "$out/ten-reps" | LC_ALL=C sort -u > "$out/all"
test "$(wc -l < "$out/all")" = 278
"$out/mixed11" "$out/rows" "$out/all" 100000 1 | awk '$NF!=0 {bad++} END {print NR,"families,",bad+0,"non-extinct or capped";if(NR!=278 || bad)exit 1}'
