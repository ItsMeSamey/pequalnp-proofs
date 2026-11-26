#!/usr/bin/env bash
set -euo pipefail
base=$(cd "$(dirname "$0")" && pwd)
mkdir -p "${1:?usage: bash verify.sh OUTPUT_DIRECTORY}"
out=$(cd "$1" && pwd)
source_dir="$base/irreducible-ten/source"
export PYTHONDONTWRITEBYTECODE=1
python3 "$base/line_basis.py"
python3 "$base/irreducible-ten/five-target/verify.py"
bash "$base/irreducible-ten/verify.sh" "$out/ten"
c++ -std=c++17 -O3 "$base/extend-eight/verify.cpp" -o "$out/verify-eight"
python3 "$base/extend-eight/decode.py" "$source_dir" | "$out/verify-eight"
python3 "$base/extend-nine/verify.py" "$source_dir" "$out"
cmp "$out/ten/refined.txt" "$base/read-once/refined-all.txt"
cmp "$out/distinct-reps.txt" "$base/read-once/geom_reps.txt"
cmp "$out/duplicate-reps.txt" "$base/read-once/dupgeom_reps.txt"
python3 "$base/one-copy/verify.py" "$source_dir/L-meta-18968.json" "$out/ten/refined.txt" "$source_dir/nine.txt" "$out/distinct-survivors.txt" "$out/duplicate-survivors.txt"
python3 "$base/read-once/verify.py"
