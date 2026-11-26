#!/usr/bin/env bash
set -eu
source_dir=$(cd "$(dirname "$0")" && pwd)
run_dir=$(mktemp -d)
trap 'rm -rf "$run_dir"' EXIT
cd "$run_dir"
python "$source_dir/control.py"
for unit in ten profiles11 canonical families general11; do
    c++ -std=c++20 -O3 "$source_dir/$unit.cpp" -o "$unit"
done
python "$source_dir/chron4.py" >ten-bases.txt
./ten <ten-bases.txt >ten-output.txt
cmp "$source_dir/ten-census.txt" ten-output.txt
./profiles11 >all-profiles.txt
./canonical <all-profiles.txt >canonical-profiles.txt
./families 0 5 <canonical-profiles.txt >census.txt
cmp "$source_dir/census.txt" census.txt
for width in 4 5; do
    ./general11 5 "$width" 0 17 >anchor.txt
    cmp "$source_dir/anchor-width$width.txt" anchor.txt
done
awk '{families += $4; if ($1 != NR-1 || $5 != 0) exit 1} END {if (NR != 660) exit 1; print NR, "profiles,", families, "helper banks"}' census.txt
