#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
build=$(mktemp -d)
trap 'rm -rf "$build"' EXIT
for exe in six_one_dirty six_one_three six_one_hot; do
  g++ -O3 -std=c++20 -mpopcnt "$exe.cpp" -o "$build/$exe"
done
{
  "$build/six_one_dirty" 1 0
  "$build/six_one_dirty" 2 0
  "$build/six_one_three" 3 0
  "$build/six_one_hot" 2 0
  "$build/six_one_hot" 3 0
  node six_one_hot_fast.js
} > "$build/census.out"
diff -u six-one-certified-census.out "$build/census.out"
