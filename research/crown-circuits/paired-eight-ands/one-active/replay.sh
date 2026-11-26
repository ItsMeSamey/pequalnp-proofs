#!/bin/sh
set -eu
out=${1:?supply a new or existing output directory}
mkdir -p "$out"
for spec in 'hot_anchor.cpp raw' 'hot_sym.cpp sym'; do
 set -- $spec
 g++ -std=c++20 -O3 -march=native "$1" -o "$out/$2"
 while read -r t b r; do
  "$out/$2" "$t" "$b" "$r" 5 "$out/$2-witness-$t-$b-$r"
 done < jobs > "$out/$2.tsv"
 awk '{a[$1]++;p[$1]+=$6;h[$1]+=$7}END{for(i=1;i<=3;i++){print i,a[i],p[i],h[i]; if(h[i])exit 1}if(a[1]!=8||a[2]!=9||a[3]!=8)exit 1}' "$out/$2.tsv"
done
