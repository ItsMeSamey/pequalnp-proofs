#!/bin/sh
set -eu
base=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
seed=$1
python "$base/verify.py" "$seed"
python "$base/summary.py" "$seed"
python "$base/joint.py" "$seed"
python "$base/finaledge.py" "$seed"
python "$base/repeated.py" "$seed"
python "$base/sixouter.py" "$seed"
python "$base/punctured-parallel.py" "$seed"
