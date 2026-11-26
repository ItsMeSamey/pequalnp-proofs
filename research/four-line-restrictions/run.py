"""Run the four-line core checks against the pinned raw-child statement."""
import argparse
import itertools
import subprocess
import sys
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('verifier', type=Path)
parser.add_argument('source', type=Path, help='folder containing verify_packing.py and L-meta-18968.json')
args = parser.parse_args()
sys.path.insert(0, str(args.source.resolve()))
from verify_packing import samples, require

rows, front, target = samples(args.source / 'L-meta-18968.json')
live = (1 << 38)-1
positive = {row & live for k, row in enumerate(rows) if (target ^ front) >> k & 1}
negative = {row & live for k, row in enumerate(rows) if not target >> k & 1}
maximal = {n for n in negative if not any(n != m and not n & ~m for m in negative)}
require(len(positive) == 28 and len(maximal) == 245, 'unexpected residual matrix')
for p in positive:
    q = (p & 8191).bit_length()-1
    require((p & 8191).bit_count() == 1 and ((p >> 13) & 127).bit_count() == 1,
            'positive must have one raw point and one suffix line')
    if q != 1:
        require(any(p & ~n == 1 << q for n in maximal), 'missing raw point witness')
for line in range(13,20):
    witnesses = [n for p in positive for n in maximal if p & ~n == 1 << line]
    for j in range(20):
        if j != line:
            require(any(n >> j & 1 for n in witnesses), 'missing earliest-line witness')

features = [sum(1 << ((j+d)%13) for d in offsets)
            for offsets in ((0,1),(3,9),(0,1,3,9)) for j in range(6)]
for row in positive | maximal:
    encoded = sum(bool((row & 8191) & support) << i for i, support in enumerate(features))
    require(encoded == row >> 20, 'unexpected point feature')

def core(lines):
    mask = sum(1 << (13+l) for l in lines)
    restricted = [p for p in positive if p & mask]
    degree = [sum(bool(p & 1 << q) for p in restricted) for q in range(13)]
    keep = {q for q,d in enumerate(degree) if d >= 2 or (d and q == 1)}
    if len(keep) < 4:
        for l in lines:
            keep.add(next(q for q,d in enumerate(degree)
                          if d == 1 and any(p & 1 << q and p & 1 << (13+l) for p in restricted)))
    deleted = sum(d > 0 and q != 1 and q not in keep for q,d in enumerate(degree))
    points = sum(1 << q for q in keep)
    free = sorted(({1 << q for q in keep} | {f & points for f in features}) - {0})
    def project(row):
        point_values = sum(bool(row & 8191 & f) << i for i,f in enumerate(free))
        line_values = sum(bool(row & 1 << (13+l)) << (len(free)+i) for i,l in enumerate(lines))
        return point_values | line_values
    ps = sorted({project(p) for p in restricted if p & points})
    negative = {project(n) for n in maximal}
    ns = sorted(n for n in negative if not any(n != m and not n & ~m for m in negative))
    cuts = []
    for x in sorted({p & ~n for p in ps for n in ns}, key=int.bit_count):
        if not any(c & x == c for c in cuts):
            cuts.append(x)
    return [18-deleted, len(free)+len(lines), len(ps), len(ns), len(cuts), *ps, *ns, *cuts], deleted

for lines in itertools.combinations(range(7),4):
    data, deleted = core(lines)
    result = subprocess.run([args.verifier.resolve()], input=' '.join(map(str,data))+'\n',
                            text=True, capture_output=True, check=True)
    require(result.stdout.startswith('UNSAT '), 'solver did not exhaust all supports')
    print('lines', ''.join(map(str,lines)), 'deleted points', deleted, 'core budget', data[0],
          result.stdout.strip(), flush=True)
