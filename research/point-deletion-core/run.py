"""Run the point-deletion core checks against the pinned raw-child statement."""
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

six = tuple(range(7,13))
require(all((f & sum(1 << q for q in six)).bit_count() <= 1 for f in features),
        'supplied feature does not collapse')
deleted = {q for q in range(13) if q not in six and q != 1}
require(deleted == {0,2,3,4,5,6}, 'unexpected deleted coordinates')

point_one = 152474746882
negative_one = 169859090180
special_cut = (1 << 1) | (1 << 20)
require(point_one in positive and negative_one in maximal, 'missing point-1 witness')
require(point_one & ~negative_one == special_cut, 'unexpected point-1 cut')
require(point_one & 8191 == 2, 'witness is not a point-1 positive')
require(not point_one & sum(1 << q for q in deleted), 'previous deletion affects witness')
require(not any(p & special_cut for p in positive if p & sum(1 << q for q in six)),
        'point-1 cut is nonzero at a high point')
print('Seven paid point deletions: six private literals and the disjoint cut {1,20}.', flush=True)

def projected(points):
    def project(row):
        return (sum(bool(row & (1 << q)) << i for i,q in enumerate(points))
                | (((row >> 13) & 127) << len(points)))
    ps = sorted({project(p) for p in positive if p & sum(1 << q for q in points)})
    ns = {project(n) for n in maximal}
    ns = sorted(n for n in ns if not any(n != m and not n & ~m for m in ns))
    return ps, ns

ps, ns = projected(six)
require((len(ps), len(ns)) == (18, 33), 'unexpected six-point core dimensions')
for i in range(6):
    priv = [n for p in ps for n in ns if p & ~n == 1 << i]
    for j in range(13):
        if i != j:
            require(any(n >> j & 1 for n in priv), 'missing earliest-point witness')
neighborhoods = [sum(p & 63 for p in ps if p & (1 << (6+j))) for j in range(7)]
require(len(set(neighborhoods)) == 7, 'line neighborhoods must be distinct')

def permute(mask, permutation):
    return sum(1 << j for i,j in enumerate(permutation) if mask & (1 << i))

orbit = set()
order = 0
for point_perm in itertools.permutations(range(6)):
    images = [permute(h, point_perm) for h in neighborhoods]
    if set(images) != set(neighborhoods):
        continue
    permutation = point_perm + tuple(6 + neighborhoods.index(im) for im in images)
    if {permute(n, permutation) for n in ns} != set(ns):
        continue
    require({permute(p, permutation) for p in ps} == set(ps), 'positive mismatch')
    orbit.add(permutation[5])
    order += 1
require(orbit == set(range(6)) and order == 24, 'unexpected point orbit')
print('Six-point core: 18 positives, 33 maximal negatives, 24 label-preserving permutations, point orbit 6.', flush=True)
ps, ns = projected(six[:-1])
cuts = []
for x in sorted({p & ~n for p in ps for n in ns}, key=int.bit_count):
    if not any(c & x == c for c in cuts):
        cuts.append(x)
require((len(ps), len(ns)) == (15, 26), 'unexpected five-point core dimensions')
require(set(cuts) == {1 << i for i in range(12)}, 'unexpected five-point support')
data = [17,12,len(ps),len(ns),len(cuts),*ps,*ns,*cuts]
result = subprocess.run([args.verifier.resolve()], input=' '.join(map(str,data))+'\n',
                        text=True, capture_output=True, check=True)
require(result.stdout == 'UNSAT 1\n', 'expected exhaustive rejection of the unique support')
print('Five-point core: 15 positives, 26 maximal negatives, 12 mandatory inputs, budget 17:', result.stdout.strip())
print('Residual requires at least 7 + 2 + 18 = 27 gates. Raw suffix requires at least 28.')
