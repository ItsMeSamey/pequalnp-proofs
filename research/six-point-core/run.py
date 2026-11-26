"""Run the six-point core checks against the pinned raw-child statement."""
import argparse
import itertools
import subprocess
import sys
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('base', type=Path)
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

full_pos, full_neg = projected(six)
require((len(full_pos),len(full_neg)) == (18,33), 'six-point dimensions')
require(all(any((1 << i) & ~n == 0 for n in full_neg) for i in range(13)),
        'each singleton must lie below a negative')
for p in full_pos:
    require(p.bit_count() == 2, 'expected an incidence edge')

point_stars = [sum(edge ^ (1 << i) for edge in full_pos if edge & (1 << i))
               for i in range(6)]
require(all(star.bit_count() == 3 for star in point_stars), 'point-star degree')
def star_output(row):
    return any(row & (1 << i) and row & star for i, star in enumerate(point_stars))
require(all(map(star_output, full_pos)) and not any(map(star_output, full_neg)),
        '23-gate star witness')

def permute(mask, permutation):
    return sum(1 << j for i,j in enumerate(permutation) if mask & (1 << i))

def geometry(ps, ns, points, size):
    neighborhoods = [sum(p & ((1<<points)-1) for p in ps if p & (1 << j))
                     for j in range(points,size)]
    if len(set(neighborhoods)) != len(neighborhoods):
        return [tuple(range(size))]
    result = []
    for pp in itertools.permutations(range(points)):
        images = [permute(h, pp) for h in neighborhoods]
        if set(images) != set(neighborhoods):
            continue
        g = pp + tuple(points + neighborhoods.index(im) for im in images)
        if {permute(p,g) for p in ps} == set(ps) and {permute(n,g) for n in ns} == set(ns):
            result.append(g)
    return result

group = geometry(full_pos, full_neg, 6, 13)
require(len(group) == 24, 'six-point symmetry order')
def orbit(erased):
    return {tuple(sorted(g[i] for i in erased)) for g in group}
require(orbit((0,)) == {(i,) for i in range(6)}, 'point transitivity')
require(orbit((6,)) | orbit((7,)) == {(i,) for i in range(6,13)}, 'line orbits')
triples = orbit((0,6,7)) | orbit((0,6,10))
require(len(triples) == 24, 'triple orbits')
for tr in triples:
    erased = sum(1 << i for i in tr)
    for i in tr:
        require(any((p & erased)==1<<i for p in full_pos), 'erased variable needs a surviving neighbor')

def run(erased, gate_budget, solver, expected):
    missing = sum(1 << i for i in erased)
    keep = [i for i in range(13) if i not in erased]
    def project_row(row):
        return sum(bool(row & (1<<i)) << j for j,i in enumerate(keep))
    ps = sorted({project_row(p) for p in full_pos if not p & missing})
    ns = {project_row(n) for n in full_neg}
    ns = sorted(n for n in ns if not any(n != m and not n & ~m for m in ns))
    cuts = []
    for x in sorted({p & ~n for p in ps for n in ns},key=int.bit_count):
        if not any(c & x == c for c in cuts):
            cuts.append(x)
    size = len(keep)
    require(set(cuts)=={1<<i for i in range(size)}, 'all retained inputs must be mandatory')
    local_group = geometry(ps,ns,sum(i<6 for i in keep),size)
    require((size,len(ps),len(ns)) == expected, 'unexpected cofactor dimensions')
    data = [gate_budget,size,len(ps),len(ns),len(cuts),*ps,*ns,*cuts,
            len(local_group),*(i for g in local_group for i in g)]
    result = subprocess.run([solver.resolve()],input=' '.join(map(str,data))+'\n',
                            text=True,capture_output=True,check=True)
    require(result.stdout == 'UNSAT 1\n','single support was not exhausted')
    print('Erased',erased,'size',size,'rows',len(ps),len(ns),'budget',gate_budget,
          result.stdout.strip(),flush=True)

run((5,),18,args.base,(12,15,26))
run((6,),18,args.base,(12,16,23))
run((7,),18,args.base,(12,15,29))
run((0,6,7),15,args.base,(10,12,16))
run((0,6,10),15,args.base,(10,12,16))
run((),21,args.verifier,(13,18,33))
print('Six-point core >=22; residual >=29; raw >=30; raw without w54 >=35.')
