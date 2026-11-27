"""Replay the fixed prefix and enumerate coordinate fibers for the fixed-support dictionary families."""
from collections import Counter
from hashlib import sha256
from itertools import combinations, combinations_with_replacement, product
from pathlib import Path
from runpy import run_path

ROOT = Path(__file__).resolve().parent
BASE = ROOT / 'baseline'


def explore(points, rows, decreasing, mode):
    pairs = tuple(combinations(range(25),2))
    if mode == 'two pairs':
        choices = combinations_with_replacement(pairs,2)
        count, dictionaries = 45150, 2
    else:
        choices = combinations(range(25),3)
        count, dictionaries = 2300, 1
    largest = {}
    for width in (1,2):
        for positions in combinations(range(25),width):
            mask = sum(1 << j for j in positions)
            sizes = Counter(rows[i][2] & mask for i in points)
            largest[positions] = max(sizes.values())
    by_d = {}
    seen = 0
    for selected in choices:
        seen += 1
        if mode == 'two pairs':
            possible = {tuple(sorted(set(selection))) for selection in product(*selected)}
            used = set(selected[0]) | set(selected[1])
        else:
            possible = combinations(selected,2)
            used = set(selected)
        k = max(largest[positions] for positions in possible)
        d = len(used & decreasing)
        lower = 2*k - 1 - dictionaries + len(decreasing) - d
        if d not in by_d or lower < by_d[d][0]:
            by_d[d] = (lower,k,selected)
    if seen != count:
        raise ValueError('wrong number of support choices')
    return by_d


def main():
    for line in (ROOT / 'SHA256SUMS').read_text().splitlines():
        digest,name = line.split('  ')
        if sha256((ROOT / name).read_bytes()).hexdigest() != digest:
            raise ValueError('checksum mismatch: ' + name)
    base = run_path(str(BASE / 'check.py'))
    base['main']()
    rows,manifest = base['replay']()
    cube = base['load']('signed-cube-pack.json')
    clause = base['load']('signed-clause-pack.json')
    decreasing = {j for j,_,_ in cube['negative_literal_edges']}
    for name,label,pack in [('DNF',1,cube),('CNF',0,clause)]:
        points = base['packed_cells'](pack,label,rows,manifest)
        for mode in ('two pairs','one triple'):
            bounds = explore(points,rows,decreasing,mode)
            lower = min(value[0] for value in bounds.values())
            print(name,mode,'tail',lower,'physical',115+lower,'by d',sorted(bounds.items()))
            expected = {('DNF','two pairs'):57, ('DNF','one triple'):59,
                        ('CNF','two pairs'):40, ('CNF','one triple'):41}
            if lower != expected[name,mode]:
                raise ValueError('unexpected fiber bound')
            if name == 'DNF':
                sizes = [bounds[d][1] for d in sorted(bounds)]
                expected_sizes = [31,28,27,25,23] if mode == 'two pairs' else [32,27,25,23]
                if sizes != expected_sizes:
                    raise ValueError('unexpected DNF fibers')


if __name__ == '__main__':
    main()
