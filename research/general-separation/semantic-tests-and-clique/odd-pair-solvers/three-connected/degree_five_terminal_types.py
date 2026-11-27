"""Canonical closed-root types with unordered compulsory pins, using exhaustive permutations."""
from collections import Counter
from itertools import permutations, product
from pathlib import Path
import json

from degree_five_terminal_sweep import closed_root


def canonical(rows):
    keys=[]
    for p,q in ((0,1),(1,0)):
        bins=[[] for _ in range(4)]
        for i in range(2,len(rows)):
            color=((rows[p]>>i)&1)+2*((rows[q]>>i)&1)
            bins[color].append(i)
        for parts in product(*(permutations(b) for b in bins)):
            order=[p,q]+[i for b in parts for i in b]
            keys.append(tuple(sum(((rows[i]>>j)&1)<<k for k,j in enumerate(order)) for i in order))
    return min(keys)


def main():
    data=json.loads(Path(__file__).with_name('degree_five_common_core_census.json').read_text())
    types=Counter(canonical(rows) for g in data for rows in closed_root(g['c'],g['a'],g['b']))
    assert Counter(map(len,types))=={6:2,8:9}
    for rows,count in sorted(types.items(),key=lambda item:(len(item[0]),item)):
        print(len(rows),count,rows)


if __name__=='__main__':
    main()
