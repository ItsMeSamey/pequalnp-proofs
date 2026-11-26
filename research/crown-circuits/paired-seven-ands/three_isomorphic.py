"""Canonicalize three continuations under gate permutations and independent pin flips."""
from itertools import permutations
from pathlib import Path
import sys
from collections import Counter, defaultdict

def flip(x):
    return ((x&1)<<1)|(x>>1)

def key(t):
    columns = [[(t[i]>>(2*j))&3 for i in range(3)] for j in range(7)]
    variants=[]
    for p in permutations(range(3)):
        def column(j):
            a=tuple(columns[j][i] for i in p)
            return min(a,tuple(map(flip,a)))
        variants.append(tuple(column(j) for j in p)+tuple(sorted(column(j) for j in range(3,7))))
    return min(variants)

def load(path):
    if not path.exists():return []
    return [list(map(int,r.split())) for r in path.read_text().splitlines(keepends=True) if r.endswith('\n')]

if __name__=='__main__':
    work=Path(sys.argv[1]); data=load(work/'three-sieve.tsv')
    allrows={row[0]:row for row in load(work/'three-live.tsv')}
    classes={idx:key(row[1:4]) for idx,row in allrows.items()}
    for cost in range(3):
        desired={r[0] for r in data if r[-1]==cost}
        group=defaultdict(list)
        for idx in sorted(desired):group[classes[idx]].append(idx)
        proven={}
        for f in [f'three-sem-{cost}.tsv',f'three-final-{cost}.tsv',f'three-a-{cost}.tsv',f'three-iso-a-{cost}.tsv']+(['three-zero.tsv','three-iso-638.tsv','three-iso-854.tsv'] if cost==0 else []):
            for row in load(work/f):
                assert row[-1]==0, (f,row)
                k=classes[row[0]]
                if k in group:proven[k]=(f,row[0])
        print(cost,len(group),len(proven),'templates',sum(len(group[k]) for k in proven),len(desired))
        if len(proven)==len(group):
            dest=Path(__file__).resolve().parent/f'three-final-cost-{cost}-isomorphism.tsv'
            dest.write_text(''.join(f'{idx} {proven[k][0]} {proven[k][1]}\n' for k in sorted(group) for idx in group[k]))
