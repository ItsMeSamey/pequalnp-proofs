"""Compare conflict-DAG, wedge DP and single-conflict signature certificates."""
from functools import reduce
from itertools import combinations
from operator import or_
from wedge_path import wedge,insert
from frontier import basis
from recognizer import bit_indices
from signature_bounds import bounds

def conflict(cols,support):
    pivots={}
    for i in bit_indices(support):
        x,b=cols[i]
        z=1<<i
        while x:
            p=x.bit_length()-1
            if p not in pivots:
                pivots[p]=(x,b,z)
                break
            xx,bb,zz=pivots[p]
            x ^= xx; b ^= bb; z ^= zz
        if not x and b: return z
    return 0

def restrict(R,i):
    pivot=next((x for x in R if x>>i&1),0)
    if not pivot: return R
    return basis(x^pivot if x>>i&1 else x for x in R if x!=pivot)

def solve(cols,L):
    stack=[basis(L)]
    seen=set()
    rows={}
    while stack:
        R=stack.pop()
        if R in seen: continue
        seen.add(R)
        if len(R)<2: continue
        C=conflict(cols,reduce(or_,R,0))
        if C:
            stack.extend({restrict(R,i) for i in bit_indices(C)})
        else:
            for a,b in combinations(R,2):
                z=wedge(a,b)
                insert(rows,z,(a,b,z))
    return [rec for _,rec in rows.values()],len(seen)
