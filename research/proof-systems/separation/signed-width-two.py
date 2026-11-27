"""Independent signed width-two validation using implication reachability."""
from itertools import combinations
from pathlib import Path
from random import Random
from runpy import run_path
nullspace=run_path(str(Path(__file__).with_name('bipolar-check.py')))['nullspace']

def validate(n,raw):
    if any(not t for t in raw): return True
    top=2*n
    graph=[set() for _ in range(top+1)]
    reach=[1<<i for i in range(top)]
    for term in raw:
        vals=sorted(set(term))
        if len(vals)==1:
            a=vals[0]; b=top
            reach[a] |= 1<<(a^1)
        else:
            a,b=vals
            reach[a] |= 1<<(b^1)
            reach[b] |= 1<<(a^1)
        graph[a].add(b); graph[b].add(a)
    for k in range(top):
        for j in range(top):
            if reach[j]>>k&1: reach[j] |= reach[k]
    def imp(a,b): return bool(reach[a]>>b&1)
    if any(imp(i,i^1) and imp(i^1,i) for i in range(0,top,2)): return True
    color={}
    for root in range(top+1):
        if root in color: continue
        scan=[root]; color[root]=0
        for u in scan:
            for v in graph[u]:
                if v not in color: color[v]=color[u]^1;scan.append(v)
                elif color[v]==color[u]: return False
        for a,b in combinations(scan,2):
            if color[a]==color[b]: continue
            pins=[i for i in (a,b) if i!=top]
            if all(not imp(i,j^1) for i in pins for j in pins): return False
    return True

def brute(n,terms):
    for x in range(1<<n):
        false=[i for i in range(2*n) if (x>>(i//2)&1)!=(i&1)]
        if any(all(i not in false for i in t) for t in terms): continue
        rows=[sum(1<<j for j,t in enumerate(terms) if i in t) for i in false]
        if any(v.bit_count()%2 for v in nullspace(rows,len(terms))): return False
    return True

if __name__=='__main__':
    rng=Random(874)
    for _ in range(2400):
        n=rng.randrange(1,8)
        terms=[tuple(rng.randrange(2*n) for i in range(rng.choice([1,2,2,2])))
               for j in range(rng.randrange(14))]
        assert validate(n,terms)==brute(n,terms)
    print('2400 signed width-two instances passed')
