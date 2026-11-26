from functools import reduce
from itertools import combinations
from operator import xor
from random import Random

rng=Random(539)
def key(mask): return mask.bit_count(),mask
def evaluate(poly,point): return sum((m&point)==m for m in poly)%2

def check(d):
    pairs=sorted((1<<i|1<<j for i,j in combinations(range(d),2)),key=key)
    base={0}|{1<<i for i in range(d)}
    missing=set(); rules={}
    for pair in pairs:
        if rng.randrange(3)==0:
            missing.add(pair)
        else:
            rules[pair]={m for m in sorted(missing|base) if rng.randrange(5)==0}
    cliques={b for b in range(1<<d) if all((b&p)!=p for p in rules)}
    normal={b: {b} for b in cliques}
    border={b|1<<i for b in cliques for i in range(d)}
    for m in sorted(border-cliques,key=key):
        i=next(i for i in range(d) if m>>i&1 and (m^(1<<i)) in cliques)
        pivot=next(p for p in rules if p&(1<<i) and m&p==p)
        q=m^pivot
        output=set()
        for term in rules[pivot]:
            cur={q}
            for bit in range(d):
                if term>>bit&1:
                    cur=reduce(xor,(normal[c|1<<bit] for c in cur),set())
            output^=cur
        assert all(key(c)<key(m) for c in output)
        normal[m]=output
    actual={x for x in range(1<<d) if all(evaluate(poly^{p},x)==0 for p,poly in rules.items())}
    assert len(actual)<=len(cliques)
    for x in actual:
        assert all(evaluate(poly,x)==((x&m)==m) for m,poly in normal.items())
    return len(actual)

models=sum(check(rng.randrange(1,8)) for _ in range(600))
print(f'600 border systems checked on all Boolean points, with {models} total models')
