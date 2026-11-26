"""Exhaustive checks of affine indicator matrix rank and marked-edge contraction."""
from collections import defaultdict
from fractions import Fraction
from itertools import combinations
from random import Random

def components(n, edges, mask):
    labels=list(range(n))
    for i,(u,v) in enumerate(edges):
        if mask >> i & 1:
            old,new=labels[u],labels[v]
            labels=[new if x==old else x for x in labels]
    return [sum(1<<i for i,v in enumerate(labels) if v==j) for j in set(labels)]

def check(n,edges):
    cols=[(1<<u)|(1<<v) for u,v in edges]
    m=len(cols)
    full=(1<<m)-1
    h=min(Fraction(sum((v&x).bit_count()==1 for v in cols),x.bit_count())
          for x in range(1,1<<n) if x.bit_count()<=n//2)
    synd=[0]
    for col in cols:
        synd += [s^col for s in synd]
    solutions=[x for x,s in enumerate(synd) if s==3]
    assert len(solutions)==1<<(m-n+1)
    assert all(sum(x>>j&1 for x in solutions)*2==len(solutions) for j in range(m))
    ranks=[]
    for left in range(1,full):
        right=full^left
        if left>right or not m<=3*left.bit_count()<=2*m:
            continue
        rows=defaultdict(set)
        for x in solutions:
            rows[x&left].add(x&right)
        supports=set(map(frozenset,rows.values()))
        assert sum(map(len,supports))==len(set().union(*supports))
        lam=n+1-len(components(n,edges,left))-len(components(n,edges,right))
        assert len(supports)==1<<lam
        assert lam>=1+h*n/(18*(3+h))
        ranks.append(len(supports))
    rng=Random(n)
    for _ in range(160):
        charge=rng.randrange(1<<n)
        clauses=[[(rng.randrange(m),rng.randrange(2)) for _ in range(rng.randrange(1,4))]
                 for _ in range(rng.randrange(8))]
        marked=sorted({j for clause in clauses for j,b in clause})
        dm=sum(1<<j for j in marked)
        comps=components(n,edges,full^dm)
        def ok(x):
            return all(any((x>>j&1)==b for j,b in clause) for clause in clauses)
        brute=sum(s==charge and ok(x) for x,s in enumerate(synd))
        projected=0
        for y in range(1<<len(marked)):
            x=sum(1<<j for i,j in enumerate(marked) if y>>i&1)
            projected+=ok(x) and all(((charge^synd[x])&c).bit_count()%2==0 for c in comps)
        assert brute==projected<<(m-len(marked)-n+len(comps))
    print(f'{n} vertices: {len(ranks)} unordered balanced cuts, minimum exact matrix rank {min(ranks)}; 160 overlays verified')

if __name__=='__main__':
    check(4,list(combinations(range(4),2)))
    check(6,[(i,(i+1)%3) for i in range(3)]+[(i+3,(i+1)%3+3) for i in range(3)]+[(i,i+3) for i in range(3)])
    check(8,[(i,i^(1<<j)) for i in range(8) for j in range(3) if not i&(1<<j)])
    check(10,[(i,(i+1)%5) for i in range(5)]+[(i+5,(i+2)%5+5) for i in range(5)]+[(i,i+5) for i in range(5)])
