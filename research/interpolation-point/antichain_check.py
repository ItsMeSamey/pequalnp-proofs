from itertools import combinations,product
from random import Random
rng=Random(398)
for trial in range(10):
    n=2; m=2; budget=1
    groups=2
    X=groups*(budget+1)
    anchor=X+m
    end=anchor+(n+1)*(budget+1)
    sets=[{j for j in range(n) if rng.randrange(2)} for i in range(m)]
    terms=set()
    for x in range(X):
        for j in range(n+1):
            for t in range(budget+1):
                y=anchor+j*(budget+1)+t
                if x<budget+1 or j==n:terms.add(frozenset(((x,0),(y,0))))
                if x>=budget+1:
                    for i in range(m):
                        if j in sets[i]:
                            for b in range(2):terms.add(frozenset(((x,0),(y,0),(X+i,b))))
    assert not any(a<b for a in terms for b in terms)
    def tree(v):
        if not v:return []
        if len(v)==1:return [set(v)]
        k=len(v)//2
        return [set(v)]+tree(v[:k])+tree(v[k:])
    cuts=tree(list(range(X)))+tree(list(range(X,end)))
    for sel in range(end):
        passed=True
        for bit in range(2):
            cf={frozenset((i,b) for i,b in t if i!=sel) for t in terms if (sel,1-bit) not in t}
            cf={t for t in cf if not any(s<t for s in cf)}
            for cut in cuts:
                rows={}
                for term in cf:
                    p=frozenset(v for v in term if v[0] in cut)
                    q=term-p
                    if p and q: rows.setdefault(p,set()).add(q)
                if len(set(map(frozenset,rows.values())))>1: passed=False
        expected=sel in range(X,X+m) and sets[sel-X]==set(range(n))
        assert passed==expected
print('10 initial antichains; all singleton selectors, both branches and all tree cuts verified')
