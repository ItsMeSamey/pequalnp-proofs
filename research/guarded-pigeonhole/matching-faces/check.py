"""Finite differential check. Brute force supplies only the single-parity oracle."""
from functools import lru_cache
from random import Random
from itertools import combinations
r=Random(90417)
def xor(A,B): return {a^b for a in A for b in B}
def perfect(V,edges):
    if not V:
        yield ()
        return
    u=min(V)
    for e in edges:
        a,b=e
        if a==u and b in V:
            for rest in perfect(V-{a,b},edges):
                yield (e,)+rest
def run(n):
    V=frozenset(range(n))
    edges=[e for e in combinations(V,2) if r.random()<0.72]
    b={e:r.randrange(2) for e in edges}
    lam=[frozenset(range(3)),frozenset(range(3,6)),frozenset(range(7))]
    lam=[s for s in lam if len(s)<n and r.randrange(4)]
    def crosses(e,s):return (e[0] in s) != (e[1] in s)
    penalty={e:r.randrange(2) if r.randrange(4)==0 else 0 for e in edges}
    w={e:penalty[e]+sum(crosses(e,s) for s in lam) for e in edges}
    tight=[e for e in edges if not penalty[e]]
    nodes=lam+[frozenset([i]) for i in V]
    @lru_cache(None)
    def dp(s,incoming):
        if len(s)==1:return {0}
        ch=[a for a in nodes if a<s and not any(a<c<s for c in nodes)]
        owner={i:j for j,c in enumerate(ch) for i in c}
        active=set(range(len(ch)))
        offset={0}
        if incoming:
            i=next(i for i in incoming if i in s)
            j=owner[i];active.remove(j);offset=dp(ch[j],incoming)
        options={}
        for e in tight:
            if not set(e)<=s:continue
            a,d=map(owner.get,e)
            if a==d or a not in active or d not in active: continue
            pair=tuple(sorted((a,d)))
            options.setdefault(pair,set()).update(x^y^b[e] for x in dp(ch[a],e) for y in dp(ch[d],e))
        labels=set()
        for matching in perfect(active,options):
            attainable=offset
            for e in matching: attainable=xor(attainable,options[e])
            labels.update(attainable)
        return labels
    all_=[(sum(w[e] for e in M),sum(b[e] for e in M)%2) for M in perfect(V,edges)]
    expected={p for c,p in all_ if c==len(lam)}
    assert dp(V,None)==expected
    return bool(expected)
ok=0
for _ in range(500):ok+=run(r.choice((8,10,12)))
print('500 face table comparisons passed;',ok,'instances attain dual bound')
