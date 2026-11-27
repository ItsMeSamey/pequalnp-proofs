"""Relax private hot factors using all nonneighbor hot pairs. No circuit SAT."""
from itertools import combinations, combinations_with_replacement
from functools import lru_cache
from pathlib import Path

raw=frozenset(1<<i for i in range(6))
def ops(S):
    return {z for x,y in combinations(S,2) for z in (x|y,x&y) if z and z not in S}
@lru_cache(None)
def feasible(R,budget):
    def dfs(S,left):
        while True:
            nxt=ops(S)
            req=nxt&R
            if not req: break
            S=S|req
        if R<=S:return True
        if not left:return False
        return any(dfs(S|{z},left-1) for z in nxt)
    return dfs(raw,budget-len(R))
p=[v for v in range(1,8) if v!=1]
l=[v for v in range(1,8) if v!=2]
def star_masks(cold,hot):
    return tuple(sum(1<<j for j,y in enumerate(hot) if not (x&y).bit_count()%2) for x in cold)
stars=star_masks(p,l)
masks=tuple(g for g in range(1,63) if any(g&s==s for s in stars))
@lru_cache(None)
def options(s,filters):
    forbidden=0
    for a,b in combinations([1<<i for i in range(6) if not s>>i&1],2):
        pair=a|b
        if all(g&pair for g in filters):
            forbidden |= pair
    return tuple(u for u in range(1,64) if u&s==s and not u&forbidden)
def check(j):
    budget=9-j
    count=0
    for gs in combinations_with_replacement(masks,j):
        targets=[options(s,tuple(g for g in gs if g&s==s)) for s in stars]
        required=set(gs)
        for t in targets:
            if len(t)==1: required.add(t[0])
        if len(required)>budget: continue
        many=[t for t in targets if len(t)>1]
        def dfs(i,R):
            nonlocal count
            if len(R)>budget:return False
            if i==len(many):
                count+=1
                return feasible(frozenset(R),budget)
            return any(dfs(i+1,R|{u}) for u in many[i])
        if dfs(0,required): raise AssertionError((gs,targets))
    print(j,count,flush=True)
if __name__=='__main__':
    import sys
    for cold,hot in ((p,l),(l,p)):
        stars=star_masks(cold,hot)
        masks=tuple(g for g in range(1,63) if any(g&s==s for s in stars))
        for j in (list(map(int,sys.argv[1:])) or range(5)):check(j)
