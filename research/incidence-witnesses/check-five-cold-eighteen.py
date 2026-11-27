from itertools import combinations, combinations_with_replacement
from functools import lru_cache
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
def check(stars):
    for ng in range(4):
        h=8-ng
        masks=[G for G in range(1,63) if any(G&s==s for s in stars)]
        cnt=0
        for gs in combinations_with_replacement(masks,ng):
            base=frozenset(gs)
            def build(i,R):
                nonlocal cnt
                if len(R)>h:return False
                if i==len(stars):
                    cnt+=1
                    if feasible(R,h):
                        print('hit',stars,gs,R,flush=True)
                        return True
                    return False
                s=stars[i]
                inter=63
                for g in gs:
                    if g&s==s:inter &= g
                # Independent selection of the filters on this path is relaxed:
                # any bits outside the intersection may be removed.
                return any(build(i+1,R|{u}) for u in range(1,64) if u&inter==s)
            if build(0,base):return True
        print('clear',ng,cnt,flush=True)
    return False
p=[v for v in range(1,8) if v!=1]
l=[v for v in range(1,8) if v!=2]
for a,b in ((p,l),(l,p)):
    stars=[sum(1<<j for j,y in enumerate(b) if (x&y).bit_count()%2==0) for x in a]
    for d,s in enumerate(stars):
        if s.bit_count()==2:
            assert not check(stars[:d]+stars[d+1:])
            print('pin',d,'excluded',flush=True)
