from itertools import combinations,product
from functools import cache
E=[(1,2),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(6,9),(6,8),(5,8)]
@cache
def norm(F):
    a=set(F)
    return tuple(sorted(x for x in a if not any(t!=x and t&x==t for t in a)))
@cache
def pin(F,x,b):return norm(tuple(t&~x if b else t for t in F if b or not(t&x)))
@cache
def mask(F):
    a=0
    for t in F:a|=t
    return a
@cache
def score(F):
    A=mask(F)
    xs=[1<<i for i in range(A.bit_length()) if A>>i&1]
    if len(xs)<3:return 0
    best=len(xs)*2
    for x,y in combinations(xs,2):
        # If both raw inputs enter the rest exclusively through this binary gate,
        # at most two joint cofactors exist. Equal pinning contracts that module.
        Fxy=[[pin(pin(F,x,a),y,b) for b in (0,1)] for a in (0,1)]
        if len({u for row in Fxy for u in row})<=2:
            merged=norm(tuple(t&~y|x if t&y else t for t in F))
            best=min(best,score(merged))
        # For a signed canalizing gate select each possible pair of controlling bits.
        # If the counterpart is essential at a controlling bit, it needs another use.
        for cx,cy in product((0,1),repeat=2):
            rx=bool(mask(pin(F,y,cy))&x)
            ry=bool(mask(pin(F,x,cx))&y)
            if rx and ry:
                cost=2+max(score(u) for row in Fxy for u in row)
            elif rx or ry:
                z=x if rx else y
                cost=1+max(score(pin(F,z,b)) for b in (0,1))
            else:
                cost=1+min(max(score(pin(F,z,b)) for b in (0,1)) for z in (x,y))
            best=min(cost,best)
        if best==0:return 0
    return best
F=norm(tuple((1<<i)|(1<<j) for i,j in E))
print(score(F),score.cache_info(),flush=True)
