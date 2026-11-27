"""Exact OR price and label-symmetric first-two-product face model."""
from functools import lru_cache
from itertools import combinations
def price(raw):
    outputs=sorted({sum(1<<i for i,v in enumerate(raw) if v>>j&1) for j in range(4)}-{0})
    m=len(outputs); sig=[sum((v>>i&1)<<j for j,v in enumerate(outputs)) for i in range(len(raw))]
    prim={1<<j for j in range(m)};need=set(sig)-{0}-prim
    extra=sorted(set(range(1,1<<m))-prim-need)
    for k in range(len(extra)+1):
        for opt in combinations(extra,k):
            pool=prim.copy()
            for v in sorted(need|set(opt),key=int.bit_count):
                if not any(x|y==v for x in pool for y in pool):break
                pool.add(v)
            else:return sum(t!=0 for t in sig)-m+k+len(need)
    raise AssertionError
def signal(v,t):
    x,y,k,j=(bool(v>>b&1) for b in range(4));d=x and y
    return bool(t&1 and d or t&2 and k and (d or j))
@lru_cache(None)
def cliques(t):
    masks=[v for v in range(16) if not signal(v,t)]
    return [s for n in range(5) for s in combinations(masks,n)
            if all(signal(x|y,t) for x,y in combinations(s,2))]
def feasible(raw,tail):
    h=tuple(raw.count(i) for i in range(16));tail=tuple(sorted(tail))
    @lru_cache(None)
    def rec(h,t):
        if not t:return not any(h)
        if sum(h)>sum(max(map(len,cliques(a))) for a in t):return False
        for s in reversed(cliques(t[-1])):
            if all(h[i] for i in s):
                v=list(h)
                for i in s:v[i]-=1
                if rec(tuple(v),t[:-1]):return True
        return False
    return rec(h,tail)
if __name__=='__main__':
    assert [max(map(len,cliques(t))) for t in range(4)]==[1,2,3,4]
    assert price([5,6,3]*3+[0]*5)==9
    assert feasible([5,6,3]*3+[0]*5,[2]*3+[0]*5)
    assert not feasible([5]*9+[0]*5,[2]*3+[0]*5)
    for t in range(4):print(t,[sum(len(s)==j for s in cliques(t)) for j in range(5)])
