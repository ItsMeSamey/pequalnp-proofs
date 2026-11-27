from itertools import combinations
from functools import reduce,lru_cache
from operator import or_
from frontier import basis,intersection
from conflict_compare import restrict
from closure_control import first_on_support
from signature_bounds import consistent
from wedge_path import wedge
from recognizer import bit_indices

def circuits(cols):
    d=max((k.bit_length() for k,b in cols),default=0)
    cs=[]
    for size in range(1,min(len(cols),d+1)+1):
        for group in combinations(range(len(cols)),size):
            mask=sum(1<<i for i in group)
            if any(c&mask==c for c in cs): continue
            if not consistent(cols,group): cs.append(mask)
    return cs

def upper(cols,L,depth,closed=False):
    cs=circuits(cols)
    @lru_cache(None)
    def closure(mask):
        return first_on_support(cols,mask)
    @lru_cache(None)
    def rec(R,h):
        ans=basis(wedge(u,v) for u,v in combinations(R,2))
        if not ans or not h: return ans
        support=reduce(or_,R,0)
        children={}
        for c in cs:
            if c&support!=c: continue
            accum=[]
            for i in bit_indices(c):
                if i not in children:
                    child=restrict(R,i)
                    if closed: child=closure(reduce(or_,child,0))
                    children[i]=rec(child,h-1)
                accum.extend(children[i])
            ans=intersection(ans,basis(accum))
            if not ans: break
        return ans
    result=rec(tuple(L),depth)
    return result,len(cs),rec.cache_info().currsize
