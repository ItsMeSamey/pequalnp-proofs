from check import constraints, parity, q, tag
from time import monotonic
from functools import lru_cache
ones=[(k,b) for k in range(1,16) for b in (2,3)]
def unsat(missing,budget):
    t=monotonic()
    initial=set()
    for u,g in constraints:
        if any(k not in missing and parity(u&k) and tag(g,k)==(q(k)^1) for k in range(1,16)):continue
        initial.add(sum(1<<i for i,(k,b) in enumerate(ones) if parity(u&k) and tag(g,k)==b))
    cs=[]
    for m in sorted(initial,key=int.bit_count):
        if not any((a&m)==a for a in cs):cs.append(m)
    hits=[sum(1<<i for i,c in enumerate(cs) if c>>b&1) for b in range(30)]
    calls=0
    @lru_cache(None)
    def sat(rem,allow,k):
        nonlocal calls
        calls+=1
        if not rem:return True
        if not k:return False
        used=lb=0
        C=rem;small=1<<32;select=0
        while C:
            p=C&-C;C^=p
            opts=cs[p.bit_length()-1]&allow;n=opts.bit_count()
            if n==0:return False
            if n<small:
                small=n; select=opts
            if not (opts&used):
                lb+=1
                if lb>k:return False
                used|=opts
        priority=sorted((b for b in range(30) if select>>b&1),key=lambda b:-(rem&hits[b]).bit_count())
        for b in priority:
            allow^=1<<b
            if sat(rem&~hits[b],allow,k-1):return True
        return False
    ok=sat((1<<len(cs))-1,(1<<30)-1,budget)
    print(missing,budget,ok,calls,round(monotonic()-t,2),flush=True)
    return not ok
assert all(unsat(L,23-15+len(L)) for L in ((3,8,11),(3,8),(3,),()))
