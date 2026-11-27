from collections import Counter
from functools import cache
from itertools import permutations
V=1023
edges=[6,24,17,33,66,132,264,528,160,640,576,320,288]
f=[int(any(x&e==e for e in edges)) for x in range(1024)]
@cache
def sub(x):return tuple(y for y in range(1024) if x&y==y)
@cache
def row(u,b):
    words=sub(u)
    sig=sum(f[b|s]<<i for i,s in enumerate(words))
    piv=sum(x for x in (2,4) if u&x and any(f[b|s]!=f[b|s|x] for s in words if not x&s))
    return sig,piv
@cache
def stage(s,t,owner):
    u=V^s^t;guard=False
    for k in sub(t):
        found=set();hot=set()
        for m in sub(s):
            sig,piv=row(u,k|m);found.add(sig)
            if len(found)>2:return 'single'
            if owner&piv:hot.add(sig)
        if len(hot)>1:guard=True
    return 'guard' if guard else 'pass'
tot=Counter();cases=0;end=0
for r in sub(304):
 if r.bit_count()>2:continue
 for order in permutations(range(4)):
    if order.index(0)>order.index(2):continue
    cases+=1;prior=[r]
    for idx,j in enumerate(order):
        out=[]
        for t in prior:
            for s in sub(V^t):
                if s&4 or bool(s&2)!=(j==2) or (j<2 and s&(64<<j)) or f[s]:continue
                why=stage(s,t,(2<<j) if j<2 else 0)
                if why!='pass':tot[idx,why]+=1;continue
                if idx==3 and f[V^s^t]:tot[idx,'output']+=1;continue
                out.append(t|s)
        prior=out;tot[idx,'kept']+=len(out)
    end+=len(prior)
print('cases',cases,'survivors',end,'kept',[tot[i,'kept'] for i in range(4)])
print('last',[(k,tot[3,k]) for k in ('single','guard','output')])
assert cases==84 and end==0
