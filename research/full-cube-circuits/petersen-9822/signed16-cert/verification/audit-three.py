from functools import cache
from itertools import product
from pathlib import Path
E=(6,24,17,33,66,132,264,528,160,640,576,320,288)
F=[any(m&e==e for e in E) for m in range(1024)]
@cache
def subs(m):
    return tuple(x for x in range(1024) if x&m==x)
@cache
def key(m,u):
    # On a graph predicate an internal edge gives constant 1. Otherwise an extension
    # accepts iff it contains a boundary singleton or an internal edge of its own.
    if F[m]:return 1024
    return sum(1<<i for i in range(10) if u>>i&1 and F[m|1<<i])
@cache
def small(s,t,n):
    u=1023^s^t
    return all(len({key(m|w,u) for w in subs(s)})<=n for m in subs(t))
base=Path('../reductions')
stored={}
for line in (base/'three_bins.log').read_text().splitlines():
    if line.startswith('survivor '):
        _,*xs,order=line.split();stored[tuple(map(int,xs))]=set(order.split(','))
seen={};raw=[0]*4
for r in subs(1008):
 if r.bit_count()>3:continue
 free=[1<<i for i in range(10) if not (r|6)>>i&1]
 for assignment in product(range(4),repeat=len(free)):
    b=[0,0,2,4]
    for i,w in zip(assignment,free):b[i]|=w
    if any(F[x] for x in b) or b[0]&64 or b[1]&128:continue
    raw[r.bit_count()]+=1
    for order in ('012','102','021'):
        s=0
        for level,c in enumerate(order,1):
            h=b[int(c)]
            if not small(h,r|s,2):break
            s|=h
            if level>1 and not small(s,r,1<<level):break
        else:seen.setdefault((r,*b),set()).add(order)
assert seen==stored
cert={}
for line in (base/'audit_guard.log').read_text().splitlines():
 if line.startswith('direct '):continue
 r,a,b,q,o,order,j,*m=line.split()
 group=tuple(map(int,(r,a,b,q,o))); j=int(j);before,s1,s2,p1,p2,w=map(int,m)
 assert order in seen[group] and j<2
 r,*bs=group
 t=r
 for c in order:
    if int(c)==j:break
    t|=bs[int(c)]
 s=bs[j];u=1023^s^t;i=2<<j
 assert before&t==before and s1&s==s1 and s2&s==s2 and u&i
 assert all(x&u==x for x in (p1,p2,w))
 for a,p in ((s1,p1),(s2,p2)):
    assert not p&i and F[before|a|p]!=F[before|a|p|i]
 assert F[before|s1|w]!=F[before|s2|w]
 assert (group,order) not in cert
 cert[group,order]=True
assert len(cert)==sum(map(len,seen.values()))
print(raw,len(seen),len(cert))
