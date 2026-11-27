from itertools import product
from random import Random
r=Random(311)
def run(n,parents,rc,q,want,pin):
    # Two colors; zero total not required; first color has two charge bits.
    roots=set(rc)
    def merge(st,v,k):
        y=dict(st)
        if v in y and y[v]!=k:return None
        y[v]=k
        return tuple(sorted(y.items()))
    def toggle(s,x):
        if x is not None:s.symmetric_difference_update({x})
    terms={()}
    factors=[]
    for j in range(2):
        f=[(v,k) for v in range(n) if (q[v]>>j)&1 for k in roots if rc[k]==0]
        if not ((want>>j)&1):f.append(None)
        factors.append(f)
    for f in factors+[[p] for p in pin]:
        new=set()
        for st in terms:
            for x in f:toggle(new,st if x is None else merge(st,*x))
        terms=new
    actual=[(terms,())]
    for v in range(n):
        nxt=[];echelon={}
        for vec,prefix in actual:
            for dest in parents[v]:
                out=set()
                for st in vec:
                    y=dict(st)
                    if v not in y:toggle(out,st);continue
                    k=y.pop(v); rest=tuple(sorted(y.items()))
                    if dest!=v:toggle(out,merge(rest,dest,k))
                    elif v==k:toggle(out,rest)
                rem=out.copy()
                while rem and max(rem) in echelon:rem ^= echelon[max(rem)]
                if rem:
                    echelon[max(rem)]=rem
                    nxt.append((out,prefix+(dest,)))
        actual=nxt
    return next((p for s,p in actual if () in s),None)
def check(P,rc,q,want,pins):
    roots=[]
    for v in range(len(q)):
        while P[v]!=v:v=P[v]
        roots.append(v)
    val=0
    for v,k in enumerate(roots):
        if rc[k]==0:val ^= q[v]
    return val==want and all(roots[v]==k for v,k in pins)
statuses=[0,0]
for trial in range(400):
    n=r.randrange(3,8)
    roots=set(r.sample(range(n),2))|{n-1}
    parents=[[v] if v in roots else [w for w in range(v+1,n) if r.randrange(2)] for v in range(n)]
    rc={v:i%2 for i,v in enumerate(sorted(roots))}
    q=[r.randrange(4) for _ in range(n)]; w=r.randrange(4)
    pins=[(r.randrange(n),r.choice(sorted(roots))) for _ in range(r.randrange(3))]
    yes=any(check(P,rc,q,w,pins) for P in product(*parents))
    P=run(n,parents,rc,q,w,pins)
    assert (P is not None)==yes and (not yes or check(P,rc,q,w,pins))
    statuses[int(yes)]+=1
print('400 exact comparisons (NO, YES):',statuses)
