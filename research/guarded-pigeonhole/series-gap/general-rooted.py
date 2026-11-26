"""Adversarial feasible rooted simple graphs, comparing semantic and derivable hulls."""
from pathlib import Path
import runpy, sys, random
from functools import lru_cache
from collections import Counter
a=runpy.run_path(str(Path(__file__).with_name('rooted-hull.py')))
insert, null, closure=a['insert'],a['null'],a['affine_closure']

@lru_cache(None)
def tables(n):
    total=(1<<(1<<n))-1
    masks=[total,total]
    for j in range(n):
        step=1<<j
        block=(1<<step)-1
        masks.append((total//((1<<(2*step))-1))*(block<<step))
    return total,masks

def classify(rows):
    m=len(rows)-2
    allbits,table=tables(m)
    hit=allbits
    pairs=[]
    for i,g in enumerate(rows):
        nb=0; vertices=g
        while vertices:
            b=vertices&-vertices;vertices^=b;nb^=table[b.bit_length()-1]
        hit &= allbits^(table[i]&nb)
        piv=1 if i<2 else 1<<(i-1)
        opp=(g>>2)<<1 | ((g&3).bit_count()%2)
        pairs.append((piv,opp))
    if not hit:return None
    span={};cnt=hit.bit_count()
    while hit:
        b=hit&-hit;hit^=b
        insert(1|((b.bit_length()-1)<<1),span)
    expected=list(null(span.values(),m+1))
    dims=[]
    for d in (2,3):
        actual,e=closure(m,pairs,d,expected)
        if len(actual)==len(expected):
            assert all(not a['reduce'](q,actual) for q in expected)
            return d,len(expected),dims+[e],cnt
        dims.append(len(expected)-len(actual))
    return 4,expected,actual,cnt

def edge(g,i,j):
    if i!=j:g[i]^=1<<j;g[j]^=1<<i

def fresh(n,rng):
    g=[0]*n;edge(g,0,1)
    cycle=rng.randint(1,n-2)
    path=[0]+list(range(2,2+cycle))+[1]
    for x,y in zip(path,path[1:]):edge(g,x,y)
    if rng.random()<.5:
        for v in range(2+cycle,n):edge(g,v,rng.randrange(v))
    p=rng.choice([.07,.1,.15,.22,.3,.45,.6])
    for i in range(n):
        for j in range(i):
            if not g[i]>>j&1 and rng.random()<p:edge(g,i,j)
    return g

def mutate(g,rng):
    g=g.copy();n=len(g);kind=rng.randrange(6)
    if n<=15 and kind==0:
        u,v=rng.sample(range(n),2);g.extend([0,0])
        edge(g,u,n);edge(g,n,n+1);edge(g,n+1,v)
    elif n<=16 and kind==1:
        v=rng.randrange(n);g.append(0)
        for j in range(n):
            if g[v]>>j&1:edge(g,n,j)
        if rng.random()<.8:edge(g,n,rng.randrange(n))
    elif n>=10 and kind==2:
        x=rng.randrange(2,n)
        g.pop(x)
        g=[(s&((1<<x)-1))|((s>>(x+1))<<x) for s in g]
    else:
        for k in range(rng.randint(1,3)):
            u,v=rng.sample(range(n),2)
            if {u,v}!={0,1}:edge(g,u,v)
    return g

def scan(runs,seed):
    rng=random.Random(seed);hard=[];counts=Counter();seen=set()
    for r in range(runs):
        if hard and r%5:g=mutate(rng.choice(hard),rng)
        else:g=fresh(rng.randrange(8,16),rng)
        sig=tuple(g)
        if sig in seen:continue
        seen.add(sig)
        result=classify(g)
        if result is None:counts['empty']+=1;continue
        d=result[0];counts[d]+=1
        if d==4:
            print("GAP",g,result,flush=True);return
        if d==3:
            if len(hard)<300:hard.append(g)
            else:hard[rng.randrange(len(hard))]=g
        if r%4000==0:print(r,dict(counts),flush=True)
    print("Final",dict(counts))
if __name__=='__main__':scan(int(sys.argv[1]),int(sys.argv[2]))
