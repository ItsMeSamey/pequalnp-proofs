from itertools import product
from random import Random
from finite_pass_rail import _independent_indices, decide_passes


def rank(matrix,p):
    a=[list(row) for row in matrix]
    r=0
    for j in range(len(a[0]) if a else 0):
        i=next((i for i in range(r,len(a)) if a[i][j]),None)
        if i is None:continue
        a[r],a[i]=a[i],a[r]
        d=pow(a[r][j],-1,p);a[r]=[t*d%p for t in a[r]]
        for i in range(r+1,len(a)):
            d=a[i][j];a[i]=[(v-d*u)%p for u,v in zip(a[r],a[i])]
        r+=1
    return r


def verify(n,d,passes,order,p,start,closing,**kw):
    options=set()
    for x in range(1<<n):
        for s in (range(d) if start is None else [start]):
            state=s
            for _,gates in passes:
                for v,a,b in gates:
                    selected=(x>>(abs(v)-1)&1)^(v<0)
                    state=(b if selected else a)[state]
            if closing[state]==s:
                options.add((x,s))
    witness,r=decide_passes(n,d,passes,order,prime=p,start=start,closing=closing,**kw)
    assert (witness in options if options else witness is None)
    return len(options),r


if __name__=='__main__':
    rng=Random(94)
    for _ in range(100):
        p=rng.choice([2,3,5]);d=rng.randrange(2,4);k=rng.randrange(4)
        tensors=[tuple(tuple(rng.sample(range(d),d)) for j in range(k)) for i in range(rng.randrange(1,8))]
        dense=[[int(all(t[j][xy[0]]==xy[1] for j,xy in enumerate(coord)))
                for coord in product(product(range(d),repeat=2),repeat=k)] for t in tensors]
        ix=_independent_indices(tensors,d,p,None)
        assert len(ix)==rank(dense,p)==rank([dense[i] for i in ix],p)
    for _ in range(90):
        n=rng.randrange(1,5);d=rng.randrange(2,5); order=rng.sample(range(1,n+1),n)
        closing=rng.sample(range(d),d);passes=[]
        for j in range(rng.randrange(4)):
            forward=rng.choice([True,False]);gates=[]
            for v in order if forward else reversed(order):
                if rng.randrange(3):
                    gates.append((v*rng.choice((-1,1)),rng.sample(range(d),d),rng.sample(range(d),d)))
            passes.append((forward,gates))
        for start in (None,rng.randrange(d)):
            verify(n,d,passes,order,rng.choice((2,3,5)),start,closing)
    e=tuple(range(5));rho=(1,2,3,4,0);inv=(4,0,1,2,3)
    passes=[(True,[(2,e,rho)])]
    for s in (None,3):
        pairs,r=verify(2,5,passes,[1,2],2,s,inv,promised_trace=s is None)
        assert pairs==(10 if s is None else 2)
    # Fixed count two gives zero trace in F₂, yet the unpromised solver accepts.
    assert verify(1,2,[],[1],2,None,(0,1))[0]==4
    assert verify(1,2,[],[1],2,1,(1,0))[0]==0
    print('100 explicit tensor rank comparisons; 180 pinned/unpinned rail decisions, Barrington 5/0, even multiplicity and even fixed-point controls passed')
