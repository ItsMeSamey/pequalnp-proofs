"""Conditional expectation using integer-scaled edge-pair agreement probabilities."""
from collections import defaultdict
from math import isqrt

def construct(network,m,r,a,u,delta,strict=True):
    assert 1<=u<=a and r>=2
    L=1<<a; R=r**a; D=R*R
    owners=[]
    for side in network:
        ids=[None]*m
        for v,(_,edges) in enumerate(side):
            assert len(edges)<=delta
            for e in edges:
                assert 0<=e<m and ids[e] is None
                ids[e]=v
        assert None not in ids
        owners.append(ids)
    if strict: assert m>=2*D*D*delta and m>=L*D and 2*L<=delta
    labels=[[None]*len(side) for side in network]
    for side in (0,1):
        prior=[]
        for v,(_,edges) in enumerate(network[side]):
            costs=defaultdict(int)
            for e in edges:
                w=owners[1-side][e]
                for j,symbol in prior:
                    z=owners[1-side][j]
                    x,y=labels[1-side][w],labels[1-side][z]
                    val=R if w==z else 1 if x is None or y is None else R*int(x==y)
                    costs[symbol]+=val
            missing=next((k for k in range(min(R,len(costs)+1)) if not costs.get(k,0)),None)
            code=missing if missing is not None else min(costs,key=lambda k:(costs[k],k))
            labels[side][v]=code
            prior.extend((e,code) for e in edges)
    digits=[[tuple((v//r**i)%r for i in range(a)) for v in side] for side in labels]
    types=defaultdict(lambda:defaultdict(list))
    for e in range(m):
        x,y=(digits[s][owners[s][e]] for s in (0,1))
        pattern=tuple((min(i,j),max(i,j)) for i,j in zip(x,y))
        key=sum((i>j)<<k for k,(i,j) in enumerate(zip(x,y)))
        types[pattern][key].append(e)
    packets=[]
    for pattern,classes in sorted(types.items()):
        mask=sum((x!=y)<<i for i,(x,y) in enumerate(pattern))
        per=1<<(a-mask.bit_count())
        for t in range((max(map(len,classes.values()))+per-1)//per):
            used=defaultdict(int); slots=[]
            for site in range(L):
                key=site&mask; j=t*per+used[key]; used[key]+=1
                ls=classes.get(key,())
                slots.append(ls[j] if j<len(ls) else None)
            packets.append(tuple(slots))
    shells=[tuple([v[i] for v in ds] for ds in digits) for i in range(u)]
    if strict:
        assert len(packets)*L<=3*m
        for sc in shells:
            for s in (0,1):
                loads=defaultdict(int)
                for (_,edges),g in zip(network[s],sc[s]): loads[g]+=len(edges)
                assert max(loads.values(),default=0)*r<=3*m
    return a,u,tuple(packets),shells

def rounded_power(s):
    lo,hi=0,s
    while lo+1<hi:
        j=(lo+hi)//2
        if j**10>=s**9:hi=j
        else:lo=j
    return hi

def preflight(s,m0,p0):
    assert s>=2 and p0>=1
    lam=(s-1).bit_length(); root=isqrt(lam)
    H=(s+root-1)//root; delta=rounded_power(s)
    d=0; total=0; upper=m0; prec=p0; layers=[]
    while upper>H:
        u=lam//(131072*(1<<d)); total+=u; a=2*total
        L=1<<a; D=64**(2*a); small=1<<(a-u)
        if not (1<=u<=H+1 and u**5>=lam**4 and L**1000<=s and D**1000<=s
                and H+1>=2*D*D*delta and H+1>=L*D and 2*L<=delta
                and upper*(2*L-1)+1<s**4 and prec*u<=(H+1)*small
                and 8*(a+1)*u<=small):
            return None
        layers.append((a,u))
        prec+=8*((3*upper+u-1)//u)*L+8*upper*(a+1)
        d+=1;upper//=8
    return H,delta,tuple(layers)

class SourcePlan:
    def __init__(self,s,m0,p0):
        self.record=preflight(s,m0,p0)
    def __call__(self,network,m,d):
        if self.record is None:return None
        H,delta,layers=self.record
        if m<=H:return None
        a,u=layers[d]
        return construct(network,m,64,a,u,delta)
