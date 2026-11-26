"""Verify the single-pencil selector used for three protected landmarks."""
from itertools import permutations
from random import Random
from single_cycle_check import fixture,orbits,switch
from check_promise_pfaffian import passive,cap,settings
from check_deterministic_universality import is_universal_raw,nonsingular

def raw_selector(p,e,anchor,a,b):
    k=len(anchor)
    # Put distinct adjacent cuts along the root carrier after its fixed splice.
    p,positions=passive(p,[a]*(k+1)+[b]+list(anchor))
    root_a=positions[0];root_b=positions[k+1]
    p=cap(p,[root_a,root_b])
    extra=list(zip(positions[1:k+1],positions[k+2:]))
    all_ch=e+extra
    ref=list(p);T=[]
    for ch in all_ch:
        lab,_=orbits(ref);t=lab[ch[0]]!=lab[ch[1]];T.append(t)
        if t:switch(ref,ch)
    _,cycles=orbits(ref)
    if len(cycles)!=1:return None
    pos={x:i for i,x in enumerate(cycles[0])}
    ends=[sorted(pos[i] for i in ch) for ch in all_ch]
    M=[sum(int((x<u<y)^(x<v<y))<<j for j,(u,v) in enumerate(ends)) for x,y in ends]
    def new():
        M.append(0);return len(M)-1
    def link(i,j):
        M[i]^=1<<j;M[j]^=1<<i
    pairs=[];flip=[]
    for i in range(0,len(e),2):
        j=i+1
        if T[i]==T[j]:pairs.append((i,j))
        else:
            u=new();link(i,u);pairs.append((j,u))
        # The tag is present for empty X on even pairs, or first-only X on odd pairs.
        x0=int(T[i])+2*int(T[j])
        flip.append(x0 in (0,1))
    d0,d1=new(),new()
    for j,vec in enumerate([1,2,3][:k]):
        i=len(e)+j
        if T[i]:q=new();link(i,q);i=q
        if vec&1:link(i,d0)
        if vec&2:link(i,d1)
    return M,pairs,flip

def audit(p,e,A,a,b):
    states=settings(p,e)
    truth=[orbits(s) for s in states]
    if not all(len(c)==len(A) and len({labels[l] for l in A})==len(A) for labels,c in truth):return False
    S=raw_selector(p,e,A,a,b)
    actual=not (S is not None and is_universal_raw(*S[:2]))
    assert actual==any(l[a]==l[b] for l,_ in truth)
    for s,(l,c) in enumerate(truth):
        if S is None:coeff=0
        else:
            M,pairs,flip=S
            removed=sum((1<<i)|(1<<j) for g,(i,j) in enumerate(pairs) if ((s>>g)&1)^flip[g])
            coeff=nonsingular(M,((1<<len(M))-1)^removed)
        assert coeff==(l[a]!=l[b]),(s,a,b,A)
    return True

if __name__=='__main__':
    r=Random(828249);checked=0
    for n in range(2,7):
        for _ in range(75):
            m=r.randrange(5) if n>=3 else 0
            p,e,last=fixture(n,[r.sample(range(n),3) for g in range(m)],r.sample(range(n),n))
            k=r.randrange(2,min(n,3)+1)
            sample=r.sample(range(n),k)+r.sample(range(n),2)
            p,c=passive(p,[last+x for x in sample]);checked+=audit(p,e,c[:-2],*c[-2:])
    for k in (2,3):
        p,e,last=fixture(k+1,[(0,1,2)],[1,0,*range(2,k+1)])
        for A in permutations(range(k+1),k):
            for a,b in permutations(range(k+1),2):
                pp,c=passive(p,[last+x for x in (*A,a,b)])
                checked+=audit(pp,e,c[:-2],*c[-2:])
    print(checked,'protected fixtures and all physical mask coefficients passed')
