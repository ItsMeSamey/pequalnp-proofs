"""Exact finite AND-star sieve and independent raw-circuit comparisons."""
from itertools import product
from random import Random
from check_and_count_low_precision_raw import arithmetic,direct
from quadratic_target import affine_domain,parity


def xorprod(a,b):
    out=set()
    for x in a:
        for y in b:
            out.symmetric_difference_update([x|y])
    return out


def affine(v,c):
    return ({0} if c else set())|{1<<j for j in range(v.bit_length()) if v>>j&1}


def gauss(P,n):
    while True:
        pair=next((m for m in P if m.bit_count()==2),None)
        if pair is None:
            return 0 if any(P-{0}) else (-1 if 0 in P else 1)*(1<<n)
        a=pair&-pair
        b=pair^a
        A={m^a for m in P if m!=pair and m&a}
        B={m^b for m in P if m!=pair and m&b}
        C={m for m in P if not m&pair}
        return 2*gauss(C^xorprod(A,B),n-2)


def signed(P,N,eq):
    flat=affine_domain(N,eq)
    if flat is None:
        return 0
    origin,dirs,_=flat
    coords=[affine(sum(((u>>j)&1)<<i for i,u in enumerate(dirs)),origin>>j&1) for j in range(N)]
    sub=set()
    for m in P:
        term={0}
        for i in range(N):
            if m>>i&1:
                term=xorprod(term,coords[i])
        sub^=term
    return gauss(sub,len(dirs))


def count(n,g,pins,centers=None,gauge=True,target=1):
    prs,(v,c)=arithmetic(n,g)
    m=len(prs)
    N=n+m
    stars=[{i}|{j for j,pair in enumerate(prs) if any(u>>(n+i)&1 for u,_ in pair)} for i in range(m)]
    seen=set()
    if centers is None:
        centers=[]
        for i,s in enumerate(stars):
            if not s&seen:
                centers.append(i)
                seen|=s
    seen=set()
    pieces=[]
    P=affine(v,c)
    for i in centers:
        if seen&stars[i]:
            raise ValueError('overlapping center stars')
        seen|=stars[i]
        s=sorted(stars[i])
        pieces.append([sum(((w>>j)&1)<<k for j,k in enumerate(s)) for w in range(1<<len(s)) if w!=1<<s.index(i)])
        if gauge and v>>(n+i)&1:
            a,b=prs[i]
            P^={1<<(n+i)}^xorprod(affine(*a),affine(*b))
    pieces.extend([[0,1<<i] for i in range(m) if i not in seen])
    total=0
    for choices in product(*pieces):
        mask=sum(choices)
        eq=list(pins)
        phase=P.copy()
        for i,(a,b) in enumerate(prs):
            z=1<<(n+i)
            if mask>>i&1:
                eq.extend([(a[0],1^a[1]),(b[0],1^b[1])])
                phase.symmetric_difference_update([z,0])
            else:
                eq.append((z,0))
        total+=signed(phase,N,eq)
    raw=affine_domain(n,pins)
    volume=(1<<len(raw[1])) if raw is not None else 0
    return (volume+(-1 if target else 1)*total)//2


if __name__=='__main__':
    rng=Random(899)
    for d in range(7):
        for _ in range(55):
            P={i for i in range(1<<d) if i.bit_count()<=2 and rng.randrange(3)==0}
            assert gauss(P,d)==sum((-1)**(sum(m&x==m for m in P)%2) for x in range(1<<d))
    g=[('and',(0,1)),('and',(0,2)),('and',(3,4)),('xor',(3,4,5))]
    try:
        count(3,g,[],[0,1])
    except ValueError:
        pass
    else:
        raise AssertionError('overlap accepted')
    # All AND outputs in readout, shared physical raw input; erasure without gauge fails.
    assert count(3,g,[],[2])==3 and count(3,g,[],[2],gauge=False)==2
    for _ in range(400):
        n=rng.randrange(1,6)
        gs=[]
        for j in range(rng.randrange(1,9)):
            op=rng.choice(['and','and','xor','one'])
            gs.append((op,tuple(rng.randrange(n+j) for j0 in range(2 if op=='and' else rng.randrange(4)))))
        pins=[(rng.randrange(1<<n),rng.randrange(2)) for j in range(rng.randrange(4))]
        for target in (0,1):
            val=sum(direct(n,gs,x)[0]==target and all(parity(x&u)==b for u,b in pins) for x in range(1<<n))
            assert count(n,gs,pins,target=target)==val
    print('385 independent quadratic Gauss sums, 800 pinned circuit counts, necessary-gauge and disjoint-star controls passed')
