"""Independent finite original-circuit residue and hashed-bit-probe checks."""
from itertools import combinations
from random import Random


def arithmetic(n,gates):
    # Each pair is (mask, constant). Raw values precede named AND outputs.
    forms=[(1<<j,0) for j in range(n)]
    products=[]
    for op,args in gates:
        if op=='and':
            products.append(tuple(forms[j] for j in args))
            f=(1<<(n+len(products)-1),0)
        else:
            a,c=0,int(op=='one')
            for j in args:
                u,b=forms[j]
                a^=u
                c^=b
            f=a,c
        forms.append(f)
    return products,forms[-1]


def reduce_eqs(eqs):
    B={}
    for mask,val in eqs:
        while mask:
            pivot=(mask&-mask).bit_length()-1
            if pivot not in B:
                B[pivot]=mask,val
                break
            u,b=B[pivot]
            mask^=u
            val^=b
        else:
            if val:
                return None
    return B


def residue(n,gates,p,pins):
    pairs,(last,c)=arithmetic(n,gates)
    m=len(pairs)
    N=n+m
    total=0
    for j in range(min(m+1,max(0,m-n+1+len(pins)+p))):
        for choice in combinations(range(m),j):
            eqs=[*pins,(last,1^c)]
            sign=m-j
            chi=0
            for i,pair in enumerate(pairs):
                z=1<<(n+i)
                if i in choice:
                    eqs.append((z,0))
                else:
                    chi^=z
                    eqs.extend((u,1^b) for u,b in pair)
            basis=reduce_eqs(eqs)
            if basis is None:
                continue
            for a,(u,b) in sorted(basis.items()):
                if chi>>a&1:
                    chi^=u
                    sign^=b
            if not chi:
                total+=(-1 if sign&1 else 1)<<(N-len(basis))
    return total%(1<<p)


def direct(n,gates,x):
    v=[x>>j&1 for j in range(n)]
    joint=x
    k=n
    for op,args in gates:
        if op=='and':
            a,b=args
            val=v[a]&v[b]
            joint|=val<<k
            k+=1
        else:
            val=int(op=='one')
            for i in args:
                val^=v[i]
        v.append(val)
    return v[-1],joint


def verify(n,gates,pins):
    good=[x for x in range(1<<n) if (lambda v: v[0] and all((v[1]&u).bit_count()%2==b for u,b in pins))(direct(n,gates,x))]
    for p in (1,2,3):
        assert residue(n,gates,p,pins)==len(good)%(1<<p)
    ans=sum(residue(n,gates,1,[*pins,(1<<j,1)])<<j for j in range(n))
    if len(good)==1:
        assert ans==good[0] and direct(n,gates,ans)[0]
    return good


if __name__=='__main__':
    rng=Random(66)
    gs=[('and',(0,1)),('and',(2,2)),('and',(2,3))]
    assert verify(2,gs,[])==[3]
    assert verify(2,gs,[(0,1)])==[]
    assert verify(2,gs,[((1<<2)|(1<<3),0),(0,0)])==[3]
    assert verify(2,gs+[('xor',(4,4))],[])==[]
    totals=[0,0,0]
    for _ in range(550):
        n=rng.randrange(1,6)
        g=[]
        for i in range(rng.randrange(1,8)):
            op=rng.choice(['and','and','xor','one'])
            args=tuple(rng.randrange(n+i) for j in range(2 if op=='and' else rng.randrange(4)))
            g.append((op,args))
        N=n+sum(op=='and' for op,_ in g)
        bound=n if rng.randrange(3) else N
        pins=[(rng.randrange(1<<bound),rng.randrange(2)) for j in range(rng.randrange(5))]
        if pins and rng.randrange(2): pins.append(pins[0])
        good=verify(n,g,pins)
        totals[min(len(good),2)]+=1
    print('550 randomized circuits; zero/unique/multiple fibers',totals,'plus explicit fanout and inconsistency controls passed')
