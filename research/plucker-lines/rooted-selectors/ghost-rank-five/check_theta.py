"""Check the asymmetric circuit descriptions independently on small binary instances."""
from itertools import combinations
from random import Random


def image(cols,x):
    value=0
    while x:
        bit=x & -x
        value^=cols[bit.bit_length()-1]
        x^=bit
    return value


def one(cols,ell,q,r):
    n=len(cols)
    # Quotient by the high bit q to make the lift coordinate explicit.
    w=[v%q for v in cols]
    g=sum((v//q)<<i for i,v in enumerate(cols))
    image_q=[image(w,x) for x in range(1<<n)]
    cycles=[x for x in range(1,1<<n) if image_q[x]==0]
    circuits=[x for x in cycles if all(x&y!=y for y in cycles if y<x)]
    roots=[c for c in circuits if c&2 and not c&1]
    def bit(v,x):return (v&x).bit_count()%2
    def submasks(x):
        v=x
        while v:
            yield v
            v=(v-1)&x
        yield 0
    if any(not bit(g,c) and not any(image_q[a]==w[0] for a in submasks(c)) for c in roots):
        return None
    expected=set()
    for d in range(1<<r):
        if not bit(d,cols[0]):continue
        forbidden=sum(bit(d,v)<<i for i,v in enumerate(cols))
        for x in cycles:
            if not x&forbidden and x&2 and not bit(g,x):
                expected.add((bit(d,q),bit(ell,x)))
    found=set()
    for k in roots:
        other=[c for c in circuits if not c&(k|1)]
        if bit(g,k):
            for m in (1,2):
                for ks in combinations(other,m):
                    x=k
                    for z in ks:
                        if z&x:break
                        x|=z
                    else:
                        if not bit(g,x) and all(image_q[a]!=w[0] for a in submasks(x)):
                            found.add((0,bit(ell,x)))
        else:
            if not any(image_q[a]==w[0] and bit(g,a)!=(cols[0]//q) for a in submasks(k)):
                continue
            for j in [0]+[a for a in other if bit(ell,a)]:
                x=k|j
                if all(not bit(g,c) for c in circuits if c&x==c):
                    found.add((1,bit(ell,x)))
    return expected==found


if __name__=='__main__':
    rng=Random(3492)
    checked=0
    for _ in range(1400):
        r=rng.randrange(3,6)
        q=1<<(r-1)
        n=rng.randrange(3,9)
        cols=[1,2]+[rng.randrange(2*q) for _ in range(n-2)]
        status=one(cols,rng.randrange(1<<n),q,r)
        if status is not None:
            assert status
            checked+=1
    print(checked,"asymmetric full weight tables verified")
