"""Small physical ring controls for row Möbius moments and selected-port cancellation."""
from itertools import product
from random import Random
from packet_entry_tape import Ring,canonical_lift
from one_packet_layer import polynomial_at_shift


def mobius(r,table):
    c=list(table)
    for j in range((len(c)-1).bit_length()):
        for m in range(len(c)):
            if m>>j&1:
                c[m]=r.add(c[m],r.neg(c[m^(1<<j)]))
    return c


def run(r,rows,cols):
    def word(x,edges):
        return sum(((x>>e)&1)<<j for j,e in enumerate(edges))
    zero,one=r.scalar(0),r.scalar(1)
    def mul(xs):
        v=one
        for a in xs: v=r.mul(v,a)
        return v
    def add(xs):
        v=zero
        for a in xs: v=r.add(v,a)
        return v
    m=sum(len(E) for E,t in rows)
    direct=add(mul(t[word(x,E)] for E,t in rows+cols) for x in range(1<<m))
    opts=[]
    for E,t in rows:
        opts.append([(sum(1<<e for i,e in enumerate(E) if s>>i&1),v)
                     for s,v in enumerate(mobius(r,t)) if v!=zero])
    total=zero
    for choice in product(*opts):
        content=sum(min((v&-v).bit_length()-1 for v in c if v) for _,c in choice)
        if content>=r.p: continue
        mask=sum(s for s,c in choice)
        moments=[add(val for x,val in enumerate(t) if x&word(mask,E)==word(mask,E)) for E,t in cols]
        total=r.add(total,mul([c for _,c in choice]+moments))
    assert total==direct


if __name__=='__main__':
    rng=Random(810)
    for trial in range(150):
        r=Ring(2+trial%5,(1,1,0),2)
        # Three-port COPY and signed OR form the row shore; columns are equality pairs.
        def table(f,d):
            birth=1+trial%6
            weight=tuple(rng.randrange(1<<birth) for _ in range(6)) if trial%2 else r.scalar(1)
            return [canonical_lift(weight,birth,r.p) if f(x) else r.scalar(0) for x in range(1<<d)]
        perm=rng.sample(range(6),6)
        rows=[(perm[:3],table(lambda x:x in (0,7),3)),(perm[3:],table(lambda x:x!=(trial%8),3))]
        cols=[([i,i+3],table(lambda x:x in (0,3),2)) for i in range(3)]
        run(r,rows,cols)
    # Three distinct L=2 packets, one real target at slot 0 of each, all on one COPY3.
    r=Ring(12,(1,1,0),2)
    W=polynomial_at_shift(r,1,r.scalar(1),0)
    assert W!=r.scalar(0) and r.power(W,3)!=r.scalar(0)
    direct=r.scalar(0)
    for y in (0,7):
        a=r.scalar(1)
        for i in range(3): a=r.mul(a,W if y>>i&1 else r.neg(W))
        direct=r.add(direct,a)
    c=mobius(r,[r.scalar(int(y in (0,7))) for y in range(8)])
    assert max(s.bit_count() for s,v in enumerate(c) if v!=r.scalar(0))==2
    assert direct==c[7]==r.scalar(0)
    print('150 OR/COPY native terminal rings passed; all-real triple route has nonzero individual factors and zero COPY3 coefficient')
