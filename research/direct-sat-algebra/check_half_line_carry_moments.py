"""Independent half-line moment replay by cyclic carries and alternating restriction."""
from itertools import combinations
from math import comb
from random import Random
from additive_slope_prefix import _det,dickson
from affine_binomial import power
from hidden_product_network import encoder
from product_slack import linearized
from punctured_witness import BinaryField
from quadratic_target import apply_basis
from selfadjoint_coset_sampler import subfield_basis


def paths(a,r):
    H=(1<<a)-1
    b=H-r
    def visit(i,c,start,seq):
        if i==a:
            if c==start:
                yield seq
            return
        for nxt in (0,1):
            u=((b>>i)&1)+2*nxt-c
            if 0<=u<=2:
                yield from visit(i+1,nxt,start,seq+(u,))
    for c in (0,1):
        yield from visit(0,c,c,())


def moment(f,D,rep,r):
    a=f.m//2
    value=_det(f,[row[:] for row in D]) if r==0 else 0
    lo=[power(f,rep,1<<i) for i in range(a)]
    hi=[power(f,rep,1<<(a+i)) for i in range(a)]
    for pat in paths(a,r):
        cols=[]
        factor=1
        for i,u in enumerate(pat):
            if u==0:
                cols.extend([[(i,1)],[(i+a,1)]])
            elif u==1:
                cols.append([(i,f.sqrt(hi[i])),(i+a,f.sqrt(lo[i]))])
            else:
                factor=f.mul(factor,f.mul(lo[i],hi[i]))
        if len(cols)%2:
            continue
        def entry(x,y):
            z=0
            for i,b in x:
                for j,c in y:
                    z^=f.mul(D[i][j],f.mul(b,c))
            return z
        value^=f.mul(factor,_det(f,[[entry(x,y) for y in cols] for x in cols]))
    return value


if __name__=='__main__':
    # Aggregate integer path-count identity (all weights except r=H).
    for a in range(1,9):
        co=[1]
        for i in range(a):
            co=[sum(co[j-d] for d in (0,1,2) if 0<=j-d<len(co)) for j in range(len(co)+2)]
        H=(1<<a)-1
        for k in range(a):
            assert sum(sum(1 for _ in paths(a,r)) for r in range(H) if r.bit_count()==k)==2*co[2*k]
    rng=Random(579)
    checks=0
    for mod,reps in ((19,64),(67,48),(283,6)):
        f=BinaryField(mod)
        a=f.m//2
        H=(1<<a)-1
        L=[apply_basis(subfield_basis(f),j) for j in range(1,H+1)]
        dual=encoder([f.trace_row(1<<j) for j in range(f.m)])
        edges=list(combinations(range(f.m),2))
        for rep_idx in range(reps):
            code=rep_idx if f.m==4 else rng.getrandbits(len(edges))
            cols=[0]*f.m
            for j,(p,q) in enumerate(edges):
                if code>>j&1:
                    cols[p]^=dual(1<<q)
                    cols[q]^=dual(1<<p)
            bad={f.mul(apply_basis(cols,x),f.inverse(x)) for x in range(1,f.size)}
            D=dickson(f,linearized(f,cols))
            for rep in (1,rng.randrange(1,f.size)):
                good=[x for x in L if f.mul(rep,x) not in bad]
                for r in range(H):
                    expect=0
                    for x in good:
                        expect^=power(f,x,r)
                    assert expect==moment(f,D,rep,r)
                    checks+=1
    print(checks,'direct field-valued half-line moments; aggregate transfer identity through a=8')
