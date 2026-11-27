"""Finite controls for the signed trace phase of xy+L(x)+M(y)+c."""
from random import Random
from hidden_cubing_polar import mul,power,apply
from implicit_suffix_controls import walsh


def tr(x,mod):
    y=0
    for _ in range(mod.bit_length()-1):
        y^=x
        x=mul(x,x,mod)
    assert y in (0,1)
    return y


def adjoint(columns,mod):
    r=len(columns)
    dual={}
    for a in range(1<<r):
        dual[sum(tr(mul(a,1<<j,mod),mod)<<j for j in range(r))]=a
    assert len(dual)==1<<r
    return tuple(dual[sum(tr(mul(1<<i,v,mod),mod)<<j for j,v in enumerate(columns))]
                 for i in range(r))


def linearized(columns,mod):
    # Reconstruct sum_j A_j s^(2^j) by eliminating the Moore evaluation matrix.
    r=len(columns)
    rows=[[power(1<<i,1<<j,mod) for j in range(r)]+[v] for i,v in enumerate(columns)]
    for i in range(r):
        k=next(k for k in range(i,r) if rows[k][i])
        rows[i],rows[k]=rows[k],rows[i]
        scale=power(rows[i][i],(1<<r)-2,mod)
        rows[i]=[mul(a,scale,mod) for a in rows[i]]
        for k in range(r):
            if k!=i:
                z=rows[k][i]
                rows[k]=[a^mul(z,b,mod) for a,b in zip(rows[k],rows[i])]
    return [row[-1] for row in rows]


def check(L,M,c,mod):
    r=len(L); Q=1<<r
    a=linearized(adjoint(L,mod),mod)
    b=linearized(adjoint(M,mod),mod)
    coeff={1:c}
    for i,u in enumerate(a):
        for j,v in enumerate(b):
            e=((1<<i)+(1<<j)-1)%(Q-1)
            coeff[e]=coeff.get(e,0)^mul(u,v,mod)
    phase={}
    for e,z in coeff.items():
        for _ in range(r):
            phase[e]=phase.get(e,0)^z
            z=mul(z,z,mod)
            e=2*e%(Q-1)
    phase={e:z for e,z in phase.items() if z}
    def scalar(s):
        bit=0
        for e,z in phase.items():bit^=mul(z,power(s,e,mod),mod)
        assert bit in (0,1)
        return bit
    psi=[scalar(s) for s in range(Q)]
    assert psi[0]==phase.get(0,0)
    H=walsh([(-1)**b for b in psi])
    hist=[0]*Q
    for x in range(Q):
        for y in range(Q):hist[mul(x,y,mod)^apply(L,x)^apply(M,y)^c]+=1
    for y in range(Q):
        idx=sum(tr(mul(1<<j,y,mod),mod)<<j for j in range(r))
        assert hist[y]==Q+H[idx]-(-1)**psi[0]
    coeffs=psi.copy()
    for i in range(r):
        for s in range(Q):
            if s>>i&1:coeffs[s]^=coeffs[s^(1<<i)]
    degree=max((s.bit_count() for s,v in enumerate(coeffs) if v),default=0)
    assert degree==max((s.bit_count() for s in phase),default=0)
    rank=None
    if degree<=2:
        radical=sum(len({psi[x]^psi[x^s] for x in range(Q)})==1 for s in range(Q))
        rank=r-(radical.bit_length()-1)
    return psi,degree,rank


if __name__=='__main__':
    rng=Random(3692)
    for r,mod in ((3,11),(5,37)):
        Q=1<<r
        def frob(k):return [power(1<<i,1<<k,mod) for i in range(r)]
        zero=[0]*r
        assert check(zero,zero,0,mod)[1:]==(0,0)
        assert check(frob(0),frob(0),0,mod)[1:]==(1,0)
        L=adjoint(frob(1),mod)
        psi,d,rank=check(L,L,0,mod)
        assert psi==[tr(power(s,3,mod),mod) for s in range(Q)] and (d,rank)==(2,r-1)
        for _ in range(16):
            check([rng.randrange(Q) for i in range(r)],[rng.randrange(Q) for i in range(r)],rng.randrange(Q),mod)
        # Exponent 7 collapses to exponent 0 in F8: canonical extension is 1 even at zero.
        L=adjoint(frob(2),mod)
        psi,d,rank=check(L,L,0,mod)
        if r==3:assert psi==[1]*Q and (d,rank)==(0,0)
        else:assert d==3 and rank is None
        print('F',Q,'20 cases; cubic-trace polar rank',r-1,'seventh-power trace degree',d)
