from math import comb
from fractions import Fraction as F
from square_grid_hermite import recover

def check(a,u,m,p,even,trim):
    L=1<<a
    # Normalized physical slots from a single packet, with omitted endpoint factor.
    def mul(q,r):
        out=[F(0)]*(len(q)+len(r)-1)
        for i,A in enumerate(q):
            for j,B in enumerate(r): out[i+j]+=A*B
        return out
    def slot(d):
        q=[F(L)]
        den=1
        for t in range(-L,L):
            if t not in (-L,d): q=mul(q,[-t,1])
            if t: den*=-t
        return [x/den for x in q]
    q=slot(0) if even else [x+2*y for x,y in zip(slot(0),slot(1))]
    poly=[F(1)]
    for _ in range(m): poly=mul(poly,q)
    poly[0]+=6
    def jet(t,j,d,bits):
        mod=1<<bits
        x=sum(poly[k]*comb(k,j)*t**(k-j) for k in range(j,len(poly)))*(2*L)**j
        x=F(x)
        assert x.denominator%2
        return x.numerator*pow(x.denominator,-1,mod)%mod
    out,req=recover(a,u,m,p,1,jet,even=even,trim=trim)
    assert out==(int(poly[0])%(1<<p),)
    return len(req),sum(n*sg for t,n,prec,sg in req)
if __name__=='__main__':
    for even in (False,True):
        a=check(3,3,3,7,even,False)
        b=check(3,3,3,7,even,True)
        assert b[0]<a[0] and b[1]<a[1]
        print('PASS physical normalized product, even=',even,'full/trimmed node and jet requests',a,b)
