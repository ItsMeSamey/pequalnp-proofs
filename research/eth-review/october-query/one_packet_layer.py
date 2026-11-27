"""One complete L=2 local interpolation/recovery layer, direct child base cases."""
from fractions import Fraction
from packet_entry_tape import Ring, canonical_lift, packet_entry
from tapered_jet_machine import recover, inverse_odd, odd_part, valuation


def unit_inverse(r,x):
    """Only used on units with no V terms."""
    y=r.power(x,(1<<len(r.f))-2)
    for _ in range(r.p.bit_length()):
        y=r.mul(y,r.add(r.scalar(2),r.neg(r.mul(x,y))))
    assert r.mul(x,y)==r.scalar(1)
    return y


def polynomial_at_shift(r,t,zeta,delta):
    """W for the grid [-2,1]. Coefficients of the shifted polynomial are integral at 2."""
    poly=[1]
    denom=1
    for q in range(-2,2):
        if q: denom *= -q
        if q!=delta:
            out=[0]*(len(poly)+1)
            for j,c in enumerate(poly):
                out[j]+=(t-q)*c
                out[j+1]+=4*c
            poly=out
    val=r.scalar(0)
    for c in reversed(poly):
        m=Fraction(c,denom)
        assert m.denominator%2
        val=r.add(r.mul(val,zeta),r.scalar(m.numerator*inverse_odd(m.denominator,r.p)))
    return val


def interpolate(r,points,values):
    """Newton divided differences, then ordinary monomial coefficients."""
    d=values[:]
    for size in range(1,len(d)):
        for j in reversed(range(size,len(d))):
            denominator=r.add(points[j],r.neg(points[j-size]))
            d[j]=r.mul(r.add(d[j],r.neg(d[j-1])),unit_inverse(r,denominator))
    result=[d[-1]]
    for j in reversed(range(len(d)-1)):
        out=[d[j]]+[r.scalar(0)]*len(result)
        for k,c in enumerate(result):
            out[k]=r.add(out[k],r.neg(r.mul(points[j],c)))
            out[k+1]=r.add(out[k+1],c)
        result=out
    return result


def layer(tables,birth,p,ell):
    """Four old unary vertices: row0,row1,column0,column1; each table has two words."""
    a=u=1; m=2; degree=6; h=6
    # All coordinates distinct; only 7 of the 8 elements of F_8 are needed.
    field=(1,1,0)
    jets={}
    counts={'nodes':0,'evaluations':0,'tuple_products':0,'child_contractions':0}
    for t in (-1,1):
        pt=p+8*h*2+8*m*2
        r=Ring(pt,field,ell)
        zero,one=r.scalar(0),r.scalar(1)
        points=[tuple((j>>b)&1 for b in range(3))+(0,)*(3*(ell-1)) for j in range(degree+1)]
        old=[[canonical_lift(val,birth,pt) for val in tab] for tab in tables]
        values=[]
        for ptval in points:
            W={delta:polynomial_at_shift(r,t,ptval,delta) for delta in (-1,0,1)}
            total=zero
            # Only b=0 has nonzero source moment since each parity tile has j=0.
            # Higher powers of that mode cannot occur since each target has one physical row.
            for beta0 in (0,1):
                for beta1 in (0,1):
                    if beta0+beta1>=pt: continue
                    beta=(beta0,beta1)
                    prod=one
                    for g in (0,1):
                        subtotal=zero
                        # Each child has two edge bits; sum directly at this base case.
                        for y in (0,1):
                            for x in (0,1):
                                local=W[1-2*g] if x else zero
                                crossing=W[0]
                                affine=[(local if y else r.add(one,r.neg(local)),
                                         [(0,crossing if y else r.neg(crossing))])]
                                entry=packet_entry(r,affine,[beta[g]],[(r.scalar(x),beta[1-g])])
                                factor=r.mul(old[g][y],old[2+1-g][x])
                                subtotal=r.add(subtotal,r.mul(entry,factor))
                        prod=r.mul(prod,subtotal)
                        counts['child_contractions']+=1
                    total=r.add(total,prod)
                    counts['tuple_products']+=1
            values.append(total)
            counts['evaluations']+=1
        jets[t]=interpolate(r,points,values)[:h]
        counts['nodes']+=1
    def query(t,j,c,pt):
        return jets[t][j][c]
    result=recover(a,u,m,p,3*ell,query)
    return tuple(result),counts


def direct_origin(tables,birth,p,ell):
    r=Ring(p,(1,1,0),ell)
    total=r.scalar(0)
    for x0 in (0,1):
        for x1 in (0,1):
            prod=r.scalar(1)
            for i,x in enumerate((x0,x1,x0,x1)):
                prod=r.mul(prod,canonical_lift(tables[i][x],birth,p))
            total=r.add(total,prod)
    return total
