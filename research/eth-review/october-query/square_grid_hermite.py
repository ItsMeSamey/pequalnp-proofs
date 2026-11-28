"""Coordinatewise Hermite recovery on positive squares from existing normalized root jets."""
from math import comb
from tapered_jet_machine import valuation

def recover(a,u,m,p,coordinates,jet,*,even=False,trim=True):
    """jet(t,order,coordinate,bits) returns [z^order]G(t+2Lz) modulo 2^bits.
    even=True is an external exact symmetry certificate, not a heuristic.
    Otherwise both original signs are read and only the final doubled origin is divided.
    """
    if not (1<=u<=a and m>=u and min(p,coordinates)>=1): raise ValueError('invalid parameters')
    L=1<<a
    alpha=2*L
    h=(3*m+u-1)//u
    v_shell=u
    if trim:
        v_shell=next(v for v in range(1,u+1) if h*(L*(v-1)+(L>>v))>m*(L-1))
    ns={t:h*(v_shell-valuation(t)) for t in range(1,L) if valuation(t)<v_shell}
    data={}
    for t,n in ns.items():
        i=valuation(t)
        v=sum(k*(2*valuation(s)-valuation(t*t-s*s)) for s,k in ns.items() if s!=t)
        slope=a+2-i
        data[t]=(v,slope,v-(n-1)*slope)
    tgt=p+int(not even)
    loss=max(0,-min(x[2] for x in data.values()))
    modulus=1<<(tgt+loss)
    sums=[0]*coordinates
    requests=[]
    for t,n in ns.items():
        v,slope,worst=data[t]
        i=valuation(t)
        bits=tgt-worst
        if bits<=0: continue
        if bits>p+8*h*(L>>i)+8*m*(a+1): raise ArithmeticError('native precision insufficient')
        mod=1<<bits
        requests.append((t,n,bits,1 if even else 2))
        beta=2*t*alpha
        c=(alpha>>(1+i))*pow(t>>i,-1,mod)%mod
        unit=1
        factors=[]
        for s,k in ns.items():
            if s==t: continue
            delta=t*t-s*s
            iv=valuation(delta)
            if beta%(1<<iv): raise ArithmeticError('nonintegral squared-grid local ratio')
            odd=delta>>iv
            unit=unit*pow((-(s*s)>>(2*valuation(s)))*pow(odd,-1,modulus),k,modulus)%modulus
            factors.append(((beta>>iv)*pow(odd,-1,mod)%mod,k))
        for d in range(coordinates):
            row=[]
            for j in range(n):
                g=jet(t,j,d,bits)
                if not even: g+=(-1 if j%2 else 1)*jet(-t,j,d,bits)
                for l in range((j+1)//2,j):
                    g-=row[l]*comb(l,j-l)*pow(c,j-l,mod)
                row.append(g%mod)
            for coeff,k in factors:
                for _ in range(k):
                    for j in range(1,n): row[j]=(row[j]-coeff*row[j-1])%mod
            weight=unit
            for j,g in enumerate(row):
                shift=loss+v-j*slope
                if shift<0: raise ArithmeticError('insufficient accumulator')
                sums[d]=(sums[d]+((weight*g)<<shift))%modulus
                weight=weight*(-(t>>i))%modulus
    divisor=1<<(loss+int(not even))
    if any(x%divisor for x in sums): raise ArithmeticError('inconsistent paired jets')
    return tuple(x//divisor for x in sums),tuple(requests)
