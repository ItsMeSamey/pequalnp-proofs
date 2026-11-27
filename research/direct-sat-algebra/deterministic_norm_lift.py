"""Deterministic norm preimage in a supplied binary field and its embedded subfield."""
from affine_binomial import power
from punctured_chart_witness import power_chart


def _primary(order,p):
    primary=1
    while order%p==0:
        order//=p
        primary*=p
    return primary


def _component(f,n,order,part):
    if part==1:return 1
    other=order//part
    return power(f,n,other*pow(other,-1,part))


def _log(f,base,target,p,order):
    """Pohlig–Hellman digits in a cyclic subgroup of known p-power order."""
    step=power(f,base,order//p)
    digits={}
    v=1
    for j in range(p):
        digits[v]=j
        v=f.mul(v,step)
    residue=target
    inv=f.inverse(base)
    x=0
    place=1
    while place<order:
        digit=digits[power(f,residue,order//(p*place))]
        x+=digit*place
        residue=f.mul(residue,power(f,inv,digit))
        inv=power(f,inv,p)
        place*=p
    if residue!=1:raise ArithmeticError("discrete log replay failed")
    return x


def norm_preimage(field,g,n):
    """Return y in GF(2^d)* with Norm(y)=n in its degree-g subfield."""
    f=field
    if type(g)!=int or g<1 or f.m%g:raise ValueError("invalid subfield degree")
    if type(n)!=int or not 0<n<f.size:raise ValueError("invalid nonzero target")
    base_order=(1<<g)-1
    if power(f,n,base_order)!=1:raise ValueError("target outside subfield")
    if n==1:return 1
    order=f.size-1
    exponent=order//base_order
    m=f.m//g
    rest=base_order
    factors=[]
    for p in range(2,m+1):
        if m%p or rest%p:continue
        # Any composite divisor's prime factors were already stripped from rest.
        part=_primary(rest,p)
        rest//=part
        target=_component(f,n,base_order,part)
        if target!=1:factors.append((p,part,target))
    answer=1
    if rest>1:
        answer=power(f,_component(f,n,base_order,rest),pow(m,-1,rest))
    if factors:
        chart=power_chart(f.m,1,f.mul)
        for p,part,target in factors:
            size=_primary(order,p)
            for i in range(1,f.size):
                gen=power(f,chart.decode(i),order//size)
                if power(f,gen,size//p)!=1:break
            else:raise ArithmeticError("no maximal primary generator")
            image=power(f,gen,exponent)
            log=_log(f,image,target,p,part)
            answer=f.mul(answer,power(f,gen,log))
    if power(f,answer,exponent)!=n:raise ArithmeticError("norm replay failed")
    return answer
