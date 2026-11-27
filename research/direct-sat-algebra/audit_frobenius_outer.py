"""Construct the norm-fiber parity Laurent polynomial explicitly and replay it."""
from itertools import permutations
from math import gcd
from affine_binomial import power
from quadratic_centroid import independent
from quadratic_target import apply_basis
from punctured_witness import BinaryField


def add_term(P,key,v):
    z=P.get(key,0)^v
    if z:
        P[key]=z
    else:
        P.pop(key,None)


def outer(f,j,U,V):
    """U,V are K elements for u_p*Tr(v_p x) error terms. Returns function on L*."""
    d=f.m
    g=gcd(j,d)
    m=d//g
    big=f.size-1
    small=(1<<g)-1
    N=big//small
    k=len(U)
    rows=[]
    for p,v in enumerate(V):
        row=[]
        for q,u in enumerate(U):
            A={(0,0):1} if p==q else {}
            # monomials w^b y^e; y inverse coefficients contain no negative powers
            for i in range(m):
                exponent=sum(1<<((j*l)%d) for l in range(i+1,m))
                a=f.mul(v,power(f,u,1<<((j*i)%d)))
                b=1
                for _ in range(d):
                    add_term(A,(b%small,exponent%big),a)
                    a=f.mul(a,a)
                    b=(b*2)%small
                    exponent=(exponent*2)%big
            row.append(A)
        rows.append(row)
    out={}
    for perm in permutations(range(k)):
        terms={(0,0):1}
        for i,p in enumerate(perm):
            new={}
            for (b,e),c in terms.items():
                for (bb,ee),cc in rows[i][p].items():
                    add_term(new,((b+bb)%small,(e+ee)%big),f.mul(c,cc))
            terms=new
        for (b,e),c in terms.items():
            if e%N:
                continue
            digit=e//N
            assert digit.bit_count()*m<=k*(m-1)
            mask=digit
            while True:
                add_term(out,(b-mask)%small,c)
                if not mask:
                    break
                mask=(mask-1)&digit
    return out


def audit(mod,j,k,rng):
    f=BinaryField(mod)
    d=f.m
    g=gcd(d,j)
    small=(1<<g)-1
    N=(f.size-1)//small
    U=[rng.randrange(1,f.size) for _ in range(k)]
    V=[rng.randrange(1,f.size) for _ in range(k)]
    cols=[]
    for i in range(d):
        x=1<<i
        y=power(f,x,1<<j)
        for u,v in zip(U,V):
            if f.trace(f.mul(v,x)):
                y^=u
        cols.append(y)
    bad={f.mul(apply_basis(cols,x),f.inverse(x)) for x in range(1,f.size)}
    P=outer(f,j,U,V)
    H=[x for x in range(1,f.size) if power(f,x,small)==1]
    hit=False
    for n in H:
        if n==1:
            if g>k:
                assert all(y in bad for y in range(1,f.size) if power(f,y,N)==1)
            continue
        w=f.inverse(1^n)
        observed=0
        for e,c in P.items():
            observed^=f.mul(c,power(f,w,e))
        assert observed==sum(y not in bad for y in range(1,f.size) if power(f,y,N)==n)%2
        hit|=bool(observed)
    if g>k and 0 in bad:
        assert hit
    return int(g>k and 0 in bad)


if __name__=='__main__':
    from random import Random
    rng=Random(9305)
    hits=tests=0
    for mod,j,k in ((19,2,1),(67,2,1),(67,3,2),(283,4,2),(283,2,2),(1033,5,2)):
        for _ in range(8):
            hits+=audit(mod,j,k,rng)
            tests+=1
    print(tests,'fully constructed outer polynomials matched every valid norm parity;',hits,'unsafe-center g>k cases')

    from deterministic_norm_lift import norm_preimage
    from quadratic_centroid import zero_combinations
    inverse_checks=repairs=0
    for mod,j in ((19,2),(67,2),(67,4),(283,4),(1033,5)):
        f=BinaryField(mod)
        d=f.m
        g=gcd(d,j)
        m=d//g
        H=zero_combinations(tuple(1<<i for i in range(d)),lambda x:power(f,x,1<<g)^x)
        N=(f.size-1)//((1<<g)-1)
        for _ in range(15):
            u,v=[rng.randrange(1,f.size) for _ in range(2)]
            c=f.mul(v,power(f,u,1<<((-j)%d)))
            if not f.trace(c):
                continue
            t=zero_combinations(H,lambda t:f.trace(f.mul(c,t)))[0]
            n=1^f.inverse(t)
            y=norm_preimage(f,g,n)
            assert n not in (0,1) and power(f,y,N)==n
            inv=[]
            for i in range(m):
                a=t
                for l in range(i+1,m):
                    a=f.mul(a,power(f,y,1<<((l*j)%d)))
                inv.append(a)
            def binv(x):
                v=0
                for i,a in enumerate(inv):
                    v^=f.mul(a,power(f,x,1<<((i*j)%d)))
                return v
            for i in range(d):
                x=1<<i
                assert binv(power(f,x,1<<j)^f.mul(y,x))==x
                inverse_checks+=1
            poly={0:1}
            for i,a in enumerate(inv):
                coef=f.mul(v,f.mul(a,power(f,u,1<<((i*j)%d))))
                e=(1-(1<<((i+1)*j%d)))%(f.size-1)
                for _ in range(d):
                    add_term(poly,e,coef)
                    e=(e*2)%(f.size-1)
                    coef=f.mul(coef,coef)
            assert poly[0]==1
            assert len(poly)<=1+d*m
            bad={f.mul(power(f,x,1<<j)^(u if f.trace(f.mul(v,x)) else 0),f.inverse(x))
                 for x in range(1,f.size)}
            for z in range(1,f.size):
                value=0
                for e,coef in poly.items():
                    value^=f.mul(coef,power(f,z,e))
                s=f.mul(y,f.mul(power(f,z,1<<j),f.inverse(z)))
                assert value==int(s not in bad)
            repairs+=1
    print(inverse_checks,'inverse-on-basis checks;',repairs,'rank-one Fourier tables and norm lifts checked')
