"""Recover polar symmetries by linear algebra. Bounded field tests run as main."""
from random import Random


def independent(rows):
    basis={}
    for v in rows:
        while v:
            k=v.bit_length()-1
            if k not in basis:
                basis[k]=v
                break
            v^=basis[k]
    return basis


def nullspace(rows,width):
    basis=independent(rows)
    result=[]
    for k in range(width):
        if k in basis:continue
        v=1<<k
        for pivot,row in sorted(basis.items()):
            if (row&v).bit_count()%2:v|=1<<pivot
        result.append(v)
    return result


def apply(matrix,v):
    result=0
    while v:
        low=v&-v
        result^=matrix[low.bit_length()-1]
        v^=low
    return result


def compose(a,b):
    return tuple(apply(a,col) for col in b)


def recover(beta,n):
    # Variables are the packed columns of A followed by the packed columns of U.
    offset=n*n
    rows=[]
    for i in range(n):
        for j in range(i):
            equations=[0]*n
            for k in range(n):
                for h in range(n):
                    if beta[k][j]>>h&1:equations[h]^=1<<(n*i+k)
                    if beta[i][k]>>h&1:equations[h]^=1<<(n*j+k)
                    if beta[i][j]>>k&1:equations[h]^=1<<(offset+n*k+h)
            rows.extend(equations)
    vectors=nullspace(rows,2*offset)
    def unpack(v):
        return tuple((v>>(i*n))&((1<<n)-1) for i in range(n))
    return [(unpack(v),unpack(v>>offset)) for v in vectors]


def mul(a,b,mod):
    out=0
    while b:
        if b&1:out^=a
        b>>=1
        a<<=1
        if a>=1<<(mod.bit_length()-1):a^=mod
    return out


def power(x,k,mod):
    y=1
    while k:
        if k&1:y=mul(y,x,mod)
        x=mul(x,x,mod)
        k>>=1
    return y


def invertible(n,rng):
    cols=[1<<i for i in range(n)]
    for _ in range(10*n):
        a,b=rng.sample(range(n),2)
        cols[a]^=cols[b]
    return tuple(cols)


def pack(cols,n):
    return sum(c<<(j*n) for j,c in enumerate(cols))


def control(m,blocks,mixed,rng):
    mod={5:37,7:131}[m]
    n=m*blocks
    C=invertible(n,rng) if mixed else tuple(1<<i for i in range(n))
    D=invertible(n,rng) if mixed else tuple(1<<i for i in range(n))
    off=rng.randrange(1<<n) if mixed else 0
    mask=(1<<m)-1
    linear=tuple(rng.randrange(1<<n) for _ in range(n))
    def F(x):
        w=apply(C,x)^off
        y=sum(power((w>>(i*m))&mask,3,mod)<<(i*m) for i in range(blocks))
        return apply(D,y)^apply(linear,x)^off
    beta=[[F((1<<i)^(1<<j))^F(1<<i)^F(1<<j)^F(0) for j in range(n)] for i in range(n)]
    pairs=recover(beta,n)
    assert len(pairs)==n
    algebra=[a for a,u in pairs]
    basis=independent(pack(a,n) for a in algebra)
    assert len(basis)==n
    for a in algebra:
        for b in algebra:
            p=compose(a,b)
            assert p==compose(b,a)
            assert len(independent([*basis.values(),pack(p,n)]))==n
    # In the verified commutative algebra, E^2=E is a linear equation.
    defect=[pack(compose(a,a),n)^pack(a,n) for a in algebra]
    coefficients=nullspace([sum(((col>>k)&1)<<j for j,col in enumerate(defect))
                            for k in range(n*n)],n)
    assert len(coefficients)==blocks
    idempotents=set()
    for z in range(1<<blocks):
        word=apply([pack(a,n) for a in algebra],apply(coefficients,z))
        e=tuple((word>>(i*n))&((1<<n)-1) for i in range(n))
        assert compose(e,e)==e
        idempotents.add(tuple(apply(C,c) for c in e))
    for s in range(1<<blocks):
        allowed=sum(mask<<(m*i) for i in range(blocks) if s>>i&1)
        assert tuple(c&allowed for c in C) in idempotents
    print('field degree',m,'blocks',blocks,'mixed',mixed,'kernel',len(pairs),'idempotents',len(idempotents))


def trace_exponents(coeff,mod):
    m=len(coeff)
    order=(1<<m)-1
    terms={}
    for i,c in enumerate(coeff):
        e=((1<<i)-3)%order
        for _ in range(m):
            terms[e]=terms.get(e,0)^c
            e=2*e%order
            c=mul(c,c,mod)
    return all(c==0 for c in terms.values())


def test_permutations(rng):
    m,mod=5,37
    cases=[[0]*m]
    # Translation of a cube: linear part a^2 x + a x^2.
    for a in range(1,32):cases.append([mul(a,a,mod),a,0,0,0])
    cases.extend([[rng.randrange(32) for _ in range(m)] for _ in range(300)])
    hits=0
    for coeff in cases:
        image=set()
        for x in range(32):
            y=power(x,3,mod)
            for i,c in enumerate(coeff):y^=mul(c,power(x,1<<i,mod),mod)
            image.add(y)
        assert trace_exponents(coeff,mod)==(len(image)==32)
        hits+=len(image)==32
    print('GF32 linear perturbations',len(cases),'permutations',hits)


if __name__=='__main__':
    rng=Random(3598)
    for m,b in ((5,1),(5,2),(7,1)):
        for mixed in (False,True):control(m,b,mixed,rng)
    test_permutations(rng)
