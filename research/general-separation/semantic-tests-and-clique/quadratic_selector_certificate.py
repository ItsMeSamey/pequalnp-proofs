"""Affine radical sections and degree-one Boolean Macaulay consequences.

Input forms are sets of squarefree monomial masks in primary variables.
Returned affine equations vanish at every selector with nonzero bias.
"""
from itertools import combinations
from random import Random


def reduce_word(x,basis):
    for i in sorted(basis,reverse=True):
        if x>>i&1:x^=basis[i]
    return x


def insert(x,basis):
    x=reduce_word(x,basis)
    if x:basis[x.bit_length()-1]=x


def kernel(rows,n):
    echelon={}
    for row in rows:insert(row,echelon)
    vectors=[]
    for free in range(n):
        if free in echelon:continue
        v=1<<free
        for i in sorted(echelon):
            if (v&echelon[i]).bit_count()%2:v|=1<<i
        vectors.append(v)
    return vectors


def value(poly,w):
    return sum(w&t==t for t in poly)%2


def poly_product(a,b):
    out=set()
    for x in a:
        for y in b:out.symmetric_difference_update((x|y,))
    return out


def certificate(q,forms):
    r=len(forms)
    if any(t<0 or t>>q or t.bit_count()>2 for p in forms for t in p):
        raise ValueError('forms must be squarefree quadratic masks on q variables')
    # Unknown coefficient of selector monomial k in section component j:
    # index j*(r+1)+k, with k=0 the constant.
    rows={}
    for i,p in enumerate(forms):
        for term in p:
            if term.bit_count()!=2:continue
            lo=term&-term
            a,b=lo.bit_length()-1,(term^lo).bit_length()-1
            for j,h in ((a,b),(b,a)):
                for k in range(r+1):
                    mon=(1<<i)|(1<<(k-1) if k else 0)
                    key=j,mon
                    rows[key]=rows.get(key,0)^(1<<(h*(r+1)+k))
    sections=kernel(rows.values(),q*(r+1))
    mons=[0]+[sum(1<<i for i in subset) for d in range(1,5) for subset in combinations(range(r),d)]
    positions={t:i for i,t in enumerate(mons)}
    echelon={}
    for vector in sections:
        coords=[{(1<<(k-1) if k else 0) for k in range(r+1)
                 if vector>>(j*(r+1)+k)&1} for j in range(q)]
        g=set()
        for i,p in enumerate(forms):
            for t in p:
                if not t:continue
                lo=t&-t
                sub=coords[lo.bit_length()-1]
                if t^lo:sub=poly_product(sub,coords[(t^lo).bit_length()-1])
                for m in sub:g.symmetric_difference_update((m|(1<<i),))
        for k in [0]+[1<<i for i in range(r)]:
            word=0
            for m in g:word^=1<<positions[m|k]
            insert(word,echelon)
    return sections,[row for i,row in sorted(echelon.items()) if i<=r]


def multiply(x,y,mod):
    n=mod.bit_length()-1
    ans=0
    while y:
        if y&1:ans^=x
        y>>=1
        x<<=1
        if x>>n:x^=mod
    return ans


def trace(x,mod):
    val=0
    for _ in range(mod.bit_length()-1):
        val^=x
        x=multiply(x,x,mod)
    assert val in (0,1)
    return val


def cubic_coordinates(x,mod):
    z=multiply(x,multiply(x,x,mod),mod)
    return sum(trace(multiply(1<<i,z,mod),mod)<<i for i in range(mod.bit_length()-1))


def basis_change(n,rng):
    rows=[1<<i for i in range(n)]
    for _ in range(8*n):
        a,b=rng.sample(range(n),2)
        rows[a]^=rows[b]
    return lambda x:sum(((v&x).bit_count()%2)<<i for i,v in enumerate(rows))


def tests():
    rng=Random(6179)
    for n,mod,copies in ((3,11,1),(3,11,2),(5,37,1)):
        q=n*copies
        for mixed in (False,True):
            A=basis_change(q,rng) if mixed else lambda x:x
            C=basis_change(q,rng) if mixed else lambda x:x
            shift=rng.randrange(1<<q) if mixed else 0
            offset=rng.randrange(1<<q) if mixed else 0
            def image(x):
                x=A(x)^shift
                return C(sum(cubic_coordinates((x>>(j*n))&((1<<n)-1),mod)<<(j*n)
                             for j in range(copies)))^offset
            vals=[image(x) for x in range(1<<q)]
            coeff=vals.copy()
            for i in range(q):
                for x in range(1<<q):
                    if x>>i&1:coeff[x]^=coeff[x^(1<<i)]
            forms=[{t for t,a in enumerate(coeff) if a>>i&1} for i in range(q)]
            sections,eqs=certificate(q,forms)
            support={s for s in range(1<<q) if sum((-1)**((s&v).bit_count()%2) for v in vals)}
            assert support=={0}
            constant_sections=[v for v in range(1<<q) if all(
                len({((vals[x]^vals[x^v])>>i)&1 for x in range(1<<q)})==1 for i in range(q))]
            assert constant_sections==[0]
            assert len(eqs)==(q if n==3 else 0)
            assert all((z&1)==0 for z in eqs)
            if n==5:
                assert not sections
                if not mixed:
                    for s in range(1,1<<q):
                        w=1
                        for _ in range(10):w=multiply(w,s,mod)
                        assert all(((s&(vals[x]^vals[x^w])).bit_count()%2)==1 for x in range(1<<q))
            print(q,'mixed',mixed,'sections',len(sections),'linear equations',len(eqs),'bias support',sorted(support))


if __name__=='__main__':tests()
