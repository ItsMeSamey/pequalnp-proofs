"""Finite tests for image saturation above a low-polar-rank selector span."""
from random import Random


def basis(words):
    rows={}
    for x in words:
        while x:
            p=x.bit_length()-1
            if p not in rows:
                rows[p]=x
                break
            x^=rows[p]
    return tuple(rows.values())


def span(generators):
    values=[0]
    for g in generators:values.extend([v^g for v in values])
    return set(values)


def polar(poly,n):
    packed=0
    for t in poly:
        if t.bit_count()==2:
            i=t&-t;j=t^i
            packed^=j<<(n*(i.bit_length()-1))
            packed^=i<<(n*(j.bit_length()-1))
    return packed


def closure(forms,n):
    r=len(forms);polars=[polar(p,n) for p in forms]
    matrices=[0]
    for b in polars:matrices.extend([v^b for v in matrices])
    rank=[len(basis((M>>(n*i))&((1<<n)-1) for i in range(n))) for M in matrices]
    D=()
    while True:
        t=len(basis(matrices[s] for s in D))
        new=basis([*D,*(s for s,v in enumerate(rank) if v<2*(r+t))])
        if len(new)==len(D):return D,t,rank
        D=new


def image(forms,n):
    def f(x):return sum((sum((x&t)==t for t in p)%2)<<i for i,p in enumerate(forms))
    return {f(x) for x in range(1<<n)}


def saturate(values,D,r):
    def proj(x):return tuple((d&x).bit_count()%2 for d in D)
    low={proj(x) for x in values}
    return {x for x in range(1<<r) if proj(x) in low}


def main():
    rng=Random(371)
    for j in range(72):
        r,n=rng.choice([(2,6),(2,8),(3,9)])
        forms=[{(1<<a)|(1<<b) for a in range(n) for b in range(a) if rng.randrange(2)} for i in range(r)]
        D,t,ranks=closure(forms,n)
        for _ in range(4):
            shifted=[p|{m for m in [0]+[1<<a for a in range(n)] if rng.randrange(2)} for p in forms]
            actual=image(shifted,n)
            assert saturate(actual,D,r)==actual
    # Outputs ab, (1+a)c, and a nondegenerate rank-ten quadratic on disjoint bits.
    forms=[{3},{5,4},{3<<(3+2*i) for i in range(5)}]
    D,t,ranks=closure(forms,13)
    assert span(D)=={0,1,2,3} and t==2 and min(ranks[4:])==10
    vals=image(forms,13)
    assert vals=={0,1,2,4,5,6} and saturate(vals,D,3)==vals
    assert saturate(vals,[1],3)!=vals
    for _ in range(9):
        shifted=[p.symmetric_difference({m for m in [0]+[1<<a for a in range(13)] if rng.randrange(2)}) for p in forms]
        actual=image(shifted,13)
        assert actual==saturate(actual,D,3)
    print('288 random shifts and ten 13-input cases passed; rank-ten equality retained, undersized D fails')


if __name__=='__main__':main()
