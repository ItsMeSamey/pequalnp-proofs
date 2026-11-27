"""Independent verifier for low-space coefficients of trace-prefix products."""
from itertools import product
from random import Random
from punctured_witness import BinaryField


def coefficient(f,a,rows,r):
    # rows[j][0] constant, rows[j][i+1] coefficient of X^(2^i).
    h=len(rows)
    H=(1<<a)-1
    if not 0<=r<H:
        raise ValueError("residue out of range")
    total=0
    for subset in range(1<<h):
        es=[]
        for i in range(a+1):
            e=[1]
            for j in range(h):
                if subset>>j&1:
                    w=rows[j][i]
                    e.append(0)
                    for k in reversed(range(1,len(e))):
                        e[k]^=f.mul(e[k-1],w)
            es.append(e)
        for initial in range(h+1):
            dp={(k,initial):v for k,v in enumerate(es[0]) if v}
            for i in range(a):
                nxt={}
                for (picks,c),v in dp.items():
                    for b,w in enumerate(es[i+1][:h-picks+1]):
                        q=b+c-((r>>i)&1)
                        if not w or q<0 or q%2:
                            continue
                        key=(picks+b,q//2)
                        nxt[key]=nxt.get(key,0)^f.mul(v,w)
                dp=nxt
            total^=dp.get((h,initial),0)
    return total


def direct(f,a,rows):
    H=(1<<a)-1
    p=[1]+[0]*(H-1)
    for row in rows:
        nxt=[0]*H
        for r,v in enumerate(p):
            for e,w in zip((0,*[1<<i for i in range(a)]),row):
                nxt[(r+e)%H]^=f.mul(v,w)
        p=nxt
    return p


if __name__=='__main__':
    rng=Random(932)
    f=BinaryField(7)
    checks=0
    for a in range(1,5):
        for h in range(6):
            for _ in range(5):
                rows=[[rng.randrange(f.size) for _ in range(a+1)] for _ in range(h)]
                ref=direct(f,a,rows)
                for r,w in enumerate(ref):
                    assert coefficient(f,a,rows,r)==w
                    checks+=1
    print(checks,'all-residue checks with arbitrary factors, empty product, constants and wrapped powers')

    from streaming_line_prefix import find_columns,coefficient as actual
    from hidden_product_network import encoder
    from quadratic_target import apply_basis
    from selfadjoint_coset_sampler import subfield_basis
    from itertools import combinations
    coefficients=answers=0
    for mod,limit in ((7,2),(19,64),(67,48),(283,12)):
        f=BinaryField(mod)
        d=f.m
        a=d//2
        sub=[apply_basis(subfield_basis(f),i) for i in range(1<<a)]
        for h in range(a+1):
            factors=[(rng.randrange(2),rng.choice(sub)) for _ in range(h)]
            rows=[]
            for c,b in factors:
                row=[c]
                for _ in range(a):
                    row.append(b)
                    b=f.mul(b,b)
                rows.append(row)
            for r,val in enumerate(direct(f,a,rows)):
                assert actual(f,factors,a,r)==val
                coefficients+=1
        dual=encoder([f.trace_row(1<<j) for j in range(d)])
        pairs=list(combinations(range(d),2))
        for rep in range(limit):
            code=rep if d<=4 else rng.randrange(1<<len(pairs))
            shift=rng.randrange(f.size)
            cols=[f.mul(shift,1<<i) for i in range(d)]
            for j,(k,l) in enumerate(pairs):
                if (code>>j)&1:
                    cols[k]^=dual(1<<l)
                    cols[l]^=dual(1<<k)
            bad={f.mul(apply_basis(cols,x),f.inverse(x)) for x in range(1,f.size)}
            for h in (0,a//2,a,None):
                assert find_columns(f,cols,h) not in bad
                answers+=1
    print(coefficients,'production coefficients and',answers,'original-column witnesses passed')
