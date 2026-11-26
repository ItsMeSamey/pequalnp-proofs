"""Small independent oracle checks for projected CNF width, local extraction, and reduction."""
from itertools import combinations, product
from collections import Counter
from random import Random

def span(xs):
    out={0}
    for x in xs:
        out |= {z^x for z in out}
    return out

def parity(a,x):
    return (a&x).bit_count()%2

def width_tests():
    n=4
    words=set(range(1<<n))
    spaces={frozenset({0})}
    for v in words:
        spaces |= {frozenset(set(u)|{z^v for z in u}) for u in spaces}
    cases=0
    for u in spaces:
        cosets={frozenset(x^s for s in u) for x in words}
        dual={a for a in words if all(parity(a,x)==0 for x in u)}
        for q in cosets:
            ref=min(q)
            for w in range(1,n+1):
                masks={s for s in words if s.bit_count()<=w}
                closed=set(words)
                for s in masks:
                    seen={x&s for x in q}
                    closed={x for x in closed if (x&s) in seen}
                small_dual=dual&masks
                affine_closed={x for x in words if all(parity(a,x^ref)==0 for a in small_dual)}
                assert affine_closed==closed
                assert (closed==q)==(span(small_dual)==dual)
                cases+=1
    for mask in range(1,256):
        r={v for v in range(8) if (mask>>v)&1}
        base=min(r)
        hull={base^v for v in span(x^base for x in r)}
        defects=hull-r
        assert {x for x in range(8) if x in hull and x not in defects}==r
    print(f'{cases} coset-width checks, 255 nonempty ternary relations')

def reduction_test(source, n):
    usages=[[] for _ in range(n)]
    local=[]; coords=0
    for clause in source:
        dest=[]
        for v,b in clause:
            usages[v].append(coords)
            dest.append((coords,b))
            coords+=1
        local.append(dest)
    for group in usages:
        if not group:
            coords+=1
        if len(group)>=2:
            for a,b in zip(group,group[1:]+group[:1]):
                local.append([(a,0),(b,1)])
    d=coords
    for clause in local:
        while len(clause)<3:
            clause.append((coords,1))
            coords+=1
    t=max(3,coords-1)
    q=t+1
    assert q<=13
    # A prism on 2t vertices has q=t+1 nontree edges.
    edges=[(i,(i+1)%t) for i in range(t)]+[(i+t,(i+1)%t+t) for i in range(t)]+[(i,i+t) for i in range(t)]
    tree=list(range(t-1))+list(range(2*t,3*t))
    cotree=sorted(set(range(3*t))-set(tree))
    out=[[(cotree[i],b) for i,b in c] for c in local]
    for i in range(d,q):
        for a,b in product((0,1),repeat=2):
            out.append([(cotree[i],0),(cotree[(i+1)%q],a),(cotree[(i+2)%q],b)])
    stars=[[i for i,(a,b) in enumerate(edges) if v in (a,b)] for v in range(2*t)]
    for star in stars:
        for word in product((0,1),repeat=3):
            if sum(word)%2:
                out.append([(e,1-b) for e,b in zip(star,word)])
    assert all(len({v for v,b in c})==3 for c in out)
    assert max(Counter(v for c in out for v,b in c).values())<=23
    def ok(f,x):
        return all(any(((x>>v)&1)==b for v,b in c) for c in f)
    counter=0
    for y in range(1<<q):
        x=sum(1<<e for i,e in enumerate(cotree) if y>>i&1)
        rem=set(tree)
        # Solve degree-one residuals in original coordinates.
        while rem:
            for star in stars:
                active=rem.intersection(star)
                if len(active)==1:
                    edge=active.pop()
                    if sum((x>>j)&1 for j in star)%2:
                        x|=1<<edge
                    rem.remove(edge)
        assert all(sum((x>>j)&1 for j in star)%2==0 for star in stars)
        counter+=ok(out,x)
    assert counter==sum(ok(source,x) for x in range(1<<n))

if __name__=='__main__':
    width_tests()
    rng=Random(378)
    for _ in range(60):
        n=rng.randint(1,3)
        source=[[(v,rng.randrange(2)) for v in rng.sample(range(n),rng.randint(0,n))]
                for _ in range(rng.randrange(3))]
        reduction_test(source,n)
    print('60 complete reductions checked on all graphic codewords, including empty clauses and free variables.')
