from itertools import combinations, product
from random import Random

def span(columns):
    points = {0}
    for v in columns:
        points |= {u ^ v for u in points}
    return points

def dot(a,b):
    return (a&b).bit_count()%2

rng=Random(47)
for trial in range(200):
    n=rng.randint(3,6)
    graph=[((1<<i)^(1<<j),rng.randrange(4)) for i,j in combinations(range(n),2) if rng.randrange(2)]
    basis=[rng.choice(tuple(span([3<<i for i in range(n-1)]))) for _ in range(2)]
    U=list(span(basis))
    extra=[(rng.choice(U),rng.randrange(4)) for _ in range(5)]
    dual=[rng.choice(U),rng.choice(U)]
    direct=set()
    adapted=set()
    fullmask=(1<<n)-1
    for d in range(0,1<<n,2):
        ds=sum(dot(d,v)<<i for i,v in enumerate(dual))
        combined=span([v|(a<<n) for v,a in graph+extra if not dot(d,v)])
        direct.update(ds^(t>>n) for t in combined if not (t&fullmask))
    for sample in range(0,1<<n,2):
        compatible=[d for d in range(0,1<<n,2) if all(dot(d^sample,v)==0 for v in U)]
        for state in span([v|(a<<n) for v,a in extra if not dot(sample,v)]):
            w=state&fullmask
            alpha=state>>n
            terminals=[i for i in range(n) if w>>i&1]
            for colors in product((0,1),repeat=len(terminals)):
                groups=[[j for j,c in zip(terminals,colors) if c==v] for v in (0,1)]
                if any(len(g)%2 for g in groups):continue
                dummy=[(1<<x)^(1<<y) for g in groups for x,y in zip(g[::2],g[1::2])]
                for d in compatible:
                    if any(dot(d,e) for e in dummy):continue
                    choices=span([v|(a<<n) for v,a in graph if not dot(d,v)])
                    ds=sum(dot(d,v)<<i for i,v in enumerate(dual))
                    adapted.update(ds^alpha^(t>>n) for t in choices if (t&fullmask)==w)
    assert direct==adapted,(trial,direct,adapted)
print("200 random nonregular-part decompositions, every two-bit target verified")
