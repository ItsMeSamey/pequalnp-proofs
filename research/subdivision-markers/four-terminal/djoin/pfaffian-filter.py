"""Independent direct test of the FPT specialization over GF(8)."""
from itertools import combinations
from random import Random


def mul(x,y):
    s=0
    while y:
        if y&1:
            s^=x
        y>>=1
        x<<=1
        if x&8:
            x^=11
    return s


def prod(xs):
    x=1
    for y in xs:
        x=mul(x,y)
    return x


def add(xs):
    x=0
    for y in xs:
        x^=y
    return x


def inv(x):
    return next(y for y in range(1,8) if mul(x,y)==1)


def eliminate(M,f):
    M=[r[:] for r in M]
    scale=1
    for j in range(f):
        row=next((i for i in range(j,len(M)) if M[i][j]),None)
        if row is None:
            return 0,[]
        M[j],M[row]=M[row],M[j]
        p=M[j][j]
        scale=mul(scale,p)
        M[j]=[mul(x,inv(p)) for x in M[j]]
        for i in range(len(M)):
            if i!=j and M[i][j]:
                v=M[i][j]
                M[i]=[x^mul(v,y) for x,y in zip(M[i],M[j])]
    return scale,[row[f:] for row in M[f:]]


def det(M):
    return eliminate(M,len(M))[0]


def filt(M,n,required):
    h=len(M)
    order=list(required)+[j for j in range(n) if j not in required]
    if len(required)>h:
        return 0
    scale,B=eliminate([[row[j] for j in order] for row in M],len(required))
    if not scale:
        return 0
    q=n-len(required)
    if len(B)%2:
        B=[row+[0] for row in B]+[[0]*q+[1]]
        q+=1
    # Multiply by the all-ones off-diagonal matrix via row sums.
    S=[add(row) for row in B]
    skew=[[add(mul(row[p],S[j]^B[j][p]) for p in range(q)) for j in range(len(B))] for row in B]
    assert all(skew[i][i]==0 for i in range(len(B)))
    value=det(skew)
    root=next(x for x in range(8) if mul(x,x)==value)
    return mul(scale,root)


def cb(n,edges,R,D,y,w,weights):
    k=len(R)
    I=[[(a==v)^(b==v) for a,b in edges] for v in range(n)]
    E0=[j for j in range(len(edges)) if j not in R]
    L=[[add(weights[e] for e in E0 if I[i][e] and I[j][e]) for j in range(n)] for i in range(n)]
    delta=D
    for j,e in enumerate(R):
        if (y>>j)&1:
            a,b=edges[e]
            delta^=(1<<a)^(1<<b)
    out=0
    for S in combinations(sorted({v for e in R for v in edges[e]}-{w}),k):
        if not det([[I[v][e] for e in R] for v in S]):
            continue
        A=set(S)|{w}
        req=[i for i in range(n) if not (((delta>>i)&1)^(i in A))]
        out^=filt([L[i] for i in range(n) if i not in A],n,req)
    return out


def direct(n,edges,R,D,y,weights):
    out=0
    other=[j for j in range(len(edges)) if j not in R]
    for F in combinations(other,n-1-len(R)):
        parent=list(range(n))
        def rep(x):
            while x!=parent[x]:
                x=parent[x]
            return x
        for e in F+R:
            a,b=map(rep,edges[e])
            if a==b:
                break
            parent[a]=b
        else:
            delta=D
            for j,e in enumerate(R):
                if y>>j&1:
                    u,v=edges[e]
                    delta^=(1<<u)^(1<<v)
            # Test D' inside the ordinary forest by explicit subset boundary.
            for m in range(1<<len(F)):
                boundary=0
                for j,e in enumerate(F):
                    if m>>j&1:
                        u,v=edges[e]
                        boundary^=(1<<u)^(1<<v)
                if boundary==delta:
                    out^=prod(weights[e] for e in F)
                    break
    return out


if __name__=='__main__':
    rng=Random(342498)
    for _ in range(500):
        n=rng.randrange(0,9)
        h=rng.randrange(n+1)
        M=[[rng.randrange(8) for j in range(n)] for i in range(h)]
        req=set(rng.sample(range(n),rng.randrange(n+1)))
        oracle=add(det([[r[j] for j in t] for r in M]) for t in combinations(range(n),h) if req<=set(t))
        assert oracle==filt(M,n,req)
    checked=0
    for _ in range(150):
        n=rng.randrange(2,8)
        pairs=list(combinations(range(n),2))
        rng.shuffle(pairs)
        edges=pairs[:rng.randint(1,min(9,len(pairs)))]
        if rng.randrange(4)==0:
            edges.append(rng.choice(edges))
        k=rng.randint(0,min(n-1,len(edges),4))
        R=tuple(rng.sample(range(len(edges)),k))
        D=rng.randrange(1<<n)
        weights=[rng.randrange(8) for e in edges]
        w=rng.randrange(n)
        for y in range(1<<k):
            assert cb(n,edges,R,D,y,w,weights)==direct(n,edges,R,D,y,weights)
            checked+=1
    print('500 mandatory-minor filters;',checked,'weighted tree-pattern checks')
