"""Independent GF(16) computations; masks label edges, vertices, and minors."""
from itertools import combinations
from random import Random


def mul(a,b):
    p=0
    while b:
        if b&1:
            p^=a
        a<<=1
        if a&16:
            a^=19
        b>>=1
    return p


def pfaffian(matrix):
    """Skew Gaussian elimination in characteristic two."""
    m=[row.copy() for row in matrix]
    out=1
    for i in range(0,len(m),2):
        j=next((v for v in range(i+1,len(m)) if m[i][v]),None)
        if j is None:
            return 0
        if j!=i+1:
            m[i+1],m[j]=m[j],m[i+1]
            for row in m:
                row[i+1],row[j]=row[j],row[i+1]
        pivot=m[i][i+1]
        out=mul(out,pivot)
        inv=next(v for v in range(1,16) if mul(v,pivot)==1)
        for a in range(i+2,len(m)):
            for b in range(a+1,len(m)):
                m[a][b]^=mul(inv,mul(m[i][a],m[i+1][b])^mul(m[i][b],m[i+1][a]))
                m[b][a]=m[a][b]
    return out


def det2(columns):
    piv={}
    for a in columns:
        while a and a.bit_length() in piv:
            a^=piv[a.bit_length()]
        if not a:
            return 0
        piv[a.bit_length()]=a
    return 1


def compressed(n,es,k,d,weights,w):
    if k>=n:
        return 0
    roots=[(1<<u)^(1<<v) for u,v in es[:k]]
    delta=d
    for e in roots:
        delta^=e
    endpoints=sorted({z for e in es[:k] for z in e}-{w})
    total=0
    for part in combinations(endpoints,k):
        a=sum(1<<i for i in part)
        if not det2([e&a for e in roots]):
            continue
        a|=1<<w
        s=delta^a
        top=[i for i in range(n) if not a>>i&1]
        h=len(top)
        size=h+n+((k+1)%2)
        matrix=[[0]*size for _ in range(size)]
        for (u,v),weight in zip(es[k:],weights):
            if u==v:
                continue
            for i,p in enumerate(top):
                if p in (u,v):
                    for q in (u,v):
                        matrix[i][h+q]^=weight
                        matrix[h+q][i]^=weight
        clique=[h+v for v in range(n) if s>>v&1]
        if (k+1)%2:
            clique.append(size-1)
        for i,j in combinations(clique,2):
            matrix[i][j]=matrix[j][i]=1
        total^=pfaffian(matrix)
    return total


def direct(n,es,k,d,weights):
    if k>=n:
        return 0,[]
    total=0
    accepted=[]
    for f in combinations(range(k,len(es)),n-1-k):
        adj=[[] for _ in range(n)]
        for i in (*range(k),*f):
            u,v=es[i]
            adj[u].append((v,i))
            adj[v].append((u,i))
        order=[0]
        par={0:(0,-1)}
        for v in order:
            for u,i in adj[v]:
                if u not in par:
                    par[u]=(v,i)
                    order.append(u)
        if len(order)!=n:
            continue
        chosen=set()
        demand=d
        for v in reversed(order[1:]):
            if demand>>v&1:
                u,i=par[v]
                chosen.add(i)
                demand^=(1<<u)|(1<<v)
        if demand or not set(range(k))<=chosen:
            continue
        weight=1
        for i in f:
            weight=mul(weight,weights[i-k])
        total^=weight
        accepted.append(f)
    return total,accepted


def recover(n,es,k,d,weights):
    """Given a nonzero evaluation, lift a spanning tree by deletion/contraction."""
    original=(n,es,d)
    ids=list(range(len(es)))
    saved=[]
    while len(es)>k:
        edges=es[:-1]
        value=compressed(n,edges,k,d,weights[:-1],0)
        if not value:
            a,b=sorted(es[-1])
            assert a!=b
            def project(v):
                return a if v==b else v-(v>b)
            edges=[(project(u),project(v)) for u,v in edges]
            new_d=0
            for v in range(n):
                if d>>v&1:
                    new_d ^= 1<<project(v)
            n-=1
            d=new_d
            saved.append(ids[-1])
        es,ids,weights=edges,ids[:-1],weights[:-1]
    assert n==k+1
    n,original_edges,d=original
    member=ids+saved
    val,trees=direct(n,[original_edges[i] for i in member],k,d,[1]*len(saved))
    assert val==1 and len(trees)==1
    return member


if __name__=='__main__':
    rng=Random(6451)
    cases=positive=0
    for _ in range(900):
        n=rng.randrange(1,10)
        es=list(combinations(range(n),2))
        rng.shuffle(es)
        es=es[:rng.randrange(min(14,len(es))+1)]
        if es and rng.randrange(3)==0:
            es.append(rng.choice(es))
        k=rng.randrange(min(n,len(es))+1)
        d=rng.randrange(1<<n)
        d^=d.bit_count()%2
        weights=[rng.randrange(16) for _ in es[k:]]
        z,trees=direct(n,es,k,d,weights)
        assert compressed(n,es,k,d,weights,rng.randrange(n))==z
        if z:
            recover(n,es,k,d,weights)
        positive+=bool(trees)
        cases+=1
    # All-odd demand and four disjoint prescribed edges: evaluate every
    # Boolean weight vector. Multilinearity certifies coefficientwise equality.
    n=8
    es=[(0,1),(2,3),(4,5),(6,7),(1,2),(3,4),(5,6),(0,3),(2,5),(3,6),(0,7)]
    for k in range(5):
        # Nonroots can include some of the first four pair edges.
        for mask in range(1<<(len(es)-k)):
            weights=[(mask>>j)&1 for j in range(len(es)-k)]
            z,_=direct(n,es,k,255,weights)
            assert compressed(n,es,k,255,weights,0)==z
    print(cases,"GF(16) weighted random tests,",positive,"positive instances;",
          sum(1<<(len(es)-k) for k in range(5)),"Boolean evaluations on all-odd eight-vertex example")
