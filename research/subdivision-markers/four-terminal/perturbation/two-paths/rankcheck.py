"""Check dual-symmetric triple trick and local block gluing for L-shaped moments."""
from itertools import combinations,product
from random import Random
from check import trees

def rank(cols):
    p={}
    for x in cols:
        while x:
            j=x.bit_length()-1
            if j not in p:
                p[j]=x;break
            x^=p[j]
    return len(p)

def triple(cols,f,p,q):
    # New three ports sum to f (the one required dependency), while the
    # two extra pure-gain directions in the old coordinates must be avoided.
    ports=[p,q,p^q^f]; m=len(cols)
    for mask in range(1<<m):
        basis=[z for i,z in enumerate(cols) if mask>>i&1]+ports
        value=0
        for x in basis:value^=x
        if value==0 and rank(basis)==len(basis)-1:return True
    return False

def raw(n,edges,d1,d2):
    hit=set()
    for order,parent,_ in trees(n,edges):
        g={0:0};h={0:0}
        for v in order[1:]:
            u,j=parent[v];g[v]=g[u]^edges[j][2];h[v]=h[u]^edges[j][3]
        score=lambda z,d:sum(z[v] for v in range(n) if d>>v&1)%2
        hit.add(score(g,d1)+2*score(h,d1)+4*score(g,d2))
    return hit

if __name__=='__main__':
    rng=Random(8831)
    for _ in range(300):
        n=rng.randint(1,5)
        E=[(rng.randrange(i),i,rng.randrange(2),rng.randrange(2)) for i in range(1,n)]
        E.extend((rng.randrange(n),rng.randrange(n),rng.randrange(2),rng.randrange(2)) for j in range(rng.randrange(4)))
        d=rng.randrange(1<<n);d^=d.bit_count()%2
        obs={x&3 for x in raw(n,E,d,d)}
        K=[(1<<u)^(1<<v)^(g<<n)^(h<<(n+1)) for u,v,g,h in E]
        got={i for i in range(4) if triple(K,d^(i<<n),1<<n,1<<(n+1))}
        assert got==obs
    for _ in range(300):
        # Blocks glued at n1-1; each block may have higher rank, too.
        n1,n2=rng.randint(2,4),rng.randint(2,4);n=n1+n2-1
        def block(k):
            return [(i,(i+1)%k,rng.randrange(2),rng.randrange(2)) for i in range(k)]
        A,B=block(n1),block(n2)
        graph=A+[(a+n1-1,b+n1-1,g,h) for a,b,g,h in B]
        ds=[rng.randrange(1<<n) for _ in range(2)];ds=[d^(d.bit_count()%2) for d in ds]
        def project(d):
            l=d&((1<<n1)-1);r=d>>(n1-1)
            return l^((l.bit_count()%2)<<(n1-1)),r^(r.bit_count()%2)
        d1,d2=map(project,ds)
        lhs=raw(n,graph,*ds)
        rhs={a^b for a in raw(n1,A,d1[0],d2[0]) for b in raw(n2,B,d1[1],d2[1])}
        assert lhs==rhs
    print('1200 one-demand/two-gain binary triple tests; 300 full block table sums')
