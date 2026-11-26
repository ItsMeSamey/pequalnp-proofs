"""Directly compare the bounded star search with enumeration on multigraphs."""
from random import Random
from solver import marker
from itertools import product
rng=Random(239137)
def run():
    for trial in range(300):
        n=rng.randrange(2,7)
        h=rng.randrange(1,min(3,n))
        m=rng.randrange(1,9)
        t=rng.randrange(0,3)
        edges=[(rng.randrange(n),rng.randrange(n)) for _ in range(m)]
        a,b=([rng.randrange(1<<t) for _ in edges] for _ in range(2))
        boundary=[(1<<u)^(1<<v) for u,v in edges]
        stars=sum(1<<i for i,(u,v) in enumerate(edges) if min(u,v)<h)
        sigma=rng.randrange(1<<m)&stars
        T=marker(boundary,rng.randrange(1<<m))
        d=T.bit_count()
        weights=[0]*n
        for (u,v),value in zip(edges,b):
            weights[u]^=value; weights[v]^=value
        J=[mask for mask in range(1<<m) if marker(boundary,mask)==T]
        cuts=[sum((((S>>u)^(S>>v))&1)<<i for i,(u,v) in enumerate(edges)) for S in range(1<<n)]
        want={marker(a,j)^marker(b,D^sigma) for j in J for D in cuts if not j&(D^sigma)}
        got=set()
        for F in {x&stars for x in range(1<<m)}:
            if F.bit_count()>h*(d+2*t):
                continue
            Tnew=T^marker(boundary,F)
            if Tnew&((1<<h)-1):
                continue
            residual=[j for j in range(1<<m) if not j&stars and marker(boundary,j)==Tnew]
            for S,D in enumerate(cuts):
                if F&(D^sigma):
                    continue
                for j in residual:
                    if not j&D:
                        got.add(marker(a,j^F)^marker(b,sigma)^marker(weights,S))
        assert want==got,(trial,want,got)
    print("300 complete signed-star score tables agree")
if __name__=='__main__':
    run()
