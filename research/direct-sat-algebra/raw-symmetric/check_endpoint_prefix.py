from itertools import combinations
from random import Random
from endpoint_prefix import parity,witness,_pfaffian,affine_chart
from quadratic_centroid import independent
from quadratic_target import apply_basis


def pf_brute(a):
    if not a: return 1
    ans=0
    for i in range(1,len(a)):
        ids=[j for j in range(1,len(a)) if j!=i]
        ans+=(-1)**(i+1)*a[0][i]*pf_brute([[a[j][k] for k in ids] for j in ids])
    return ans


def check():
    rng=Random(519)
    for n in range(0,9,2):
        for _ in range(10):
            a=[[0]*n for _ in range(n)]
            for i,j in combinations(range(n),2):
                a[i][j]=rng.randrange(-3,4)
                a[j][i]=-a[i][j]
            assert _pfaffian(a)==pf_brute(a)
    seen=0
    for n in range(6):
        for _ in range(12):
            H=[rng.randrange(1<<n) for k in range(rng.randrange(3))]
            H+=H[:1]
            d=rng.randrange(1<<n)
            tabs={(u,i,j):rng.randrange(16) for u in range(1<<len(H))
                  for i,j in combinations(range(n),2)}
            def edge(u,i,j,a,b):return tabs[u,i,j]>>(2*a+b)&1
            def matrix(t):
                u=sum(((v&t).bit_count()%2)<<j for j,v in enumerate(H))
                cols=[(t^d)&(1<<i) for i in range(n)]
                for i,j in combinations(range(n),2):
                    z=edge(u,i,j,t>>i&1,t>>j&1)
                    cols[i]^=z<<j
                    cols[j]^=z<<i
                return cols
            for _ in range(3):
                fixed=rng.randrange(1<<n)
                val=fixed&rng.randrange(1<<n)
                pins=[(rng.randrange(1<<n),rng.randrange(2)) for k in range(rng.randrange(3))]
                good=[t for t in range(1<<n) if t&fixed==val and
                      all((v&t).bit_count()%2==b for v,b in pins) and len(independent(matrix(t)))==n]
                assert parity(n,H,edge,offset=d,fixed=fixed,values=val,pins=pins)==len(good)%2
                seen+=1
            res=witness(n,H,edge,0,offset=d,center=lambda t:t)
            assert bool(res)==bool(parity(n,H,edge,offset=d))
            if res:
                t,y=res
                assert apply_basis(matrix(t),y)==t
    n=6
    common=(1<<n)-1
    def edge(u,i,j,x,y):
        if j==i+1:return x^u
        if i==0 and j==n-1:return y^u
        return 0
    assert len(independent(common^(1<<i) for i in range(n)))==n
    entries={tuple(sorted((i,(i+1)%n))):(0,common^(1<<i)) for i in range(n)}
    assert affine_chart(n,entries,max_rank=0) is None
    basis,oracle=affine_chart(n,entries,max_rank=1)
    assert len(basis)==1
    for t in range(1<<n):
        u=(t&basis[0]).bit_count()%2
        for i,j in combinations(range(n),2):
            assert oracle(u,i,j,t>>i&1,t>>j&1)==edge(t.bit_count()%2,i,j,t>>i&1,t>>j&1)
    assert parity(n,[common],edge)==1 and witness(n,[common],edge,17) is not None
    print(seen,"nonlinear pinned prefix comparisons, 50 exact integer Pfaffians, and full-rank/offdiag rank-one residual control passed")


if __name__=="__main__":
    check()
