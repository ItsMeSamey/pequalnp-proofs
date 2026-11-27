from itertools import combinations
from random import Random
from quadratic_centroid import independent
from syndrome_integer_prefix import parity
from slope_group_algebra import Pencil


def good(n,D,t):
    rows=[sum(c<<j for j,c in enumerate(row))^(t&(1<<i)) for i,row in enumerate(D)]
    return len(independent(rows))==n


def check():
    rng=Random(1317)
    cases=0
    for n in range(6):
        for _ in range(16):
            H=[rng.randrange(1<<n) for _ in range(rng.randrange(4))]
            H+=H[:1]
            tab=[[[rng.randrange(2) for j in range(n)] for i in range(n)] for z in range(1<<len(H))]
            def word(t): return sum(((v&t).bit_count()%2)<<i for i,v in enumerate(H))
            fixed=rng.randrange(1<<n)
            vals=rng.randrange(1<<n)&fixed
            pins=[(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(3))]
            expect=sum(good(n,tab[word(t)],t) for t in range(1<<n) if t&fixed==vals
                       and all((v&t).bit_count()%2==b for v,b in pins))%2
            assert parity(n,H,tab.__getitem__,fixed=fixed,values=vals,pins=pins)==expect
            cases+=1
            P=Pencil(n,{ij:(rng.randrange(2),rng.randrange(1<<n)) for ij in
                        ((i,j) for i in range(n) for j in range(n) if i!=j)})
            def D(s):
                cols=P.frozen_columns(s)
                return [[cols[j]>>i&1 for j in range(n)] for i in range(n)]
            h=rng.randrange(n+1)
            x=rng.randrange(1<<h)
            assert parity(n,P.forms,D,fixed=(1<<h)-1,values=x)==P.parity(h,x)
    for n in range(2,8):
        edges=list(combinations(range(n),2))
        w=[rng.randrange(-n,n+1) for _ in range(n)]
        for _ in range(15):
            forms={e:([p for p in edges if sum(w[i] for i in p)<sum(w[i] for i in e)
                       and rng.randrange(2)],rng.randrange(1<<(n+1))) for e in edges}
            def D(t):
                rows=[[0]*n for j in range(n)]
                for (i,j),(terms,l) in forms.items():
                    z=((t|(1<<n))&l).bit_count()+sum((t>>a)&(t>>b)&1 for a,b in terms)
                    rows[i][j]=rows[j][i]=z%2
                return rows
            assert sum(good(n,D(t),t) for t in range(1<<n))%2
    print(cases,"nonlinear syndrome/pin cases and 96 Berkowitz comparisons, 90 weighted-degree oddness controls passed")


if __name__=="__main__":
    check()
