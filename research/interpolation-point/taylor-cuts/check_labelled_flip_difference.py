from itertools import combinations,product
from random import Random

from labelled_flip_difference import solve,find_nonzero


def profile(n,edges,b):
    def walk(V):
        if not V:
            yield ()
        else:
            u=min(V)
            for i,(a,c,g) in enumerate(edges):
                if u in (a,c) and a in V and c in V:
                    for rest in walk(V-{a,c}):
                        yield (i,)+rest
    out={}
    for ids in walk(set(range(n))):
        g=tuple(sum(edges[i][2][j] for i in ids)%3 for j in range(b))
        out.setdefault(g,[]).append(frozenset(ids))
    return out

if __name__=='__main__':
    rng=Random(816)
    calls=0
    for k in range(40):
        n=2*(1+k%3)
        b=1+k%2
        order=(tuple(range(n//2)),tuple(range(n//2,n))) if k%3==1 else tuple(range(n))
        pairs=[(u,v) for u,v in combinations(range(n),2) if k%3!=1 or u<n//2<=v]
        es=[(u,v,tuple(rng.randrange(3) for j in range(b))) for u,v in pairs for _ in range(1+rng.randrange(2))]
        full=profile(n,es,b)
        for g in product(range(3),repeat=b):
            kw={'odd_chord':True} if k%3==2 else {'strong_order':order}
            status,w,_=solve(n,es,g,**kw)
            assert status==('SAT' if g in full else 'UNSAT')
            if w is not None:
                assert frozenset(w) in full[g]
            calls+=1
        P=[rng.randrange(3) for g in product(range(3),repeat=b)]
        expected=[g for i,g in enumerate(product(range(3),repeat=b)) if P[i] and g in full]
        status,w,_=find_nonzero(n,es,b,P,strong_order=order)
        assert status==('SAT' if expected else 'UNSAT')
        calls+=1
    es=[(i,(i+1)%6,(int(i==0),)) for i in range(6)]
    for kw in ({},{'odd_chord':True},{'strong_order':tuple(range(6))}):
        assert solve(6,es,(2,),**kw)[0]=='UNKNOWN'
    assert solve(6,es,(2,),odd_chord=True,state_cap=0)[0]=='UNKNOWN'
    print(calls,'complete-host/ordered-bipartite multigraph target and arbitrary function checks plus uncertified C6 controls passed')
