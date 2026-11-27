from itertools import combinations,product
from random import Random
from labelled_flip_difference import solve
from twin_flip_catalogue import Catalogue
from check_labelled_flip_difference import profile


def audit(n,edges):
    full=profile(n,edges,2)
    for t in product(range(3),repeat=2):
        s,w,_=solve(n,edges,t,twin_primitive=True)
        assert s==('SAT' if t in full else 'UNSAT')
        if w is not None:
            assert frozenset(w) in full[t]


if __name__=='__main__':
    rng=Random(1248)
    # False twins 0 and 6 within the first C6 class, and 1 and 7 within the second.
    ty=[0,1,2,3,4,5,0,1]
    es=[(u,v,(rng.randrange(3),rng.randrange(3))) for u,v in combinations(range(8),2)
        if (ty[u]-ty[v])%6 in (1,5)]
    cat=Catalogue(8,es)
    assert cat.stats['long_patterns']==1
    full=(1<<8)-1
    def long(mask):
        return [u for u,l,r in cat.flips(mask) if len(l)>=3]
    assert long(full)==[63] and long(full-3)==[252]
    audit(8,es)
    # Central twin type occurs twice at opposite parity in a bowtie.
    bow=[(u,v,(0,int({u,v}=={4,5}))) for u,v in combinations(range(6),2)
         if (u<2<=v or (u,v) in ((2,3),(4,5)))]
    assert Catalogue(6,bow).stats['repeated_type']>=1
    audit(6,bow)
    # Clique collapses to one true-twin class. Four-switches and parallel flips suffice.
    clique=[(u,v,(rng.randrange(3),rng.randrange(3))) for u,v in combinations(range(6),2)
            for j in range(1+int((u+v)%4==0))]
    assert Catalogue(6,clique).stats['types']==1
    audit(6,clique)
    assert solve(6,bow,(2,2),twin_primitive=True,cycle_cap=0)[0]=='UNKNOWN'
    print('27 original-ID target comparisons plus residual re-selection, repeated-type bowtie, clique and cap controls passed')
