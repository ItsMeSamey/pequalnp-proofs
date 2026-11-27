from itertools import combinations,product
from random import Random
from one_defect_coordinate_2sat import layout,search,solve_flats,search_with_closure


def span(B):
    S={0}
    for x in B:
        S.update([v^x for v in S])
    return S


if __name__=='__main__':
    rng=Random(413)
    cases=0
    for d in range(1,5):
        V=range(1,1<<d)
        bases=[set(B) for B in combinations(V,d) if len(span(B))==1<<d]
        Ps=sorted({tuple(sorted((x,y,x^y))) for x,y in combinations(V,2)})
        for _ in range(220):
            P=rng.sample(Ps,rng.randrange(min(len(Ps),6)+1))
            F=set(rng.sample(list(V),rng.randrange(min(len(V),3)+1)))
            ok=any(F<=B and all(len(B.intersection(Q))==2 for Q in P) for B in bases)
            assert (layout(F,P) is not None)==ok
            flats=[[(x,rng.randrange(2))] for x in F]+[[(x,rng.randrange(2)) for x in Q[:2]] for Q in P]
            status,w=solve_flats(d,flats)
            good={z for z in range(1<<d) if all(any((z&v).bit_count()%2!=b for v,b in f) for f in flats)}
            assert (status!='UNKNOWN')==ok and (not ok or (status=='YES')==bool(good))
            assert w is None or w in good
            transform=list(rng.choice(bases))
            offset=rng.randrange(1<<d)
            def recode(v):
                out=0
                for i,x in enumerate(transform):
                    if v>>i&1:
                        out^=x
                return out
            recoded=[[(recode(v),b^((v&offset).bit_count()%2)) for v,b in f] for f in flats]
            assert solve_flats(d,recoded)[0]==status
            cases+=1
    tally={}
    for rows in product(range(8),repeat=3):
        for b in range(8):
            good={z for z in range(8) if (b&z).bit_count()%2 and
                  all(not(z>>i&1 and (z&r).bit_count()%2) for i,r in enumerate(rows))}
            status,w=search(rows,b)
            assert status=='UNKNOWN' or ((status=='YES')==bool(good))
            assert w is None or w in good
            for j in range(3):
                if b>>j&1:
                    assert search(rows,b,j)[0]==status
            s,w=search_with_closure(rows,b)
            assert s=='UNKNOWN' or (s=='YES')==bool(good)
            assert w is None or w in good
            tally[status]=tally.get(status,0)+1
    print(cases,'basis, dense affine invariance, and flat tests;',tally)
