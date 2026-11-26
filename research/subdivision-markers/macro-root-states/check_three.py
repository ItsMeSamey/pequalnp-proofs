"""Exhaustive small controls for the oracle reduction. The test oracle is exponential."""
from collections import Counter
from random import Random
from macro import small_port, spectrum
from solve import canonical, functional, image
from check import brute


def brute_triple(ordinary, terminals):
    goal = image(terminals,7)
    for m in range(1<<len(ordinary)):
        if image(ordinary,m) != goal:
            continue
        support = tuple(v for i,v in enumerate(ordinary) if m>>i & 1) + tuple(terminals)
        if len(canonical(support)) == len(support)-1:
            return m
    return None


def trial():
    rng=Random(194902)
    counts=Counter()
    for _ in range(65):
        local=tuple(rng.randrange(16) for _ in range(rng.randrange(4,9)))
        mat=canonical(local)
        if len(mat)<3:
            continue
        port=tuple(rng.sample(mat,3))
        rec=[]
        def counted(ordinary,terminals):
            result=brute_triple(ordinary,terminals)
            rec.append(result is not None)
            return result
        table=small_port(list(enumerate(local)),port,counted)
        i=0
        while i<len(rec):
            if rec[i]:
                counts["primal"]+=1
                i+=1
            else:
                counts["dual" if rec[i+1] else "absent"]+=1
                i+=2
        targets={image(port,j) for j in range(8)}
        orig={f:set() for f in range(8)}
        for mask in range(1<<len(local)):
            u=image(local,mask)
            if u not in targets:
                continue
            selected=tuple(v for i,v in enumerate(local) if mask>>i&1)
            for f in range(8):
                if functional(port+selected,f) is not None:
                    orig[f].add(u)
        for f in range(8):
            assert orig[f] == set(table[f])
            for u,m in table[f].items():
                support=tuple(v for i,v in enumerate(local) if m>>i&1)
                assert image(local,m)==u and functional(port+support,f) is not None
        counts["local"]+=1
    for _ in range(80):
        D=tuple(rng.randrange(16) for _ in range(8))
        L=tuple(rng.randrange(8) for _ in D)
        M=tuple(rng.randrange(8) for _ in D)
        found,_=spectrum(D,L,M,3,[(0,1,2),(3,4,5),(6,7)],((0,1),2),brute_triple)
        scores,cycles,cuts=brute(D,L,M)
        assert set(found)==scores
        for q,(c,d) in found.items():
            assert c in cycles and d in cuts and not c&d and image(L,c)^image(M,d)==q
        counts["outer"]+=1
    return counts


if __name__=="__main__":
    print(trial())
