"""Direct monomial and extracted-edge checks, including deterministic cancellations."""
from itertools import product,combinations
from random import Random
from ternary_labelled_matching import search,_evaluate,_field


def main():
    rng=Random(117)
    total=0
    for n in (0,2,4,6):
        f,roots=_field(n)
        for trial in range(5):
            b=trial%3
            edges=[(i,j,tuple(rng.randrange(3) for _ in range(b))) for i,j in combinations(range(n),2)
                   if rng.randrange(4)]
            if edges:
                edges.append(edges[0])
            weights=[rng.randrange(f.size) for _ in edges]
            sets=[s for s in combinations(range(len(edges)),n//2)
                  if sorted(v for k in s for v in edges[k][:2])==list(range(n))]
            for t in product(range(3),repeat=b):
                good=[s for s in sets if all(sum(edges[k][2][i] for k in s)%3==y for i,y in enumerate(t))]
                val=0
                for s in good:
                    m=1
                    for k in s:
                        m=f.mul(m,weights[k])
                    val^=m
                assert _evaluate(range(n),edges,t,weights,f,roots)==val
                stream=iter(weights)
                st,w=search(n,edges,t,randbelow_fn=lambda q:next(stream))
                assert (st=="SAT")==bool(val)
                assert tuple(sorted(w)) in good if w is not None else st=="UNKNOWN"
                total+=1
    edges=[(0,1,(1,)),(0,1,(1,))]
    hits=0
    for weights in product(range(4),repeat=2):
        stream=iter(weights)
        st,w=search(2,edges,(1,),randbelow_fn=lambda q:next(stream))
        hits+=st=="SAT"
    assert hits==12
    assert search(2,edges,(2,),randbelow_fn=lambda q:1)==("UNKNOWN",None)
    assert search(2,edges,(1,),randbelow_fn=lambda q:1)==("UNKNOWN",None)
    stream=iter((1,1,0,2))
    assert search(2,edges,(1,),rounds=2,randbelow_fn=lambda q:next(stream))==("SAT",(1,))
    print(total,"filtered Pfaffians and witness restrictions matched monomial sums; GF4 uniform census 12/16")


if __name__=="__main__":
    main()
