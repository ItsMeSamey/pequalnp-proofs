from fractions import Fraction
from random import Random
from affine_syndrome_trellis import minimum_table, nae_minimum_table, dot


def brute(n, score, boundary, pins):
    out={}
    for x in range(1<<n):
        if any(dot(x,a)!=b for a,b in pins):continue
        key=sum((dot(x,a)^b)<<i for i,(a,b) in enumerate(boundary))
        val=score(x)
        if key not in out or out[key]>val:out[key]=val
    return out


if __name__=='__main__':
    rng=Random(99017); cases=checked=0
    for n in range(7):
        def form():return rng.randrange(1<<n),rng.randrange(2)
        for _ in range(65):
            pins=[form() for _ in range(rng.randrange(4))]
            boundary=[form() for _ in range(rng.randrange(6))]
            terms=[(Fraction(rng.randrange(-4,5),rng.randrange(1,4)),*form()) for _ in range(8)]
            _,a,b=terms[0]
            terms.extend([(7,a,b),(7,a,b^1)])
            def score(x):
                return sum(w*(-1)**(dot(x,a)^b) for w,a,b in terms)
            triples=[[form() for _ in range(3)] for _ in range(rng.randrange(7))]
            def violated(x):
                return sum(len({dot(x,a)^b for a,b in triple})==1 for triple in triples)
            for func,(table,sizes) in [(score,minimum_table(n,terms,boundary,pins)),
                                        (violated,nae_minimum_table(n,triples,boundary,pins))]:
                expected=brute(n,func,boundary,pins)
                assert {b:v for b,(v,x) in table.items()}==expected
                for beta,(v,x) in table.items():
                    assert func(x)==v and all(dot(x,a)==b for a,b in pins)
                    assert beta==sum((dot(x,a)^b)<<i for i,(a,b) in enumerate(boundary))
                cases+=1;checked+=len(table)
    # Dense check space with a narrow particular column order: independent triangles.
    n=14
    terms=[(j%3+1, a, j%2) for j,a in enumerate(sum(([1<<(2*i),2<<(2*i),3<<(2*i)] for i in range(n//2)),[]))]
    table,sizes=minimum_table(n,terms)
    assert max(sizes)==2 and len(sizes)==22
    print(cases,'all-boundary tables;',checked,'optimal witnesses; disjoint triple codes peak at',max(sizes))
