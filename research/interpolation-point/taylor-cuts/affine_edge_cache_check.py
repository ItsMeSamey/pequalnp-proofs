from fractions import Fraction
from random import Random
from affine_edge_cache import AffineEdgeCache


def direct(terms,x):
    return sum(w for w,flat in terms if all((a&x).bit_count()%2==b for a,b in flat))


def check(n,terms):
    cache=AffineEdgeCache(n,terms)
    values=[direct(terms,x) for x in range(1<<n)]
    assert values==[cache.value(x) for x in range(1<<n)]
    lo,hi=cache.extrema()
    assert lo==(min(values),values.index(min(values)))
    assert hi==(max(values),values.index(max(values)))
    return cache


def main():
    # Under x0 the residual parity flips: negative scale is necessary.
    neg=check(3,[(5,[(7,1)]),(-2,[])])
    assert neg.root[0].edges[1][1]<0
    # Distinct offsets for every fixed prefix, but only one nonconstant cache node per depth.
    n=8
    affine=check(n,[(1<<i,[(1<<i,1)]) for i in range(n)])
    assert [len(l) for l in affine.layers]==[1]*n+[0]
    rng=Random(19117)
    for n in range(5):
        for _ in range(12):
            terms=[(Fraction(rng.randrange(-4,5),rng.randrange(1,4)),
                    [(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(4))])
                   for _ in range(rng.randrange(7))]
            check(n,terms)
    print("62 fixtures; negative-scale extrema; 8 nonconstant representatives for 256 distinct values")


if __name__=='__main__':
    main()
