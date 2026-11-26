"""Compare forced leaf strategies and verify Walsh normalization directly."""
from fractions import Fraction
from itertools import product
from random import Random
from affine_cell_energy import dot
from semantic_tree_solver import minimize, sparse_spectrum, SpectrumLimit


def score(terms,x):
    return sum(w for w,rows in terms if all(dot(x,a)==b for a,b in rows))


def compare(n,leaves,tree,eq=()):
    scores={x:sum(score(terms,x) for terms in leaves) for x in range(1<<n)
            if all(dot(x,a)==b for a,b in eq)}
    for strategy in ("edge","sparse-edge","trellis","auto"):
        answer=minimize(n,leaves,tree,eq,leaf_strategy=strategy,spectrum_cap=1<<n)
        if not scores:
            assert answer is None
        else:
            v,x=answer
            assert v==min(scores.values())==scores[x]


def main():
    rng=Random(1279)
    for n in range(4):
        for _ in range(5):
            leaves=[[(Fraction(rng.randrange(-4,5),3),
                      [(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(3))])
                     for _ in range(3)] for _ in range(3)]
            compare(n,leaves,(1,(2,0)),[(rng.randrange(1<<n),rng.randrange(2))])
            for terms in leaves:
                expected={a:Fraction(sum(score(terms,x)*(-1 if dot(a,x) else 1)
                                         for x in range(1<<n)),1<<n) for a in range(1<<n)}
                assert sparse_spectrum(n,terms,1<<n)=={a:w for a,w in expected.items() if w}
    terms=[(1,[(1,0),(2,0),(4,0)])]
    assert sparse_spectrum(3,terms,1) is None
    assert minimize(3,[terms],0,spectrum_cap=1)==minimize(3,[terms],0,leaf_strategy="edge")
    for strategy in ("sparse-edge","trellis"):
        try:
            minimize(3,[terms],0,leaf_strategy=strategy,spectrum_cap=1)
        except SpectrumLimit:
            pass
        else:
            raise AssertionError("forced sparse strategy ignored cap")
    # Dense linearly independent forms: J+I is invertible in even dimension.
    d=8
    masks=[((1<<d)-1)^(1<<i) for i in range(d)]
    dense=[(-1<<i,[(a,1)]) for i,a in enumerate(masks)]
    coeff=sparse_spectrum(d,dense,d+1)
    assert set(coeff)=={0,*masks}
    for strategy in ("auto","trellis","sparse-edge"):
        value,x=minimize(d,[dense],0,leaf_strategy=strategy)
        assert value==-(1<<d)+1 and all(dot(a,x) for a in masks)
    print("20 four-strategy fixtures, 60 full spectra, sparse-cap and 8 dense independent parities")


if __name__=='__main__':
    main()
