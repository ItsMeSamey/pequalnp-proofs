"""Pointwise profiles, multiplicity, and complements against direct assignments."""
from itertools import combinations, product
from random import Random
from affine_selector_projection import build_projection, parity


def sat(flats,x):
    return all(not all(parity(x&m)==t for m,t in flat) for flat in flats)


def check(n,flats,forms):
    p=build_projection(n,flats,forms)
    if p is None:
        return False
    original={x for x in range(1<<n) if sat(flats,x)}
    lifted=[]
    union=set()
    for z in range(1<<p.core_n):
        for a in p.arms:
            x=p.lift(a,z)
            assert a.word==sum((parity(m&x)^t)<<i for i,(m,t) in enumerate(forms))
            active=all(parity(z&m)==v for m,v in a.equations)
            if active:
                union.add(z)
            assert (sat(p.core_flats,z) and active)==(x in original)
            if sat(p.core_flats,z) and active:
                lifted.append(x)
    assert len(lifted)==len(set(lifted)) and set(lifted)==original
    if all(len(a.equations)<=1 for a in p.arms):
        f=p.one_equation_union()
        assert union=={z for z in range(1<<p.core_n) if f is None or sat((f,),z)}
    return True


def complement_exists(n, flats, forms):
    """Independent search over images of standard basis vectors for small n."""
    def span(vectors):
        acc={0}
        for v in vectors:
            acc |= {x^v for x in acc}
        return acc
    S=span(m for m,_ in forms)
    planes=[span(m for m,_ in f) for f in flats if any(not sat((f,),x) for x in range(1<<n))]
    # For a retraction pi, both disjoint and line intersections are tested by pi(P) ⊆ P∩S.
    for imgs in product(S,repeat=n):
        def proj(v):
            t=0
            for i,a in enumerate(imgs):
                if v>>i&1:t^=a
            return t
        if all(proj(v)==v for v in S) and all(all(proj(v) in P for v in P) for P in planes):
            return True
    return False


if __name__=='__main__':
    rng=Random(162)
    ok=0
    for _ in range(2000):
        n=rng.randrange(7)
        form=lambda:(rng.randrange(1<<n),rng.randrange(2))
        forms=[form() for _ in range(rng.randrange(5))]
        flats=[((m,a^1),(k,b^1)) for (m,a),(k,b) in combinations(forms,2)]
        flats.extend(tuple(form() for _ in range(rng.randrange(1,3))) for _ in range(rng.randrange(6)))
        ok+=check(n,flats,forms)
    for _ in range(250):
        n=rng.randrange(1,5)
        forms=[(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(3))]
        flats=[((m,a^1),(k,b^1)) for (m,a),(k,b) in combinations(forms,2)]
        flats.extend(tuple((rng.randrange(1<<n),rng.randrange(2)) for j in range(rng.randrange(1,3))) for i in range(rng.randrange(7)))
        assert (build_projection(n,flats,forms) is not None)==complement_exists(n,flats,forms)
    assert build_projection(2,[],[(1,0),(2,0)]) is None
    # One selector and two disjoint unary normals force contradictory projections.
    assert build_projection(2,[((2,0),),((3,0),)],[(1,0)]) is None
    # Two overlapping projected cells represent distinct selector assignments.
    assert check(4,[((1,1),(2,1)),((1,1),(4,0)),((2,1),(4,0))],[(1,0),(2,0)])
    print(f'{ok} accepted random projections checked pointwise; {2000-ok} certificates rejected; 250 exhaustive projection existence checks and explicit fixtures passed')
