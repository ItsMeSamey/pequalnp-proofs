from itertools import combinations,product
from random import Random
from horn_closure_xor import solve_horn_xor,principal_hull,horn_xor_hull,effective_xor_rank


def affine(points):
    if not points:
        return set()
    origin=next(iter(points))
    out={origin}
    for x in points:
        out|={z^(x^origin) for z in out}
    return out


def generated(origin,basis):
    out={origin}
    for d in basis:
        out|={x^d for x in out}
    return out


def check(n,clauses,rows):
    horn={x for x in range(1<<n) if all(any(bool(x>>(abs(l)-1)&1)==(l>0)
                                             for l in c) for c in clauses)}
    target={x for x in horn if all((x&a).bit_count()%2==b for a,b in rows)}
    w=solve_horn_xor(n,clauses,rows)
    assert (w in target) if target else (w is None)
    h=principal_hull(n,clauses)
    if horn:
        assert generated(h.origin,h.directions)==affine(horn)
        for i in range(n):
            vals={x>>i&1 for x in horn}
            assert bool(h.forced_zero>>i&1)==(vals=={0})
            assert bool(h.forced_one>>i&1)==(vals=={1})
            for j in range(n):
                if len(vals)==2:
                    assert any(c>>i&c>>j&1 for c in h.classes)==all(
                        (x>>i^x>>j)&1==0 for x in horn)
    else:
        assert h is None
    got=horn_xor_hull(n,clauses,rows)
    assert (got is None) if not target else (got[0] in target and generated(*got)==affine(target))


def main():
    # Genuine nonlinear rule, equivalent pair, forced one and forced zero.
    clauses=[(-1,-2,3),(-3,4),(-4,3),(5,),(-6,)]
    for bits in product(range(2),repeat=3):
        rows=list(zip((3,6,5),bits))
        check(6,clauses,rows)
    assert effective_xor_rank(6,clauses,[(4|8,0),(16,1),(1,1)])==1
    assert effective_xor_rank(6,clauses,[(4|8,1)]) is None
    check(2,[(1,),(-1,)],[])
    check(0,[()],[])
    check(0,[],[])
    rng=Random(3372)
    for n in range(1,6):
        for _ in range(50):
            clauses=[]
            for _ in range(rng.randrange(9)):
                body=rng.sample(range(1,n+1),rng.randrange(n+1))
                head=rng.randrange(n+1)
                clauses.append([-i for i in body]+([head] if head else []))
            rows=[(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(5))]
            check(n,clauses,rows)
    print("261 exact Horn/XOR witness, principal-class and constrained-hull fixtures")


if __name__=='__main__':
    main()
