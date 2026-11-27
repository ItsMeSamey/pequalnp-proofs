from itertools import product, combinations
from random import Random
from torus_overlap import decide, _monomial
from punctured_witness import BinaryField


def check():
    rng = Random(8174)
    cases = 0
    for modulus in (7,19):
        f = BinaryField(modulus)
        for n in (0,1,2):
            points = list(product(range(1,f.size),repeat=n))
            for _ in range(10):
                def row():
                    return tuple(rng.randrange(-4,5) for _ in range(n))
                A = [row() for _ in range(rng.randrange(3))]
                c = [_monomial(f,rng.choice(points),a) for a in A]
                polys = [[(rng.randrange(1,f.size),row()) for _ in range(rng.randrange(1,4))]
                         for _ in range(rng.randrange(1,4))]
                def value(poly,x):
                    out = 0
                    for k,e in poly:
                        out ^= f.mul(k,_monomial(f,x,e))
                    return out
                truth = any(all(_monomial(f,x,a)==v for a,v in zip(A,c)) and
                            all(value(poly,x) for poly in polys) for x in points)
                got = decide(f,n,A,c,polys,max_overlap=300)
                if got.status == "UNKNOWN":
                    assert got.overlap > 300
                    got = decide(f,n,A,c,polys,max_overlap=got.overlap)
                assert got.status in ("SAT", "UNSAT") and (got.status == "SAT") == truth
                cases += 1

    f = BinaryField(7)
    def edges(n, pairs):
        return [[(1,tuple(int(k==u) for k in range(n))),
                 (1,tuple(int(k==v) for k in range(n)))] for u,v in pairs]
    tree = [(0,1),(1,2),(2,3)]
    assert decide(f,4,[],[],edges(4,tree)).overlap == 1
    cycle = edges(4,tree+[(3,0)])
    assert decide(f,4,[],[],cycle).status == "SAT"
    assert decide(f,4,[],[],cycle,max_overlap=2).status == "UNKNOWN"
    assert decide(f,4,[],[],edges(4,combinations(range(4),2))).status == "UNSAT"
    f = BinaryField(19)
    # One dependency with overlap 5 in order 15, on a nonidentity coset.
    a = _monomial(f,[2],[5])
    allowed = [(1,(1,)), (1,(0,))]
    r = decide(f,1,[(5,)],[a],[allowed,allowed])
    assert (r.status,r.overlap,r.peak_states) == ("SAT",5,5)
    print(cases,"brute-force checks and composite coset/forest/cycle/clique controls passed")


if __name__ == "__main__":
    check()
