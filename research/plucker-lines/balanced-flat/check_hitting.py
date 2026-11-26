"""Universal affine-flat coverage, finite-field tests, and mixed witness checks."""
from itertools import combinations
from random import Random

from hitting import (affine_space, field_modulus, field_trace, hitting_points,
                     irreducible, multiply, poly_mod, solve, trace_points)
from solver import basis, bits, parity


def check_fields():
    for degree in range(1, 9):
        for candidate in range(1 << degree, 2 << degree):
            reducible = any(not poly_mod(candidate, factor)
                            for factor in range(2, 1 << (1+degree//2)))
            assert irreducible(candidate) != reducible
        modulus = field_modulus(degree)
        q = 1 << degree
        traces = [field_trace(a,modulus) for a in range(q)]
        assert set(traces) == {0,1}
        for base in range(1,q):
            assert {multiply(base,a,modulus) for a in range(q)} == set(range(q))


def check_flats():
    for r,h in [(0,0),(1,1),(3,2),(4,3),(5,2),(6,2)]:
        points = set(trace_points(r,h))
        for c in range(min(h,r)+1):
            for equations in combinations(range(1,1 << r), c):
                if len(basis(equations)) != c:
                    continue
                observed = {sum(parity(m & x) << i for i,m in enumerate(equations))
                            for x in points}
                assert len(observed) == 1 << c
    # Force the non-enumerative path; test every codimension-one flat.
    points = set(hitting_points(13,1))
    assert len(points) < 1 << 13 and 0 in points
    assert len(basis(points)) == 13
    assert list(hitting_points(5,0)) == [0]


def dual_valid(d, t, s, tests):
    return not parity(t & d) and (s is None or parity(s & d)) and all(
        parity(mask & d) == rhs for mask,rhs in tests)


def expected_label(d, target, root_label, moments):
    mixed = sum(parity(mask & d) << j for j,mask in enumerate(moments))
    return mixed ^ target ^ root_label


def verify(answer, rank, ordinary, t, s, tests, target, root_label, moments):
    d, indices = answer
    assert d < 1 << rank and indices < 1 << len(ordinary)
    assert dual_valid(d,t,s,tests)
    primal = label = 0
    for i in bits(indices):
        v,w = ordinary[i]
        assert not parity(d & v)
        primal ^= v
        label ^= w
    assert primal == t and label == expected_label(d,target,root_label,moments)


def exhaustive(rank, ordinary, t, s, tests, target, root_label, moments):
    for d in range(1 << rank):
        if not dual_valid(d,t,s,tests):
            continue
        image = {0}
        for v,w in ordinary:
            if not parity(v & d):
                image |= {x ^ (v | (w << rank)) for x in image}
        if t | (expected_label(d,target,root_label,moments) << rank) in image:
            return True
    return False


def check_structured():
    rng = Random(13886)
    for _ in range(350):
        rank = rng.randrange(6)
        labels = rng.randrange(4)
        lifted_rank = rank + labels
        h = rng.randrange(lifted_rank + 1)
        generators = []
        while len(generators) < lifted_rank-h:
            a = rng.randrange(1 << lifted_rank)
            if len(basis(generators + [a])) > len(generators):
                generators.append(a)
        # Actual strong blocking set on W: all basis vectors and pair sums.
        lifted = generators + [a ^ b for a,b in combinations(generators,2)]
        lifted += [rng.randrange(1 << lifted_rank) for _ in range(rng.randrange(6))]
        ordinary = [(a % (1 << rank), a >> rank) for a in lifted]
        t = rng.randrange(1 << rank)
        s = rng.choice([None, rng.randrange(1 << rank)])
        tests = [(rng.randrange(1 << rank),rng.randrange(2)) for _ in range(rng.randrange(4))]
        moments = [rng.randrange(1 << rank) for _ in range(labels)]
        target, root_label = [rng.randrange(1 << labels) for _ in range(2)]
        answer = solve(rank, labels, ordinary, h+min(h,labels), t, target,
                       root_label, moments, tests, s)
        assert (answer is not None) == exhaustive(rank, ordinary, t, s, tests,
                                                 target, root_label, moments)
        if answer is not None:
            verify(answer,rank,ordinary,t,s,tests,target,root_label,moments)
        equations = tests + [(t,0)] + ([] if s is None else [(s,1)])
        space = affine_space(rank,equations)
        generated = set()
        if space is not None:
            origin,directions = space
            generated = {origin}
            for v in directions:
                generated |= {x ^ v for x in generated}
        assert generated == {d for d in range(1 << rank) if dual_valid(d,t,s,tests)}

    # W is the whole 16-dimensional primal space with zero labels; h=1.
    # The only possible primal label is 0, while its mixed target is 1+d(e0).
    # This forces the solver past the first hitting point and through the trace path.
    rank = 16
    unit = [1 << j for j in range(rank)]
    ordinary = [(v,0) for v in unit + [a ^ b for a,b in combinations(unit,2)]]
    answer = solve(rank,1,ordinary,2,0,target=1,moments=[1])
    assert answer is not None
    verify(answer,rank,ordinary,0,None,[],1,0,[1])
    assert solve(13,0,[],1,1) is None


if __name__ == '__main__':
    check_fields()
    check_flats()
    check_structured()
    print('Binary fields through degree 8, universal small-flat coverage, and 350 structured cases passed.')
