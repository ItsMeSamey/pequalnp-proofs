"""Brute oracle for all triples of subspaces of GF(2)^3 and sparse source controls."""
from itertools import combinations
from read_two_ring_nonzero import compile_nonzero
from ring_image_beta_chart import _nest_order, _nested_sat, solve_sparse, solve_source_sparse
from ring_image_common_basis import common_basis


def linear_set(vectors):
    values = {0}
    for v in vectors:
        values.update([x ^ v for x in values])
    return frozenset(values)


def controls():
    bases = [s for s in combinations(range(1,8),3) if len(linear_set(s)) == 8]
    spaces = sorted({linear_set(s) for b in bases for k in range(4) for s in combinations(b,k)},
                    key=lambda s:(len(s),sorted(s)))
    assert len(spaces) == 16
    for triple in combinations(spaces,3):
        possible = any(all(linear_set(set(b) & s) == s for s in triple) for b in bases)
        result = common_basis(3,triple)
        assert (result is not None) == possible, triple
        if result:
            axes, sig = result
            assert all(linear_set(a for a,t in zip(axes,sig) if t >> i & 1) == s
                       for i,s in enumerate(triple))
    rows = [(1,2,3,4),(-1,-2,3,4),(-1,2)]
    for n, formula, status in [(4,rows,"nonzero"),(0,[()],"zero"),(0,[],"nonzero"),
                              (4,[(-4,),(1,2,3,4)],"nonzero"),
                              (3,[(1,2),(2,3),(3,1)],"unknown")]:
        result = solve_source_sparse(n,formula)
        assert result["status"] == status, result
        physical = compile_nonzero(n,formula)
        fields = [physical[key] for key in ("n","clauses","point","k")]
        assert solve_sparse(*fields) == result
        if status == "nonzero":
            ids = set(result["true_ids"])
            assert all(any((abs(l) in ids) == (l>0) for l in row) for row in formula)
    assert solve_source_sparse(10**1000, [(1,2,10**1000)])["status"] == "nonzero"
    assert solve_sparse(*fields[:-1],-1) == dict(status="off_image")
    # Direct Davis-Putnam zero and model restoration (closure may pre-empt these).
    all_patterns = [frozenset(a if w >> (a-1) & 1 else -a for a in (1,2,3)) for w in range(8)]
    order = _nest_order(all_patterns)
    assert _nested_sat(all_patterns,order) is None
    for drop in range(8):
        kept = all_patterns[:drop] + all_patterns[drop+1:]
        model = _nested_sat(kept,order)
        assert all(any((abs(l) in model) == (l>0) for l in row) for row in kept)


if __name__ == "__main__":
    controls()
    print("560 arbitrary-rank chart oracle triples and sparse physical beta-chart controls passed.")
