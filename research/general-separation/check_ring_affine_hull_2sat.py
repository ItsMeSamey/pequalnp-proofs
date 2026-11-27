"""Small controls for hull closure, exact cylinder projection and physical recovery."""
from itertools import product
from read_two_ring_nonzero import compile_nonzero
from ring_image_affine_hull_2sat import Span, _binary_cover, solve, solve_source


def controls():
    cases = [
        (3, [(-1,), (1,2,3)], "nonzero"),
        (3, [(-1,), (1,2,3), (-2,), (-3,)], "zero"),
        (3, [(1,2,3),(1,2,-3),(-1,2,3)], "nonzero"),
        (3, [(1,2,3)], "unknown"),
        (4, [(1,),(-1,2),(-2,3),(-3,4),(-4,)], "zero"),
        (0, [], "nonzero"),
        (0, [()], "zero"),
    ]
    for n, rows, expected in cases:
        compiled = compile_nonzero(n, rows)
        fields = [compiled[k] for k in ("n","clauses","point","k")]
        r = solve(*fields)
        assert r == solve_source(n, rows) and r["status"] == expected, r
        models = [a for a in product((0,1), repeat=n)
                  if all(any(a[abs(l)-1] == (l>0) for l in row) for row in rows)]
        if expected == "nonzero":
            assert r["assignment"] in models
        if expected == "zero":
            assert not models
    fields[-1] = -1
    assert solve(*fields) == {"status":"off_image"}
    span = Span()
    span.append(3)  # local t = u0 xor u1, neither chart axis is itself local
    clauses = _binary_cover(span, {0}, [1,2])
    assert clauses is not None
    for word in range(4):
        excluded = any(all((a & word).bit_count() % 2 == b for a,b in tests)
                       for tests in clauses)
        assert excluded == (word.bit_count() % 2 == 0)


if __name__ == "__main__":
    controls()
    print("Affine hull and projected binary cylinder controls passed.")
