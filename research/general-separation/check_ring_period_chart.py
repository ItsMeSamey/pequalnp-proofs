"""Tiny exhaustive period/fiber and physical backend controls."""
from itertools import product
from read_two_ring_nonzero import compile_nonzero
from ring_image_period_chart import essential_normals, solve_source_sparse, solve_sparse


def controls():
    for table in range(256):
        words = {w for w in range(8) if table >> w & 1}
        normals = essential_normals(words,3)
        for delta in range(8):
            assert all((delta & v).bit_count() % 2 == 0 for v in normals) == (
                {w ^ delta for w in words} == words)
    words = {0,1,2,9,8,11}
    target = [tuple(-j if w >> (j-1) & 1 else j for j in range(1,5)) for w in words]
    for n,rows in [(4,target),(3,[(1,2),(2,3),(3,1)]),(1,[(1,),(-1,)])]:
        compiled = compile_nonzero(n,rows)
        fields = tuple(compiled[k] for k in ("n","clauses","point","k"))
        result = solve_sparse(*fields)
        assert result == solve_source_sparse(n,rows)
        def satisfies(s):
            return all(any((abs(l) in s) == (l>0) for l in row) for row in rows)
        exists = any(satisfies({i+1 for i,b in enumerate(bits) if b})
                     for bits in product((0,1),repeat=n))
        assert result["status"] == ("nonzero" if exists else "zero")
        if exists:
            assert satisfies(set(result["true_ids"]))
    assert solve_source_sparse(10**1000,[(10**1000,)])["true_ids"] == (10**1000,)


if __name__ == "__main__":
    controls()
    print("Essential periods, chart fibers, beta and Horn controls passed.")
