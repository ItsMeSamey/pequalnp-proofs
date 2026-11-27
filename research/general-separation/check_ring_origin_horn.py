"""A strict comparable-signature shear and a bad fixed origin."""
from read_two_ring_nonzero import compile_nonzero
from ring_image_origin_horn import solve_source_sparse, solve_sparse


def controls():
    rows = [tuple(-j if t >> (j-1) & 1 else j for j in range(1,5)) for t in (0,1,2,7)]
    rows.append((3,4))
    compiled = compile_nonzero(4,rows)
    fields = tuple(compiled[k] for k in ("n","clauses","point","k"))
    for r in (solve_source_sparse(4,rows), solve_sparse(*fields,origin_true_ids=())):
        assert r["status"] == "nonzero"
        selected = set(r["true_ids"])
        assert all(any((abs(l) in selected) == (l>0) for l in row) for row in rows)
    assert solve_source_sparse(1,[(1,)],origin_true_ids=()) == dict(
        status="unknown",reason="origin_outside_hull")
    assert solve_source_sparse(1,[(1,)],origin_true_ids=(1,))["true_ids"] == (1,)
    # The three nonzero difference vectors sum to zero, so no dual basis
    # makes all three distinct functionals weight one. Keep allowed hull full.
    forbidden = (1,2,3)
    rows = [tuple(-j if w >> (j-1) & 1 else j for j in range(1,4)) for w in forbidden]
    assert solve_source_sparse(3,rows,origin_true_ids=()) == dict(
        status="unknown",reason="no_origin_tuple_chart")


if __name__ == "__main__":
    controls()
    print("Fixed-origin tuple Horn shear and incompatible kernels passed.")
