"""Sparse binary identifiers and dense physical compatibility."""
from read_two_ring_nonzero import compile_nonzero
import ring_image_affine_hull_sparse as hull
import ring_image_coordinate_sparse as chart


def controls():
    big = 10**1000
    arity = big**2
    for module in (hull,chart):
        for rows, expected in [
            ([(big,)], (big,)),
            ([(1,), (big,), (-arity,)], (1,big)),
            ([], ()),
        ]:
            result = module.solve_source_sparse(arity,rows)
            assert result == dict(status="nonzero",true_ids=expected)
            chosen = set(result["true_ids"])
            assert all(any((abs(lit) in chosen) == (lit > 0) for lit in row) for row in rows)
        assert module.solve_source_sparse(arity,[(big,),(-big,)])["status"] == "zero"
    r = compile_nonzero(3, [(1,), (-3,)])
    fields = tuple(r[k] for k in ("n","clauses","point","k"))
    assert hull.solve(*fields) == dict(status="nonzero", assignment=(1,0,0))
    for module in (hull,chart):
        assert module.solve_sparse(*fields) == dict(status="nonzero",true_ids=(1,))
        assert module.solve_sparse(*fields[:-1],-1) == dict(status="off_image")


if __name__ == "__main__":
    controls()
    print("Sparse binary names and physical witness compatibility passed.")
