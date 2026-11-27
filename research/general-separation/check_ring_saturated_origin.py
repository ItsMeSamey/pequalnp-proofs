"""Translation excludes the default point from a saturated set."""
from read_two_ring_nonzero import compile_nonzero
from ring_image_origin_horn import solve_source_sparse as fixed
from ring_image_saturated_origin import solve_source_sparse, solve_sparse


def controls():
    shift = 15
    rows = [tuple(-j if (t ^ shift) >> (j-1) & 1 else j for j in range(1,5))
            for t in (0,1,2,7,8)]
    rows.append((-3,-4))
    assert fixed(4,rows)["status"] == "unknown"
    compiled = compile_nonzero(4,rows)
    values = tuple(compiled[k] for k in ("n","clauses","point","k"))
    for result in (solve_source_sparse(4,rows), solve_sparse(*values)):
        assert result["status"] == "nonzero"
        true = set(result["true_ids"])
        assert all(any((abs(l) in true) == (l>0) for l in row) for row in rows)
    masks = (0,1,2,4,8,15)
    rows = [tuple(-j if t >> (j-1) & 1 else j for j in range(1,5)) for t in masks]
    assert solve_source_sparse(4,rows) == dict(status="unknown",reason="too_many_forbidden_patterns")


if __name__ == "__main__":
    controls()
    print("Full active saturated origin search and cardinality controls passed.")
