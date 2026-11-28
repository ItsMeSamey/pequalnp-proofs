"""Physical decision on two independent source blocks that require different reductions."""
from itertools import product

from read_two_ring_nonzero import compile_nonzero
from ring_image_saturated_rank_pivots import decide, solve_source_sparse


def fields(n, rows):
    image = compile_nonzero(n, rows)
    return tuple(image[name] for name in ("n", "clauses", "point", "k"))


def satisfies(bits, row):
    return any(bits[abs(literal) - 1] == (literal > 0) for literal in row)


def main():
    chain = [(-1, -2, -3), (-1, -2, 3), (-1, -4, 2)]
    remote = [(6, 7, 8), (9, 10, 11)]
    binary = [(-6, 5), (-7, -5), (-9, 5), (-10, -5)]
    rows = chain + remote + binary
    models = {bits for bits in product(range(2), repeat=11)
              if all(satisfies(bits, row) for row in rows)}
    assert len(models) == 180
    for value in (0, 1):
        assert sum(bits[4] == value for bits in models) == 90
    args = fields(11, rows)
    answer = decide(*args)
    assert answer["status"] == "nonzero" and answer["route"] == "saturated_pivots"
    bits = tuple(answer["assignment"])
    assert bits in models
    assert tuple(i for i, bit in enumerate(bits, 1) if bit) == answer["true_ids"]
    assert tuple(answer["rank_history"]) == (5, 3, 2)
    assert {frozenset((-1, -2)), frozenset((-1, -4))} <= set(map(frozenset, answer["derived"]))
    assert answer["pivots"] == (5,) and all(5 not in row for row in remote)
    metrics = answer["metrics"]
    assert metrics["rank"] == metrics["basis_rows"] == 2 and metrics["common_rank"] == 0
    assert metrics["ternary_rows"] == len(chain + remote) and metrics["gains"] == [2]
    assert metrics["branch_calls"] == 1
    for key in ("projection_calls", "rank_work", "discovery_work", "candidate_records"):
        assert metrics[key] > 0
    for cap, measured in (("discovery_cap", "discovery_work"), ("rank_cap", "rank_work"),
                          ("branch_cap", "branch_calls")):
        limited = solve_source_sparse(11, rows, **{cap: metrics[measured] - 1})
        assert limited["status"] == "unknown" and limited["reason"] == cap.replace("_", " ")
        assert limited["metrics"][measured] < metrics[measured]
    assert decide(*args, branch_cap=0)["status"] == "unknown"
    impossible = [(1, 2, 3), (1, 2, -3), (-1,), (-2,)]
    assert not any(all(satisfies(bits, row) for row in impossible)
                   for bits in product(range(2), repeat=3))
    assert decide(*fields(3, impossible))["status"] == "zero"
    print("Physical SAT and UNSAT, 180 original models, remote pivot and three budgets passed.")


if __name__ == "__main__":
    main()
