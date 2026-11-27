"""Replay the matching adapter on graphs and on signed one-hot CNF+XOR."""
from itertools import combinations, product
from random import Random

from check_onehot_colour_folds import encode
from onehot_ternary_target import decide
from ternary_frame import color


def check_source():
    edges = [(u, v) for u in range(3) for v in range(3, 6)]
    assert color(6, edges, cap=0)[0] == "UNKNOWN"
    status, coloring, stats = color(6, edges, cap=0, four_row_high=1)
    assert status == "SAT" and stats["four_row"]["status"] == "SAT"
    assert stats["residual_rank"] == 4 and all(coloring[u] != coloring[v] for u, v in edges)
    assert color(6, edges, cap=0, four_row_high=0)[0] == "UNKNOWN"
    assert color(6, edges, cap=81, four_row_high=0)[0] == "SAT"
    strict_source = None
    for seed in range(64):
        clauses, equations = encode(6, edges, Random(seed))
        status, witness, stats = decide(18, clauses, equations, state_cap=0, four_row_high=1)
        if stats.get("four_row", {}).get("status") == "SAT":
            assert status == "SAT" and decide(18, clauses, equations, state_cap=0)[0] == "UNKNOWN"
            assert all(any(bool(witness >> (abs(lit)-1) & 1) == (lit > 0) for lit in row) for row in clauses)
            assert all((witness & mask).bit_count() % 2 == rhs for mask, rhs in equations)
            strict_source = seed
            break
    assert strict_source is not None
    rng = Random(4247)
    for _ in range(80):
        edges = [edge for edge in combinations(range(6), 2) if rng.randrange(2)]
        good = any(all(c[u] != c[v] for u, v in edges) for c in product(range(3), repeat=6))
        status, coloring, _ = color(6, edges, cap=3**10, four_row_high=1)
        assert (status, coloring is not None) == (("SAT", True) if good else ("UNSAT", False))
    print("80 brute graph controls, 4 strict/fallback graph calls, strict signed source seed", strict_source)


if __name__ == "__main__":
    check_source()
