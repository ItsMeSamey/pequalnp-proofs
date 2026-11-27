"""End-to-end global-row witnesses, caps and fallback on a subdivided K3,4."""
from random import Random

from check_onehot_colour_folds import encode
from onehot_ternary_target import decide
from ternary_frame import color
from ternary_global_rows import solve as global_solve
from ternary_matching_portfolio import search


def main():
    edges = [(u, v) for u in range(3) for v in range(3, 7) if (u, v) != (2, 6)]
    edges.extend([(2, 7), (6, 7)])
    assert color(8, edges, cap=0)[0] == "UNKNOWN"
    assert color(8, edges, cap=0, four_row_high=2)[0] == "UNKNOWN"
    for b, h, k in [(0, 2, 2), (1, 1, 2), (1, 2, 0)]:
        status, _, stats = color(8, edges, cap=0, global_b=b, global_h=h, owner_kappa=k)
        assert status == stats["global_matching"]["status"] == "UNKNOWN"
    caps = dict(global_b=1, global_h=2, owner_kappa=2)
    status, colors, stats = color(8, edges, cap=0, **caps)
    assert status == stats["global_matching"]["status"] == "SAT"
    assert all(colors[u] != colors[v] for u, v in edges)
    clauses, equations = encode(8, edges, Random(1))
    assert decide(24, clauses, equations, state_cap=0)[0] == "UNKNOWN"
    status, witness, stats = decide(24, clauses, equations, state_cap=0, **caps)
    assert status == stats["global_matching"]["status"] == "SAT"
    assert all(any(bool(witness >> (abs(lit)-1) & 1) == (lit>0) for lit in row) for row in clauses)
    assert all((witness & mask).bit_count() % 2 == rhs for mask, rhs in equations)
    assert color(8, edges, cap=81, global_b=0)[0] == "SAT"
    labelled = [(0,1,(1,)), (0,2,(1,)), (0,3,(2,)), (1,2,(1,)), (1,3,(2,)), (2,3,(0,))]
    for goal, cap, rounds, expected in [(0,1,0,"SAT"),(2,1,0,"UNSAT"),
                                        (0,0,0,"UNKNOWN"),(2,0,2,"UNKNOWN")]:
        calls = dict.fromkeys(("owner_calls","planar_calls","hull_calls","random_calls"),0)
        status, _ = search(4, labelled, (goal,), owner_kappa=0, planar_cap=cap,
                           rounds=rounds, randbelow_fn=Random(32).randrange, metrics=calls)
        assert status == expected and calls["planar_calls"] == cap
        assert calls["random_calls"] == bool(rounds)
    for first, expected in [("UNKNOWN","UNKNOWN"), ("UNSAT","UNSAT")]:
        answers = iter([first])
        def branch(n, edges, target):
            return next(answers, "UNSAT"), None
        result, _ = global_solve(4, [(1,1,1,1)]*3, b=0, h=4, branch_solver=branch)
        assert result == expected
    print("Strict graph/signed source, three cap misses and exact fallback passed")


if __name__ == "__main__":
    main()
