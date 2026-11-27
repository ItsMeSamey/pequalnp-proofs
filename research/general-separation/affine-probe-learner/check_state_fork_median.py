"""Independent finite controls for the production prefix learner and DFS."""
from unittest.mock import patch

import state_dependent_interval_repair as repair
from primitive_rewrite_chain import endpoint, evaluate, public_cap
from threshold_interval_solver import UnsupportedQuery, forecast_factory, solve


def sources(n):
    """Canonical all-ones singleton and a AND (NOT a), distinct from zero."""
    gates = []
    root = 0
    for i in range(1, n):
        wire = n + len(gates)
        gates.extend(((root, i), (wire, wire)))
        root = wire + 1
    positive = (tuple(gates), root)
    negative = (((0, 0), (0, n), (n + 1, n + 1)), n + 2)
    return tuple(endpoint(n, *f, (1 << n) - 1) for f in (positive, negative))


def preorder(lo, hi):
    if lo > hi:
        return []
    mid = (lo + hi) // 2
    return [mid] + preorder(lo, mid - 1) + preorder(mid + 1, hi)


def rejected(thunk):
    try:
        thunk()
    except UnsupportedQuery:
        return
    raise AssertionError("foreign circuit accepted")


def check(n):
    last = (1 << n) - 1
    positive, negative = sources(n)
    assert negative != ((), -1) and positive != negative
    for source, other in ((positive, negative), (negative, positive)):
        cap = public_cap(n, len(source[0]))
        predict = forecast_factory(n, source)
        rows = {endpoint(n, *source, j): j for j in range(-1, last + 1)}
        assert len(rows) == last + 2
        assert all(evaluate(n, *source, u) == (source == positive and u == last)
                   for u in range(last + 1))
        for row, cut in rows.items():
            assert all(evaluate(n, *row, u) ==
                       (evaluate(n, *source, u) and u <= cut)
                       for u in range(last + 1))

        # The second foreign row has the correct outer AND and true cutoff
        # operand. The production parser must still validate the whole DAG.
        for foreign in (((), -2), endpoint(n, *other, last // 2)):
            rejected(lambda: predict(n, cap, (), foreign))
        pool = [(u, b) for u in range(last + 1) for b in (0, 1)
                if u or b == 0]
        visits = []
        feasible_depths = []

        def virtual(pair, cut):
            u, b = pair
            return int(b and u <= cut)

        def inspect(width, budget, history, query):
            candidates = pool
            for k, (past, label) in enumerate(history):
                assert predict(width, budget, history[:k], past) != label
                candidates = [v for v in candidates if virtual(v, rows[past]) == label]
            if source == positive and all(evaluate(n, *q, last) == b
                                          for q, b in history):
                feasible_depths.append(len(history))
                assert len(history) <= n and (last, 1) in candidates
            actual = predict(width, budget, history, query)
            votes = sum(virtual(v, rows[query]) for v in candidates)
            assert actual == int(2 * votes > len(candidates))
            return actual

        def watch(width, gates, output, x):
            assert (gates, output) == source
            visits.append(x)
            return evaluate(width, gates, output, x)

        with patch.object(repair, "evaluate", watch):
            result = repair.solve(n, source, cap, n, inspect)
        assert solve(n, source) == dict(**result, bound=n, cap=cap)
        assert visits == preorder(1, last)
        assert result["ambiguity_depth"] == n - 1
        if source == positive:
            assert result["status"] == "witness" and result["assignment"] == last
            assert max(feasible_depths) == n
        else:
            assert result["status"] == "unsat"

        # No virtual pair can have positive label for the zero sentinel.
        impossible = ((((), -1), 1),)
        assert predict(n, cap, impossible, source) == 0
        rejected(lambda: predict(n, cap, impossible, ((), -2)))
        rejected(lambda: predict(n, cap, ((((), -2), 0),), source))


def dimension_zero():
    for source in (((), -1), ((), -2)):
        cap = public_cap(0, 0)
        predict = forecast_factory(0, source)
        assert predict(0, cap, (), ((), -1)) == 0
        assert predict(0, cap, (), source) == evaluate(0, *source, 0)
        result = repair.solve(0, source, cap, 0, predict)
        assert result["status"] == ("witness" if source[1] == -2 else "unsat")
        assert result.get("assignment") == (0 if source[1] == -2 else None)


if __name__ == "__main__":
    dimension_zero()
    for dimension in range(1, 6):
        check(dimension)
    print("The production learner matches virtual counts and the median traversal.")
