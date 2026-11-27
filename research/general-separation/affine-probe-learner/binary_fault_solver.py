"""Interval SAT search with global restarts on certified binary exclusions.

Input JSON is {"n": arity, "F": [NAND pairs, output]}. Input 0 is the MSB.
Set PYTHONINTMAXSTRDIGITS=0 before starting Python for large decimal witnesses.

A learned clause excludes a cube certified false on the ORIGINAL NAND DAG.
All original witnesses survive. Each phase uses a fresh learner for F(R(x)),
where R fixes the current 2-CNF's models and otherwise returns a chosen model.
Every pending search node and history is discarded on refinement. R(j) obeyed
the old clauses and violates the new one, so refinements are always fresh.
There are U=1+2n+4*binom(n,2) possible clauses. Each of at most U+1 phases
visits O((B+2)*2**k) nodes, since each edge charges one mistake, and at most k
unresolved binary forks lie on any phase path. B is the maximum phase budget.
For the bundled threshold learner B=n and work per node is polynomial in n
and the explicit source size. The frozen interval solver is unchanged.
"""
import json
import sys

from binary_fault_retraction import Gamma, compile_retraction, exclusion_cube
from primitive_forecast_extractor import _natural, _source
from primitive_rewrite_chain import endpoint, evaluate, public_cap
from threshold_interval_solver import forecast_factory


def _phase(n, original, gamma, retracted, learner_factory, bound, stats):
    source = retracted.gates, retracted.output
    cap = public_cap(n, len(source[0]))
    budget = n if bound is None else (bound(n, cap) if callable(bound) else bound)
    _natural(budget, "mistake bound")
    predict = learner_factory(n, source)
    pending = [(0, (1 << n) - 1, (), 0)]
    while pending:
        lower, upper, history, depth = pending.pop()
        stats["nodes"] += 1
        stats["k"] = max(stats["k"], depth)
        if len(history) > budget:
            continue

        def ask(index):
            query = endpoint(n, *source, index)
            if len(query[0]) > cap:
                raise ValueError("prefix exceeds public cap")
            bit = predict(n, cap, history, query)
            if type(bit) not in (int, bool) or bit not in (0, 1):
                raise ValueError("learner returned a non-bit forecast")
            stats["forecasts"] += 1
            stats["replay_rounds"] += len(history)
            return query, int(bit)

        left, right = lower - 1, upper
        left_query, bit = ask(left)
        if bit:
            stats["endpoint_errors"] += 1
            pending.append((lower, upper, history + ((left_query, 0),), depth))
            continue
        right_query, bit = ask(right)
        if not bit:
            stats["endpoint_errors"] += 1
            pending.append((lower, upper, history + ((right_query, 1),), depth))
            continue
        while right - left > 1:
            mid = (left + right) // 2
            query, bit = ask(mid)
            if bit:
                right, right_query = mid, query
            else:
                left, left_query = mid, query

        stats["crossings"] += 1
        point = retracted.lift(right)
        if not gamma.accepts(point):
            raise ValueError("retracted point violates the active clauses")
        original_bit = evaluate(n, *original, point)
        if evaluate(n, *source, right) != original_bit:
            raise ValueError("compiled retraction disagrees with original evaluation")
        if original_bit:
            return "witness", point
        stats["false_crossings"] += 1
        cube = exclusion_cube(n, *original, point)
        if cube is not None:
            return "refine", (point, cube)

        if lower < right < upper:
            depth += 1
            stats["binary_forks"] += 1
            stats["k"] = max(stats["k"], depth)
        if right < upper:
            pending.append((right + 1, upper, history + ((right_query, 0),), depth))
        if lower < right:
            pending.append((lower, right - 1, history + ((left_query, 1),), depth))
    return "exhausted", None


def solve(n, F, learner_factory=forecast_factory, bound=None):
    """Optional custom deterministic learners must satisfy their stated bound.

    bound may be an integer or a function of n and the current public cap.
    Using the built-in learner and its default bound gives unconditional SAT.
    """
    _natural(n, "n")
    if learner_factory is not forecast_factory and bound is None:
        raise ValueError("a custom predictor requires an explicit justified mistake bound")
    original = _source(n, F)
    gamma = Gamma(n)
    stats = dict(nodes=0, forecasts=0, replay_rounds=0, endpoint_errors=0,
                 k=0, binary_forks=0, fresh_clauses=0, phases=0,
                 crossings=0, false_crossings=0)

    def done(status, reason, **extra):
        return dict(status=status, reason=reason, clauses=gamma.clauses, **stats, **extra)

    while True:
        anchor = 0 if gamma.accepts(0) else gamma.model()
        if anchor is None:
            return done("unsat", "2sat")
        retracted = compile_retraction(n, *original, gamma, anchor=anchor)
        stats["phases"] += 1
        event, value = _phase(n, original, gamma, retracted, learner_factory, bound, stats)
        if event == "witness":
            return done("witness", "original_evaluation", assignment=value)
        if event == "exhausted":
            return done("unsat", "interval_exhaustion")
        point, cube = value
        if not gamma.add_cube(cube) or gamma.accepts(point):
            raise ValueError("binary exclusion did not remove its certified model")
        stats["fresh_clauses"] += 1


if __name__ == "__main__":
    instance = json.load(sys.stdin)
    print(json.dumps(solve(instance["n"], instance["F"]), separators=(",", ":")))
