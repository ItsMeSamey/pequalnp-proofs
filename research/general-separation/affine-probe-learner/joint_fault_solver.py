"""Exact SAT search with binary and affine exclusions in original coordinates.

Input JSON is {"n": arity, "F": [NAND pairs, output]}. Input 0 is the MSB.
The default exact threshold learner has mistake bound n. For large decimal
assignments start Python with PYTHONINTMAXSTRDIGITS=0.

Every binary clause excludes a Kleene-certified original zero cube. Every
affine equation is recognized at a conjunct of the original NAND output.
Original solutions satisfy both banks. Each phase decides their joint
feasibility, compiles the map fixing all joint models and sending every
other input to the chosen joint model, and starts a fresh interval search.

The first violated recognized equation is learned at a false lifted point;
otherwise a certified binary exclusion is attempted before ordinary branching.
Such a point satisfies all historical equations: a newly violated one raises
their coefficient rank or makes the system inconsistent. Thus at most n+1
affine updates and 1+2*n+4*binom(n,2) binary updates are possible. Let w be
the largest min(p,q) at a mixed anchor call and k the largest ambiguity
depth in an interval search. Anchor work is 2**w times a polynomial per
restart; search work is 2**k times a polynomial per phase for the bundled
learner. These costs add, because anchors are found only at phase boundaries.
"""
import json
import sys

from binary_fault_retraction import Gamma, exclusion_cube
from joint_fault_retraction import affine_conjuncts, compile_joint_retraction
from mixed_binary_anchor import solve as find_anchor
from primitive_forecast_extractor import _natural, _source
from primitive_rewrite_chain import endpoint, evaluate, public_cap
from threshold_interval_solver import forecast_factory


def _satisfies(row, point):
    mask, rhs = row
    return (mask & point).bit_count() % 2 == rhs


def _phase(n, original, candidates, retracted, learner_factory, bound, stats):
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
        if not retracted.accepts(point):
            raise ValueError("retracted point violates the active clauses")
        original_bit = evaluate(n, *original, point)
        if evaluate(n, *source, right) != original_bit:
            raise ValueError("compiled retraction disagrees with original evaluation")
        if original_bit:
            return "witness", point
        stats["false_crossings"] += 1
        for row in candidates:
            if not _satisfies(row, point):
                return "row", (point, row)
        cube = exclusion_cube(n, *original, point)
        if cube is not None:
            return "clause", (point, cube)

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
    """Return a checked original witness or an exhaustive UNSAT result.

    An alternative deterministic learner must satisfy the supplied mistake
    bound (an integer or a function of arity and the current public cap).
    """
    _natural(n, "n")
    if learner_factory is not forecast_factory and bound is None:
        raise ValueError("a custom predictor requires an explicit justified mistake bound")
    original = _source(n, F)
    candidates = affine_conjuncts(n, *original)
    gamma = Gamma(n)
    rows = ()
    stats = dict(nodes=0, forecasts=0, replay_rounds=0, endpoint_errors=0,
                 k=0, binary_forks=0, fresh_clauses=0, fresh_rows=0, phases=0,
                 crossings=0, false_crossings=0, anchor_calls=0,
                 anchor_fibers=0, anchor_width=0)

    def done(status, reason, **extra):
        return dict(status=status, reason=reason, rows=rows, clauses=gamma.clauses,
                    **stats, **extra)

    while True:
        search = find_anchor(n, gamma.clauses, rows)
        stats["anchor_calls"] += 1
        stats["anchor_fibers"] += search.fibers
        stats["anchor_width"] = max(stats["anchor_width"], min(search.p, search.q))
        if search.witness is None:
            return done("unsat", "mixed_inconsistent")
        retracted = compile_joint_retraction(n, *original, gamma, rows, search.witness)
        stats["phases"] += 1
        event, value = _phase(n, original, candidates, retracted,
                              learner_factory, bound, stats)
        if event == "witness":
            return done("witness", "original_evaluation", assignment=value)
        if event == "exhausted":
            return done("unsat", "interval_exhaustion")
        point, certificate = value
        if event == "row":
            if certificate in rows or _satisfies(certificate, point):
                raise ValueError("affine exclusion failed to remove its certified model")
            rows += (certificate,)
            stats["fresh_rows"] += 1
        elif event == "clause":
            if not gamma.add_cube(certificate) or gamma.accepts(point):
                raise ValueError("binary exclusion failed to remove its certified model")
            stats["fresh_clauses"] += 1
        else:
            raise ValueError("unknown phase event")


if __name__ == "__main__":
    instance = json.load(sys.stdin)
    print(json.dumps(solve(instance["n"], instance["F"]), separators=(",", ":")))
