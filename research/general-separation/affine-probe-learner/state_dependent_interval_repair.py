"""Depth-first candidate-preserving repairs for a deterministic mistake-bounded oracle."""
from primitive_forecast_extractor import _natural, _source
from primitive_rewrite_chain import endpoint, evaluate


def solve(n, F, cap, bound, learner):
    """learner(n, cap, history, query) must replay the specified immutable history."""
    _natural(n, "n")
    _natural(cap, "cap")
    _natural(bound, "bound")
    gates, output = _source(n, F)
    pending = [(0, (1 << n) - 1, (), 0)]
    stats = dict(nodes=0, forecasts=0, replay_rounds=0,
                 endpoint_errors=0, binary_forks=0, ambiguity_depth=0)
    while pending:
        lower, upper, history, ambiguities = pending.pop()
        stats["nodes"] += 1
        stats["ambiguity_depth"] = max(stats["ambiguity_depth"], ambiguities)
        if len(history) > bound:
            continue

        def ask(index):
            query = endpoint(n, gates, output, index)
            if len(query[0]) > cap:
                raise ValueError("query exceeds public NAND cap")
            prediction = learner(n, cap, history, query)
            if type(prediction) not in (bool, int) or prediction not in (0, 1):
                raise ValueError("learner returned a non-bit forecast")
            stats["forecasts"] += 1
            stats["replay_rounds"] += len(history)
            return query, int(prediction)

        left, right = lower - 1, upper
        left_query, left_bit = ask(left)
        if left_bit:
            stats["endpoint_errors"] += 1
            pending.append((lower, upper, history + ((left_query, 0),), ambiguities))
            continue
        right_query, right_bit = ask(right)
        if not right_bit:
            stats["endpoint_errors"] += 1
            pending.append((lower, upper, history + ((right_query, 1),), ambiguities))
            continue
        while right - left > 1:
            middle = (left + right) // 2
            query, bit = ask(middle)
            if bit:
                right, right_query = middle, query
            else:
                left, left_query = middle, query
        if evaluate(n, gates, output, right):
            return dict(status="witness", assignment=right, **stats)
        two_children = lower < right < upper
        if two_children:
            stats["binary_forks"] += 1
        next_depth = ambiguities + int(two_children)
        if right < upper:
            pending.append((right + 1, upper, history + ((right_query, 0),), next_depth))
        if lower < right:
            pending.append((lower, right - 1, history + ((left_query, 1),), next_depth))
    return dict(status="unsat", **stats)
