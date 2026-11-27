"""SAT by positive-threshold repair with the production sampled halving learner.

Input JSON on stdin: {"n": 3, "F": [[[0,1]],3]}. Input 0 is the MSB,
gate i has address n+i, and -1/-2 denote zero/one. Time is
2**n * poly(n+s+1) including history replays. --max-points optionally
bounds the sample budget per trial; refusal is a resource error, never UNSAT.
"""
import argparse
import json
import sys

from forecast_consistency_search import solve as forecast_solve
from limited_query_halving import learner_factory
from primitive_forecast_extractor import _natural, _source
from primitive_rewrite_chain import evaluate


def minimum_points(n):
    """Least positive budget giving the arity-wide exact-n mistake guarantee."""
    _natural(n, 'arity')
    return 1 if n < 2 else (1 << (n-1)) + 1


def solve(n, F, *, max_points=None):
    _natural(n, 'arity')
    F = _source(n, F)
    if max_points is not None:
        _natural(max_points, 'max_points')
        # Avoid constructing an oversized budget integer just to refuse it.
        if not max_points or (n >= 2 and n > (max_points-1).bit_length()):
            raise ValueError('minimum sample budget exceeds max_points')
    m = minimum_points(n)
    result = forecast_solve(n, F, learner_factory(m), mode='positive')
    if result['status'] == 'witness' and evaluate(n, *F, result['assignment']) != 1:
        raise AssertionError('sampled forecast witness rejected by original NAND circuit')
    return dict(result, sample_budget=m)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-points', type=int)
    args = parser.parse_args()
    data = json.load(sys.stdin)
    try:
        result = solve(data['n'], data['F'], max_points=args.max_points)
    except ValueError as exc:
        parser.error(str(exc))
    print(json.dumps(result, sort_keys=True))


if __name__ == '__main__':
    main()
