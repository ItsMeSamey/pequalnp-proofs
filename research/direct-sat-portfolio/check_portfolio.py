"""Check dispatch, rewrites and untouched witnesses against exhaustive original models."""
import json
from collections import Counter
from random import Random
from unittest.mock import patch

import portfolio

rng = Random(714091)
decisions = Counter()
for i in range(240):
    n = rng.randrange(6)
    gates = tuple((rng.getrandbits(n+j+1), rng.getrandbits(n+j+1))
                  for j in range(rng.randrange(7)))
    last = rng.getrandbits(n+len(gates)+1)
    outputs = [portfolio.evaluate(n, gates, last, x) for x in range(1 << n)]
    reduced, new_last, _, _ = portfolio.simplify(n, gates, last, 12)
    assert outputs == [portfolio.evaluate(n, reduced, new_last, x) for x in range(1 << n)]
    for routes in (None, [], [portfolio.ROUTES[i % 4]]):
        result = portfolio.solve(n, gates, last, routes=routes, budget=500,
                                 rewrite_budget=i % 5)
        assert (result['status'] == 'sat') == any(outputs)
        if any(outputs):
            assert outputs[result['witness']] and result['verified']
        decisions[result['route']] += 1
for example in ((1, [(8, 2)], 2), (1, [], 4), (True, [], 1)):
    try:
        portfolio.solve(*example)
    except ValueError:
        pass
    else:
        raise AssertionError(example)
with patch('affine_quotient.solve', return_value=dict(status='sat', witness=0)):
    try:
        portfolio.solve(2, [(2, 4)], 8, routes=['affine_quotient'], rewrite_budget=0)
    except RuntimeError as error:
        assert 'original evaluation' in str(error)
    else:
        raise AssertionError('unsound witness accepted')
print(json.dumps(dict(complete_dispatches=sum(decisions.values()), decisions=decisions), sort_keys=True))
large = portfolio.solve(15000, (), 1 << 15000)
assert large['witness'] == 1 << 14999 and large['verified']
for action in (TimeoutError(), lambda *args, **kwargs: dict(status='unknown')):
    with patch('affine_quotient.solve', side_effect=action):
        again = portfolio.solve(2, [(2, 4)], 8, routes=['affine_quotient'], rewrite_budget=0)
        assert again['route'] == 'exhaustive' and again['witness'] == 3
