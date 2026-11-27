"""Original-word integration controls. Optional --full-mask exercises width 12."""
import argparse
import json
from pathlib import Path
import random
import subprocess
import sys

from check_binary_fault_solver import Source, raw
from limited_query_halving import capacity
from odd_masked_circuit import compile_source
from sampled_forecast_sat import minimum_points, solve


def check(n, F, *, limit=9):
    words = [x for x in range(1 << n) if raw(n, F, x)]
    result = solve(n, F, max_points=limit)
    assert result['status'] == ('witness' if words else 'unsat')
    if words:
        assert result['assignment'] in words
    assert result['sample_budget'] == minimum_points(n)
    return result


def arbitrary():
    rng = random.Random(7021)
    for n in range(5):
        m = minimum_points(n)
        assert capacity(m, n) >= 1 << n
        assert m == 1 or capacity(m-1, n) < 1 << n
        for _ in range(6):
            gates = []
            for i in range(7):
                gates.append(tuple(rng.randrange(-2, n+i) for _ in range(2)))
            check(n, (tuple(gates), n+len(gates)-1))
        for wire in range(-2, n):
            check(n, ((), wire))
    try:
        solve(4, ((), -1), max_points=8)
    except ValueError as exc:
        assert 'budget' in str(exc)
    else:
        raise AssertionError('insufficient budget did not refuse')


def mask_fixture(phi):
    # Actual r=0 masked-positive-threshold-support source: (not t & u & v & phi)
    # OR (t & u & v). Both branches have the planted high witness 111.
    c = Source(3)
    uv = c.both(1, 2)
    lower = c.both(c.both(c.inv(0), uv), -2 if phi else -1)
    upper = c.both(0, uv)
    out = c.nand(c.inv(lower), c.inv(upper))
    return compile_source(3, c.finish(out))


def tiny_masks(full_mask):
    for phi in (False, True):
        physical = mask_fixture(phi)
        # Substitute zero for all nine free mask bits and expose the three tail
        # inputs. This retains every raw NAND and its order on this restriction.
        wires = {-1: -1, -2: -2, **{i: -1 for i in range(9)},
                 **{9+i: i for i in range(3)}}
        c = Source(3)
        for i, (a, b) in enumerate(physical[0], 12):
            wires[i] = c.nand(wires[a], wires[b])
        out = wires[physical[1]]
        assert all(raw(3, c.finish(out), x) == raw(12, physical, x) for x in range(8))
        assert set(x for x in range(8) if raw(3, c.finish(out), x)) == ({3,7} if phi else {7})
        check(3, c.finish(out))
        clipped = c.finish(c.both(out, c.inv(0)))
        assert check(3, clipped)['status'] == ('witness' if phi else 'unsat')
        if full_mask:
            result = check(12, physical, limit=2049)
            assert raw(12, physical, result['assignment'])
        else:
            try:
                solve(12, physical, max_points=9)
            except ValueError as exc:
                assert 'budget' in str(exc)
            else:
                raise AssertionError('width-12 mask bypassed small-test guard')


def cli():
    script = Path(__file__).with_name('sampled_forecast_sat.py')
    command = [sys.executable, str(script), '--max-points', '1']
    data = json.dumps({'n': 1, 'F': [[], 0]})
    got = json.loads(subprocess.run(command, input=data, text=True, check=True,
                                    capture_output=True).stdout)
    assert got['status'] == 'witness' and got['assignment'] == got['sample_budget'] == 1


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--full-mask', action='store_true')
    args = parser.parse_args()
    arbitrary()
    tiny_masks(args.full_mask)
    cli()
    print('Sampled SAT gates, mask controls, budget guard, and CLI passed.')
