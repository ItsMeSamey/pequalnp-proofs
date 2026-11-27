"""Eliminate guarded uses of a primary input by invertible Boolean shears.

If a NAND wire v is syntactically x_p XOR g(x_without_p), and the output
cannot reach p without traversing v, replace the uses of v by raw p and
remove dead gates. In the new coordinates p is the old v; all other input
bits are unchanged. This triangular substitution permutes the entire cube.
After all substitutions remove unused coordinates. Each compact solution
has exactly 2**(n-width) original lifts; lift exposes all of them.

Scan in topological order, resolving ties by least original input index.
A signed spine may alternate NAND(x,x) inversions and the four-NAND XOR
macro; either operand may supply the spine, the other must omit the pivot
syntactically. Each NAND gate in the XOR macro may commute its inputs.
Every iteration removes at least its selected gate. A straightforward
scan with one blocked reachability walk per candidate takes polynomial
bit time in n+s, including <=s iterations and the saved inverse circuits.
This is a sufficient recognition rule; expressions outside it remain usable.
"""
import argparse
from dataclasses import dataclass
import json
import sys

from primitive_forecast_extractor import _natural, _source
from primitive_rewrite_chain import evaluate
from sampled_forecast_sat import solve as sampled_solve


def _word(width, x):
    if type(x) is not int or x < 0 or x.bit_length() > width:
        raise ValueError("packed assignment out of range")


def _cone(n, gates, output, block=None):
    seen = set()
    stack = [output]
    while stack:
        wire = stack.pop()
        if wire == block or wire in seen:
            continue
        seen.add(wire)
        if wire >= n:
            stack.extend(gates[wire - n])
    return seen


def _clean(n, F, origin, gate=None, pivot=None):
    gates, out = F
    live = _cone(n, gates, out, gate)
    rebuilt, labels, renumber = [], [], {}

    def image(w):
        if w == gate:
            return pivot
        return w if w < n else renumber[w]

    for i, (a, b) in enumerate(gates):
        w = n + i
        if w in live:
            renumber[w] = n + len(rebuilt)
            rebuilt.append((image(a), image(b)))
            labels.append(origin[i])
    return (tuple(rebuilt), image(out)), tuple(labels)


def _xor(n, gates, a, b):
    if a < n or b < n:
        return None
    left, right = gates[a - n], gates[b - n]
    for li, shared in enumerate(left):
        if shared < n:
            continue
        for ri, partner in enumerate(right):
            if partner != shared:
                continue
            u, v = left[1-li], right[1-ri]
            if gates[shared - n] in ((u, v), (v, u)):
                return u, v
    return None


def _candidate(n, F):
    gates, out = F
    support = {-1: 0, -2: 0}
    signed = {-1: 0, -2: 0}
    for w in range(n):
        support[w] = signed[w] = 1 << w
    for w, (a, b) in enumerate(gates, n):
        support[w] = support[a] | support[b]
        if a == b:
            pivots = signed[a]
        else:
            pair = _xor(n, gates, a, b)
            if pair is None:
                pivots = 0
            else:
                u, v = pair
                pivots = (signed[u] & ~support[v]) | (signed[v] & ~support[u])
        signed[w] = pivots
        if pivots:
            for outer in _cone(n, gates, out, w):
                if 0 <= outer < n:
                    pivots &= ~(1 << outer)
            if pivots:
                return w, (pivots & -pivots).bit_length() - 1
    return None


@dataclass(frozen=True)
class Step:
    pivot: int
    original_gate: int
    old_gates: tuple
    old_wire: int


def _select(n, x, indices):
    result = 0
    for i in indices:
        result = (result << 1) | ((x >> (n - 1 - i)) & 1)
    return result


@dataclass(frozen=True)
class Compression:
    n: int
    F: tuple
    active: tuple
    dropped: tuple
    steps: tuple

    @property
    def width(self):
        return len(self.active)

    def project(self, x):
        _word(self.n, x)
        for step in self.steps:
            mask = 1 << (self.n - 1 - step.pivot)
            y = evaluate(self.n, step.old_gates, step.old_wire, x)
            x = (x | mask) if y else (x & ~mask)
        return _select(self.n, x, self.active)

    def lift(self, y, free=0):
        _word(self.width, y)
        _word(len(self.dropped), free)
        x = 0
        for indices, bits in ((self.active, y), (self.dropped, free)):
            for j, i in enumerate(indices):
                if bits & (1 << (len(indices) - 1 - j)):
                    x |= 1 << (self.n - 1 - i)
        for step in reversed(self.steps):
            mask = 1 << (self.n - 1 - step.pivot)
            if evaluate(self.n, step.old_gates, step.old_wire, x & ~mask):
                x ^= mask
        return x


def compress(n, F):
    _natural(n, "arity")
    original = _source(n, F)
    gates, out = original
    F, origin = _clean(n, original, range(n, n + len(gates)))
    steps = []
    while True:
        candidate = _candidate(n, F)
        if candidate is None:
            break
        w, p = candidate
        steps.append(Step(p, origin[w - n], F[0], w))
        F, origin = _clean(n, F, origin, w, p)
    gates, out = F
    live = _cone(n, gates, out)
    active = tuple(i for i in range(n) if i in live)
    dropped = tuple(i for i in range(n) if i not in live)
    index = {w: i for i, w in enumerate(active)}

    def compact(w):
        if w < 0:
            return w
        return index[w] if w < n else len(active) + w - n

    reduced = tuple((compact(a), compact(b)) for a, b in gates), compact(out)
    return Compression(n, reduced, active, dropped, tuple(steps))


def solve(n, F, *, max_points=None):
    _natural(n, "arity")
    original = _source(n, F)
    reduced = compress(n, original)
    result = sampled_solve(reduced.width, reduced.F, max_points=max_points)
    if result["status"] == "witness":
        y = result["assignment"]
        x = reduced.lift(y)
        if reduced.project(x) != y or not evaluate(n, *original, x):
            raise AssertionError("lift failed original NAND replay")
        result = dict(result, assignment=x, compact_assignment=y)
    return dict(result, reduced_width=reduced.width, rewrites=len(reduced.steps),
                free_bits=len(reduced.dropped))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-points", type=int)
    args = parser.parse_args()
    data = json.load(sys.stdin)
    result = solve(data["n"], data["F"], max_points=args.max_points)
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    print(json.dumps(result, sort_keys=True))
