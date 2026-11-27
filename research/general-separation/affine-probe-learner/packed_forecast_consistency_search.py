"""Conditional SAT search by packing disjoint tags at one arity and raw NAND cap.

The supplied pure polynomial-clock predictor must make at most h mistakes
on every realizable h-bit circuit stream at the given cap S. A deficient
state is a realizable all-positive all-wrong history beginning with its
source labeled 1, at which some proper comparator T_j is forecast positive
but no survivor satisfies T_j. Across all source histories at common h,S,
assume at most p(h+S) deficient survivor sets can be pairwise disjoint,
where p(t)=C*(t+1)**d and C,d are fixed nonnegative integers.

Every rejected satisfiable trial of the positive decision procedure supplies
such a nonempty survivor set: at the first false crossing where its proposed
lower feedback would destroy realizability (including a false crossing at
zero), the positive upper comparator had no support. A synthetic full upper
endpoint always has support. If no such crossing occurs, the bound prevents
rejection after h+1 errors. A positive reset on an identically false source
would itself violate the mistake bound by h further coordinate mistakes.
Thus no unsatisfiable trial can accept. Tag fibers are pairwise disjoint and
contain every survivor at each trial's nonempty history. The algorithm never
has to locate a deficient state. Its guarantees depend on the supplied learner.

For k>0 the adjusted size parameter h+S is 9n+s+12k+10, with s the
original number of gates. Exponential growth in k dominates its fixed
degree-d polynomial, so the least k is O_{C,d}(log(n+s+2)). By minimality
2**k <= 2*p(h+S) for k>0. Each amplified decision tries at most 2**k
sources sequentially, and witness recovery uses at most n+1 amplified
decisions. The frozen positive procedure uses O((h+1)**2) forecasts per
trial on histories of O(h+1) rows. Tag construction and each raw query
and replay have polynomial bit cost for a polynomial-clock predictor.
No uniform polynomial in the input encodings of arbitrary C,d is claimed.

CLI accepts JSON {"n": ..., "F": [gates, output], "C": ..., "d": ...} and
--learner MODULE:CALLABLE. For large decimal witnesses set
PYTHONINTMAXSTRDIGITS=0 before launching Python.
"""
import argparse
import importlib
import json
import sys

from forecast_consistency_search import _bind, decide as positive_decide, public_cap
from primitive_forecast_extractor import _natural, _source
from primitive_rewrite_chain import evaluate


def parameters(n, s, C=1, d=1):
    """Least feasible k, using the actual learner cap without building tags."""
    for name, value in (("arity", n), ("source size", s), ("C", C), ("d", d)):
        _natural(value, name)
    k = 0
    while True:
        width = n + k
        size = s + (3 * k + 2 if k else 0)
        cap = public_cap(width, size)
        tags = 1 << k
        if tags > C * (width + cap + 1) ** d:
            return dict(k=k, tags=tags, width=width, cap=cap, packed_gates=size)
        k += 1


def tagged(n, F, k, tag):
    """Tag inputs follow the original MSB-first inputs. Gate counts are uniform."""
    _natural(n, "arity")
    _natural(k, "tag width")
    _natural(tag, "tag")
    if tag >= 1 << k:
        raise ValueError("tag out of range")
    original, output = _source(n, F)
    if not k:
        return original, output
    width = n + k

    def shift(w):
        return w + k if w >= n else w

    gates = [(shift(a), shift(b)) for a, b in original]

    def nand(a, b):
        wire = width + len(gates)
        gates.append((a, b))
        return wire

    equal = -2
    for i in range(k):
        wire = n + i
        negative = nand(wire, wire)
        literal = wire if tag & (1 << (k - 1 - i)) else negative
        both = nand(equal, literal)
        equal = nand(both, both)
    masked = nand(shift(output), equal)
    return tuple(gates + [(masked, masked)]), width + len(gates)


class _PackedRun:
    def __init__(self, n, F, predict, C, d):
        self.n = n
        self.predict = predict
        self.plan = parameters(n, len(F[0]), C, d)
        self.decisions = 0
        self.trials = 0

    def decision(self, residual):
        self.decisions += 1
        if self.n == 0:
            return bool(evaluate(0, *residual, 0))
        plan = self.plan
        for tag in range(plan["tags"]):
            circuit = tagged(self.n, residual, plan["k"], tag)
            if len(circuit[0]) != plan["packed_gates"]:
                raise ValueError("tagged source length changed")
            self.trials += 1
            if positive_decide(plan["width"], circuit, self.predict, "positive"):
                return True
        return False


def decide(n, F, predict, C=1, d=1):
    _natural(n, "arity")
    F = _source(n, F)
    return _PackedRun(n, F, predict, C, d).decision(F)


def solve(n, F, predict, C=1, d=1):
    """Self-reduce using amplified decisions on every restricted original source."""
    _natural(n, "arity")
    F = _source(n, F)
    run = _PackedRun(n, F, predict, C, d)
    if not run.decision(F):
        return dict(status="unsat", decisions=run.decisions, trials=run.trials, **run.plan)
    residual = F
    assignment = 0
    for i in range(n):
        zero = _bind(residual, i, 0)
        bit = int(not run.decision(zero))
        residual = _bind(residual, i, 1) if bit else zero
        assignment = (assignment << 1) | bit
    if not evaluate(n, *F, assignment):
        raise ValueError("amplified decisions failed original witness verification")
    return dict(status="witness", assignment=assignment, decisions=run.decisions,
                trials=run.trials, **run.plan)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--learner", required=True, metavar="MODULE:CALLABLE")
    args = parser.parse_args()
    module, sep, name = args.learner.partition(":")
    if not sep or not name:
        parser.error("expected MODULE:CALLABLE")
    data = json.load(sys.stdin)
    learner = getattr(importlib.import_module(module), name)
    result = solve(data["n"], data["F"], learner, data["C"], data["d"])
    print(json.dumps(result, separators=(",", ":")))
