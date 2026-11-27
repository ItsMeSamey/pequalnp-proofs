"""Conditional SAT extraction using a caller-supplied, polynomial-clock predictor.

predict(n,cap,history,query) returns one bit on a fresh replay of that history.
Circuits are immutable (NAND pairs, output) on the same original arity throughout.
'positive' requires positive support only for proper thresholds at realizable
all-positive all-wrong histories, plus an n-mistake bound on all realizable
circuit streams. A false source forecast positive at reset would cost an error
on label zero while retaining the entire cube; n fresh coordinate mistakes
could then be forced on one assignment. Thus a reset positive implies SAT.
'one' and 'two' need respectively one-
or two-wise feasibility at realizable all-wrong histories, without a mistake
bound. Arbitrary callbacks do not give a decision guarantee. Returned witnesses
always have their original source evaluated. The caller supplies the clock.
"""
import argparse
import importlib
import json
import sys

from primitive_forecast_extractor import _natural, _source
from primitive_rewrite_chain import evaluate


def public_cap(n, s):
    return _natural(s, "gate count") + 8 * _natural(n, "arity") + 8


def threshold(n, j):
    """Canonical raw NAND comparator [packed x <= j], MSB first."""
    _natural(n, "arity")
    if type(j) is not int or not -1 <= j < 1 << n:
        raise ValueError("threshold out of range")
    if j == -1:
        return (), -1
    if j == (1 << n) - 1:
        return (), -2
    gates = []

    def nand(a, b):
        wire = n + len(gates)
        gates.append((a, b))
        return wire

    smaller = -2
    for i in reversed(range(n)):
        if j & (1 << (n - 1 - i)):
            smaller = nand(i, nand(smaller, smaller))
        else:
            blocked = nand(nand(i, i), smaller)
            smaller = nand(blocked, blocked)
    return tuple(gates), smaller


def _bind(F, i, bit):
    gates, output = F
    constant = -1 - bit

    def sub(wire):
        return constant if wire == i else wire

    return tuple((sub(a), sub(b)) for a, b in gates), sub(output)


class _Run:
    def __init__(self, n, F, predict, mode):
        if mode not in ("positive", "one", "two"):
            raise ValueError("unknown consistency mode")
        self.n = n
        self.cap = public_cap(n, len(F[0]))
        self.mode = mode
        self.predict = predict
        self.stats = dict(decisions=0, forecasts=0, committed_errors=0,
                          max_history=0, false_crossings=0, early_yes=0)

    def ask(self, history, query):
        if len(query[0]) > self.cap:
            raise ValueError("raw NAND query exceeds the public cap")
        self.stats["forecasts"] += 1
        bit = self.predict(self.n, self.cap, history, query)
        if type(bit) not in (int, bool) or bit not in (0, 1):
            raise ValueError("predictor returned a non-bit")
        return int(bit)

    def positive_error(self, history, query):
        # The preceding prediction on this frozen state was zero.
        history = history + ((query, 1),)
        self.stats["committed_errors"] += 1
        self.stats["max_history"] = max(self.stats["max_history"], len(history))
        return history

    def decision(self, F):
        self.stats["decisions"] += 1
        n = self.n
        if n == 0:
            return bool(evaluate(n, *F, 0)), 0
        if self.mode == "one":
            residual = F
            guess = 0
            for i in range(n):
                if self.ask((), residual):
                    self.stats["early_yes"] += 1
                    return True, None
                history = self.positive_error((), residual)
                bit = self.ask(history, ((), i))
                residual = _bind(residual, i, bit)
                guess = (guess << 1) | bit
            return bool(evaluate(n, *F, guess)), guess

        if self.ask((), F):
            self.stats["early_yes"] += 1
            return True, None
        history = self.positive_error((), F)
        top = (1 << n) - 1
        while True:
            if self.mode == "positive" and len(history) > n:
                return False, None
            lo, hi = -1, top
            left = None
            if self.mode == "two":
                if self.ask(history, threshold(n, lo)):
                    return False, None
                if not self.ask(history, threshold(n, hi)):
                    return False, None
            # Positive mode uses the known endpoint truth values synthetically.
            # A nonempty live model set always supports the full upper endpoint.
            while hi - lo > 1:
                mid = (lo + hi) // 2
                middle = threshold(n, mid)
                if self.ask(history, middle):
                    hi = mid
                else:
                    lo, left = mid, middle
            if evaluate(n, *F, hi):
                return True, hi
            self.stats["false_crossings"] += 1
            if self.mode == "two" or hi == 0:
                return False, None
            # Some live model is <=hi. Since F(hi)=0 it is also <=hi-1.
            # Here lo>=0, so this lower threshold really was asked and voted 0.
            history = self.positive_error(history, left)


def decide(n, F, predict, mode="positive"):
    _natural(n, "arity")
    F = _source(n, F)
    return _Run(n, F, predict, mode).decision(F)[0]


def solve(n, F, predict, mode="positive"):
    _natural(n, "arity")
    F = _source(n, F)
    run = _Run(n, F, predict, mode)
    yes, point = run.decision(F)
    if not yes:
        return dict(status="unsat", cap=run.cap, **run.stats)
    if point is None:
        # An early positive answer supplies no point. Decide each zero
        # branch with fresh histories; a negative answer forces the one.
        residual = F
        point = 0
        for i in range(n):
            zero = _bind(residual, i, 0)
            choose_zero, _ = run.decision(zero)
            bit = int(not choose_zero)
            residual = zero if choose_zero else _bind(residual, i, 1)
            point = (point << 1) | bit
    if not evaluate(n, *F, point):
        raise ValueError("positive decision failed original assignment verification")
    return dict(status="witness", assignment=point, cap=run.cap, **run.stats)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--learner", required=True, metavar="MODULE:CALLABLE")
    parser.add_argument("--mode", choices=("positive", "one", "two"), default="positive")
    args = parser.parse_args()
    module, sep, name = args.learner.partition(":")
    if not sep or not name:
        parser.error("expected MODULE:CALLABLE")
    data = json.load(sys.stdin)
    predictor = getattr(importlib.import_module(module), name)
    print(json.dumps(solve(data["n"], data["F"], predictor, args.mode)))
