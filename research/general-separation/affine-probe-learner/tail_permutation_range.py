"""Certified NAND tail permutations and exact closed-interval queries.

For a recognized m-bit suffix t the original G obeys G(u,t)=B(t XOR g(u)).
Input 0 is the most significant bit; t is the least significant m bits.
A cut for tail input i must have an XOR/inversion spine from i, omit every
other tail variable syntactically, and intercept every i-to-output path.
Use the last eligible wire in original topological order for each tail, then
check the outer cone reaches no raw variable without first hitting a cut.
An unused tail is represented by its own input. Try suffix widths in ascending
order, finally using the full identity cut. This recognizes a sufficient
structural condition; m is the smallest width accepted by this procedure.

With s gates, preprocessing makes O(s) reachability scans to check individual
domination and at most h+1 joint scans; the simple suffix candidate loop uses
O((h+1)**2*(s+1)) mask operations on O(h+1)-bit integers. All preprocessing
is polynomial in h+s (including allocation of primary-coordinate masks).
Then one inclusive interval query costs O(2**m * poly(h+s)) bit operations
and polynomial working space. Prefix boundary offsets are evaluated once
per bound, independently of 2**(h-m). The raw input encoding is preserved.
"""
import argparse
from dataclasses import dataclass
import json
import sys

from pivot_cone_rewrite import _cone, _word, _xor
from primitive_forecast_extractor import _natural, _source
from primitive_rewrite_chain import evaluate


def _profiles(h, gates, out):
    support = {-1: 0, -2: 0}
    signed = {-1: 0, -2: 0}
    eligible = {}
    live = _cone(h, gates, out)
    for i in range(h):
        support[i] = signed[i] = 1 << i
    for w, (a, b) in enumerate(gates, h):
        support[w] = support[a] | support[b]
        spines = 0
        if a == b:
            spines = signed[a]
        else:
            pair = _xor(h, gates, a, b)
            if pair is not None:
                u, v = pair
                spines = (signed[u] & ~support[v]) | (signed[v] & ~support[u])
        signed[w] = spines
        if spines and w in live:
            for i in _cone(h, gates, out, w):
                if 0 <= i < h:
                    spines &= ~(1 << i)
            if spines:
                eligible[w] = spines
    return support, eligible


def _outer(h, gates, out, cuts):
    m = len(cuts)
    mapped = {wire: i for i, wire in enumerate(cuts)}
    mapped.update({-1: -1, -2: -2})
    stack = [out]
    live = set()
    while stack:
        wire = stack.pop()
        if wire in mapped or wire in live:
            continue
        if wire < h:
            return None
        live.add(wire)
        stack.extend(gates[wire-h])
    outer = []
    for w in sorted(live):
        a, b = gates[w-h]
        mapped[w] = m + len(outer)
        outer.append((mapped[a], mapped[b]))
    return tuple(outer), mapped[out]


@dataclass(frozen=True)
class TailRange:
    h: int
    original: tuple
    cuts: tuple
    F: tuple

    @property
    def m(self):
        return len(self.cuts)

    @property
    def width(self):
        return self.m

    def offset(self, u):
        """Evaluate the cut word at (u,0) on the full original gate ordering."""
        _word(self.h - self.m, u)
        x = u << self.m
        values = [(x >> (self.h-1-i)) & 1 for i in range(self.h)]

        def value(w):
            return -1-w if w < 0 else values[w]

        for a, b in self.original[0]:
            values.append(1 ^ (value(a) & value(b)))
        result = 0
        for wire in self.cuts:
            result = (result << 1) | value(wire)
        return result

    def lift(self, u, y):
        _word(self.m, y)
        return (u << self.m) | (y ^ self.offset(u))

    def project(self, x):
        _word(self.h, x)
        return (x & ((1 << self.m)-1)) ^ self.offset(x >> self.m)

    def _boundary(self, j):
        if type(j) is not int or not -1 <= j < 1 << self.h:
            raise ValueError("invalid inclusive rank boundary")
        if j == -1:
            return 0, 0, -1
        u, t = divmod(j, 1 << self.m)
        return u, self.offset(u), t

    @staticmethod
    def _rank(y, boundary):
        u, offset, t = boundary
        return u + int((y ^ offset) <= t)

    def rank(self, y, j):
        """Number of original words at most j projecting to the specified y."""
        _word(self.m, y)
        return self._rank(y, self._boundary(j))

    def _interval(self, lo, hi):
        if type(lo) is not int or not 0 <= lo <= 1 << self.h:
            raise ValueError("invalid inclusive lower bound")
        if type(hi) is not int or not -1 <= hi < 1 << self.h:
            raise ValueError("invalid inclusive upper bound")
        if lo > hi:
            return None
        return self._boundary(lo-1), self._boundary(hi)

    def _query(self, lo, hi, *, count_all):
        bounds = self._interval(lo, hi)
        if bounds is None:
            return 0, None
        before, end = bounds
        total, witness = 0, None
        for y in range(1 << self.m):
            first = self._rank(y, before)
            size = self._rank(y, end) - first
            if not size or not evaluate(self.m, *self.F, y):
                continue
            total += size
            if witness is None:
                # Exactly one point of this fiber per prefix, in prefix order;
                # its zero-based rank within the whole fiber is its prefix.
                witness = self.lift(first, y)
                if not lo <= witness <= hi or not evaluate(self.h, *self.original, witness):
                    raise AssertionError("tail lift did not produce an original interval witness")
                if not count_all:
                    break
        return total, witness

    def range_count(self, lo, hi):
        return self._query(lo, hi, count_all=True)[0]

    def witness(self, lo, hi):
        return self._query(lo, hi, count_all=False)[1]


def recognize(h, F):
    _natural(h, "arity")
    original = _source(h, F)
    gates, out = original
    support, eligible = _profiles(h, gates, out)
    for m in range(h + 1):
        start = h - m
        cuts = list(range(start, h))
        if m < h:
            for w, candidates in eligible.items():
                tail_support = support[w] >> start
                if tail_support and tail_support & (tail_support-1) == 0:
                    slot = tail_support.bit_length()-1
                    if candidates & (1 << (start + slot)):
                        cuts[slot] = w
        cuts = tuple(cuts)
        outer = _outer(h, gates, out, cuts)
        if outer is not None:
            return TailRange(h, original, cuts, outer)
    raise AssertionError("identity cut failed")


def solve(h, F, lo, hi, *, max_latents=None):
    model = recognize(h, F)
    model._interval(lo, hi)
    if max_latents is not None:
        _natural(max_latents, "max_latents")
    required = 1 << model.m
    if lo <= hi and max_latents is not None and required > max_latents:
        return dict(status="unknown", reason="latent_budget", required=required,
                    available=max_latents, latent_width=model.m)
    count, witness = model._query(lo, hi, count_all=True)
    if witness is None:
        return dict(status="unsat", count=count, latent_width=model.m)
    return dict(status="witness", count=count, assignment=witness, latent_width=model.m)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-latents", type=int)
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    args = parser.parse_args()
    data = json.load(sys.stdin)
    answer = solve(data["n"], data["F"], data["lo"], data["hi"],
                   max_latents=args.max_latents)
    print(json.dumps(answer, separators=(",", ":")))
