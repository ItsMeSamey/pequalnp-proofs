"""Stream exact scores for lexicographic physical lists at one fixed prefix."""
from itertools import product
from math import comb
from operator import index


def scaled_coefficients(m, order, support):
    """Return 2**m times the Walsh coefficients at support for powers 0..order."""
    values = [1] + [0] * order
    for i in range(m):
        sign = -1 if (support >> i) & 1 else 1
        values = [
            (1 + sign) * values[t] + sign * sum(
                comb(t, a) * (values[t-a] << (i*a)) for a in range(1, t+1)
            ) for t in range(order+1)
        ]
    return values


class OrderedScores:
    """feed(row, score) receives every actual list, including equal-score duplicates."""
    def __init__(self, m, length, base, order=None):
        self.m, self.length, self.base = map(index, (m, length, base))
        self.order = self.length if order is None else index(order)
        if self.m < 1 or self.base < 0 or not 0 <= self.order <= self.length:
            raise ValueError("invalid stage parameters")
        self.seen = 0
        self.terms = 0
        self.sums = [0] * (self.order+1)
        self.best = None
        self.winner = None

    def feed(self, row, score):
        row = tuple((index(i), index(c)) for i, c in row)
        score = index(score)
        if len(row) != self.length or not 0 <= score <= self.base:
            raise ValueError("invalid trial length or score")
        rank = mask = 0
        for i, c in row:
            if not 0 <= i < self.m or c not in (0, 1):
                raise ValueError("invalid physical row entry")
            rank = rank*(2*self.m) + 2*i + c
            mask ^= c << i
        if rank != self.seen:
            raise ValueError("expected next physical list in lexicographic order")
        if not mask and score != self.base:
            raise ValueError("zero row must preserve the prefix score")
        self.seen += 1
        if self.best is None or score < self.best:
            self.best, self.winner = score, row
        size = mask.bit_count()
        if size > self.order:
            return
        indices = tuple((i, 1) for i in range(self.m) if mask >> i & 1)
        if row != indices + ((0, 0),)*(self.length-size):
            return
        self.terms += 1
        signed = 2*score-self.base
        for k, a in enumerate(scaled_coefficients(self.m, self.order, mask)):
            self.sums[k] += a*signed

    def finish(self):
        if self.seen != (2*self.m)**self.length:
            raise ValueError("incomplete ordered trial stream")
        moments = []
        for total in self.sums:
            q, r = divmod(total, 1 << self.m)
            if r:
                raise ValueError("scores gave a nonintegral moment")
            moments.append(q)
        return tuple(moments), self.winner, self.best


def integrate(m, length, base, score, order=None):
    """Call the physical-list oracle once per list; preserve the original first tie."""
    stream = OrderedScores(m, length, base, order)
    alphabet = product(range(m), range(2))
    for row in product(alphabet, repeat=length):
        stream.feed(row, score(row))
    return stream.finish()
