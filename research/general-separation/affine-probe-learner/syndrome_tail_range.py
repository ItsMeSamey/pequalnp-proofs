"""Syntactic affine tail-syndrome cuts with exact original NAND interval counts.

The inherited TailRange interval API enumerates latent words of width m (rank).
tail_width is the actual physical suffix width. Basis coordinates are MSB-first.
For each possible suffix recognize signed XORs of tail bits with arbitrary
prefix functions. Formally identical offset tokens cancel. Repeated slopes
are accepted when Gaussian elimination leaves a constant offset. Keep the
smallest latent rank among the tested maximal cuts and the permutation cut.
All preprocessing is polynomial; queries cost 2**rank times polynomial work
and polynomial space. No minimality among untested certificates is claimed.
"""
from dataclasses import dataclass
from pivot_cone_rewrite import _xor, _word
from primitive_forecast_extractor import _source, _natural
from tail_permutation_range import TailRange, recognize as permutation_cut


def _profiles(h, gates, width):
    rows = {-1: (0, 0), -2: (0, 1)}
    for i in range(h):
        rows[i] = (1 << (h-1-i), 0) if i >= h-width else (0, 1 << (i+1))
    for w, (a, b) in enumerate(gates, h):
        left, right = rows.get(a), rows.get(b)
        if left == (0, 0) or right == (0, 0):
            rows[w] = (0, 1)
        elif a == b or left == (0, 1) or right == (0, 1):
            operand = right if left == (0, 1) else left
            if operand is not None:
                rows[w] = operand[0], operand[1] ^ 1
        else:
            pair = _xor(h, gates, a, b)
            if pair is not None and all(i in rows for i in pair):
                (s, f), (t, g) = (rows[i] for i in pair)
                rows[w] = s ^ t, f ^ g
            elif left is not None and right is not None and left[0] == right[0] == 0:
                rows[w] = 0, 1 << (w+1)
    return rows


def _candidate(h, original, width):
    gates, out = original
    rows = _profiles(h, gates, width)
    cuts, outer, stack = set(), set(), [out]
    while stack:
        w = stack.pop()
        if w < 0 or w in cuts or w in outer:
            continue
        if w in rows:
            cuts.add(w)
        else:
            outer.add(w)
            stack.extend(gates[w-h])
    basis, pivots, image = [], {}, {}
    for w in sorted(cuts):
        s, f = rows[w]
        coeff = 0
        while s:
            j = s.bit_length()-1
            if j not in pivots:
                break
            a, b, c = pivots[j]
            s, f, coeff = s ^ a, f ^ b, coeff ^ c
        if s:
            single = 1 << len(basis)
            pivots[s.bit_length()-1] = s, f, coeff ^ single
            basis.append(w)
            image[w] = single, 0
        elif f <= 1:
            image[w] = coeff, f
        else:
            return None
    rank = len(basis)
    built, labels = [], {-1: -1, -2: -2}

    def nand(a, b):
        built.append((a, b))
        return rank+len(built)-1

    for w, (coeff, bit) in image.items():
        wire = -1
        while coeff:
            low = coeff & -coeff
            i = low.bit_length()-1
            if wire == -1:
                wire = i
            else:
                share = nand(wire, i)
                wire = nand(nand(wire, share), nand(i, share))
            coeff ^= low
        labels[w] = nand(wire, wire) if bit else wire
    for w in sorted(outer):
        a, b = gates[w-h]
        labels[w] = nand(labels[a], labels[b])
    return SyndromeRange(h, original, tuple(basis), (tuple(built), labels[out]),
                         width, tuple(rows[w][0] for w in basis))


def _count(width, equations):
    pivots = {}
    for row, rhs in equations:
        while row:
            i = row.bit_length()-1
            if i not in pivots:
                pivots[i] = row, rhs
                break
            a, b = pivots[i]
            row, rhs = row ^ a, rhs ^ b
        else:
            if rhs:
                return 0
    return 1 << (width-len(pivots))


@dataclass(frozen=True)
class SyndromeRange(TailRange):
    tail_width: int
    slopes: tuple

    def offset(self, u):
        _word(self.h-self.tail_width, u)
        x = u << self.tail_width
        values = {-1: 0, -2: 1}
        for i in range(self.h):
            values[i] = (x >> (self.h-1-i)) & 1
        for w, (a, b) in enumerate(self.original[0], self.h):
            values[w] = 1 ^ (values[a] & values[b])
        return sum(values[w] << (self.m-1-i) for i, w in enumerate(self.cuts))

    def _boundary(self, j):
        if type(j) is not int or not -1 <= j < 1 << self.h:
            raise ValueError("invalid rank boundary")
        if j < 0:
            return 0, 0, -1
        u, t = divmod(j, 1 << self.tail_width)
        return u, self.offset(u), t

    def _rank(self, z, boundary):
        u, offset, t = boundary
        if t < 0:
            return 0
        width = self.tail_width
        total = u << (width-self.m)
        target = z ^ offset
        eq = [(s, (target >> (self.m-1-i)) & 1) for i, s in enumerate(self.slopes)]
        for j in reversed(range(width)):
            row, bit = 1 << j, (t >> j) & 1
            if bit:
                total += _count(width, [*eq, (row, 0)])
            eq.append((row, bit))
        return total + _count(width, eq)

    def project(self, x):
        _word(self.h, x)
        out = self.offset(x >> self.tail_width)
        for i, s in enumerate(self.slopes):
            out ^= ((x & s).bit_count() & 1) << (self.m-1-i)
        return out

    def lift(self, ordinal, z):
        """Recover the zero-based ordinal's raw word in the full z-fiber."""
        _word(self.h-self.m, ordinal)
        _word(self.m, z)
        low, high = 0, (1 << self.h)-1
        while low < high:
            mid = (low+high)//2
            if self.rank(z, mid) > ordinal:
                high = mid
            else:
                low = mid+1
        return low


def recognize(h, F):
    _natural(h, "arity")
    original = _source(h, F)
    prev = permutation_cut(h, original)
    best = SyndromeRange(h, original, prev.cuts, prev.F, prev.m,
                         tuple(1 << j for j in reversed(range(prev.m))))
    for width in range(h+1):
        candidate = _candidate(h, original, width)
        if candidate is not None and (candidate.m, width) < (best.m, best.tail_width):
            best = candidate
    return best


def solve(h, F, lo, hi, *, max_latents=None):
    model = recognize(h, F)
    model._interval(lo, hi)
    if max_latents is not None:
        _natural(max_latents, "max_latents")
    required = 1 << model.m
    if lo <= hi and max_latents is not None and required > max_latents:
        return dict(status="unknown", reason="latent_budget", required=required,
                    available=max_latents, latent_width=model.m)
    count, x = model._query(lo, hi, count_all=True)
    if x is None:
        return dict(status="unsat", count=0, latent_width=model.m)
    return dict(status="witness", count=count, assignment=x, latent_width=model.m)
