"""Ranked subset convolution over a supplied characteristic-two field.

Tuple index S is the coefficient of the squarefree monomial for subset S.
Each label variable squares to zero. Products cost O(h² 2^h) field operations.
"""


class LabelRing:
    def __init__(self, field, h):
        if type(h) is not int or h < 0:
            raise ValueError("label count must be a nonnegative integer")
        self.field = field
        self.h = h
        self.size = 1 << h
        self.zero = (0,) * self.size
        self.one = (1,) + self.zero[1:]
        self._ranks = tuple(s.bit_count() for s in range(self.size))

    def _check(self, x):
        if len(x) != self.size:
            raise ValueError("wrong number of subset coefficients")

    def add(self, x, y):
        self._check(x)
        self._check(y)
        return tuple(a ^ b for a, b in zip(x, y))

    xor = add

    def square(self, x):
        self._check(x)
        return (self.field.mul(x[0], x[0]),) + self.zero[1:]

    def _transform(self, rows):
        # Subset zeta transform, also its inverse in characteristic two.
        for i in range(self.h):
            step = 1 << i
            for row in rows:
                for block in range(0, self.size, 2 * step):
                    for low in range(block, block + step):
                        row[low + step] ^= row[low]

    def _ranked_zeta(self, x):
        rows = [[0] * self.size for _ in range(self.h + 1)]
        for mask, degree in enumerate(self._ranks):
            rows[degree][mask] = x[mask]
        self._transform(rows)
        return rows

    def mul(self, x, y):
        self._check(x)
        self._check(y)
        left = self._ranked_zeta(x)
        right = self._ranked_zeta(y)
        result = [[0] * self.size for _ in range(self.h + 1)]
        for total, row in enumerate(result):
            for i in range(total + 1):
                a, b = left[i], right[total - i]
                for mask in range(self.size):
                    row[mask] ^= self.field.mul(a[mask], b[mask])
        # Inversion forces union exactly S; total degree |S| forces disjointness.
        self._transform(result)
        return tuple(result[degree][mask] for mask, degree in enumerate(self._ranks))
