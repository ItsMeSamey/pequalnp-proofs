"""Check individual linear consequences in the fixed six-site symbolic reservoir."""
from itertools import combinations

ROWS = (170, 449, 240, 81, 300, 341, 174, 327, 178)


def main():
    # The low six bits are the inner selections. The next three are payload parities.
    def guards(z):
        inner = z & 63
        colors = z >> 6
        source = 3 ^ (colors & 5)
        target = 7 ^ (colors >> 1)
        out = source
        for i, row in enumerate(ROWS[3:]):
            if (inner >> i) & 1:
                out ^= row & 7
                parity = ((inner & (row >> 3)).bit_count()
                          + (target & row & 7).bit_count()) % 2
                out |= parity << (i + 3)
        return out

    for degree in (2, 3):
        monomials = [sum(1 << i for i in positions)
                     for d in range(degree + 1) for positions in combinations(range(9), d)]
        index = {m: i for i, m in enumerate(monomials)}
        col = []
        for m in monomials:
            v = 0
            s = m
            while True:
                v ^= guards(s)
                if not s:
                    break
                s = (s - 1) & m
            col.append(v)
        assert not any(c for c, m in zip(col, monomials) if m.bit_count() > 2)
        basis, pending = {}, []

        def reduce(p):
            while p and p.bit_length() in basis:
                p ^= basis[p.bit_length()]
            return p

        def insert(p):
            p = reduce(p)
            if p:
                basis[p.bit_length()] = p
                if monomials[p.bit_length() - 1].bit_count() < degree:
                    pending.append(p)

        for j in range(9):
            insert(sum(((c >> j) & 1) << i for i, c in enumerate(col)))
        for p in pending:
            for j in range(9):
                prod = 0
                for i,m in enumerate(monomials):
                    if (p >> i) & 1:
                        prod ^= 1 << index[m | (1 << j)]
                insert(prod)
        linear = [1 << index[1 << j] for j in (6, 7, 8)]
        linear[-1] ^= 1
        membership = tuple(reduce(p) == 0 for p in linear)
        print(degree, len(basis), membership)
        if degree == 3:
            assert all(membership)
    valid = [v for v in range(512) if guards(v) == 0]
    assert {v >> 6 for v in valid} == {4} and ((4 << 6) | 9) in valid


if __name__ == "__main__":
    main()
