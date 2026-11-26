"""Exact sampled circuit-equation direction checks and multiplexer residues."""
from itertools import product
from random import Random


def walsh(values):
    a = [1 - 2 * v for v in values]
    step = 1
    while step < len(a):
        for start in range(0, len(a), 2 * step):
            for i in range(start, start + step):
                x, y = a[i], a[i + step]
                a[i], a[i + step] = x + y, x - y
        step *= 2
    return a


def residue(values):
    spectrum = walsh(values)
    scale = min(abs(x) & -abs(x) for x in spectrum if x)
    return (len(values) // scale).bit_length() - 1, [x // scale % 2 for x in spectrum]


def span(vectors):
    group = [0]
    seen = {0}
    for vector in vectors:
        if vector not in seen:
            group += [v ^ vector for v in group]
            seen = set(group)
    return group


def degree(values):
    a = values[:]
    step = 1
    while step < len(a):
        for base in range(0, len(a), 2 * step):
            for i in range(base, base + step):
                a[i + step] ^= a[i]
        step *= 2
    return max((i.bit_count() for i, x in enumerate(a) if x), default=-1)


def check_circuit(n, r, rng):
    gates = [[(rng.randrange(1 << (n + i)), rng.randrange(2)) for _ in range(2)]
             for i in range(r)]
    output = rng.randrange(1 << (n + r)) | (1 << (n + r - 1))
    values = []
    for x in range(1 << n):
        wires = x
        for i, (a, b) in enumerate(gates):
            left = (wires & a[0]).bit_count() % 2 ^ a[1]
            right = (wires & b[0]).bit_count() % 2 ^ b[1]
            wires |= (left & right) << (n + i)
        values.append((wires & output).bit_count() % 2)
    g, odd = residue(values)
    H = span(mask for pair in gates for mask, _ in pair)
    D = span(v for v in H if v < 1 << n)
    nu = 2 * r - (len(H).bit_length() - 1)
    assert 0 <= nu <= 2 * (r - g)
    assert len(D).bit_length() - 1 >= r + 1 - nu
    done = set()
    for x in range(1 << n):
        if x not in done:
            coset = [x ^ v for v in D]
            done.update(coset)
            assert degree([odd[i] for i in coset]) <= 2 * (r - g) - nu
    if r == g:
        support = [i for i, y in enumerate(odd) if y]
        translated = {i ^ support[0] for i in support}
        assert len(span(translated)) == len(translated)
        assert r + 1 <= len(translated).bit_length() - 1 <= 2 * r


def check_mux():
    for n in range(2, 8):
        m = (1 << n) - 1
        values = []
        expected = []
        for selector, b, a in product(range(2), range(m + 1), range(m + 1)):
            values.append((b if selector else a) == m)
            expected.append((a == 0) ^ (b == 0))
        g, odd = residue(values)
        assert g == n and odd == expected
        assert sum(odd) == 4 * (2**n - 1)


if __name__ == "__main__":
    rng = Random(73103)
    tests = 0
    for n in range(2, 7):
        for r in range(1, 6):
            for _ in range(12):
                check_circuit(n, r, rng)
                tests += 1
    check_mux()
    print(f"{tests} seeded circuits: all coset-degree and saturation conditions verified")
    print("6 mux spectra, including all frequencies of the 15-input example")
