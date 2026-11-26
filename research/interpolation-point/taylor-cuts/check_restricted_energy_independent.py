"""Check the affine-cell character-sum energy identity against direct transforms."""
from fractions import Fraction
from random import Random

rng = Random(201946)
def dot(x, y):
    return (x & y).bit_count() & 1

def subspace(n):
    span = {0}
    for _ in range(rng.randrange(n + 1)):
        x = rng.randrange(1 << n)
        span |= {v ^ x for v in span}
    return span

for trial in range(200):
    n = rng.randrange(1, 6)
    domain = range(1 << n)
    cells = [(Fraction(rng.randrange(-3, 4), rng.randrange(1, 5)), rng.choice(domain),
              subspace(n)) for _ in range(5)]
    if trial % 3 == 0:
        a, b, v = cells[0]
        cells.append((-a, b, v))
    f = [sum(a for a, b, v in cells if (x ^ b) in v) for x in domain]
    spectrum = [sum(Fraction((-1)**dot(x,s), 1 << n)*f[x] for x in domain)
                for s in domain]
    mask = rng.choice(domain)
    affine = {mask ^ s for s in subspace(n)}
    if trial % 11 == 0:
        affine.clear()
    expected = sum(spectrum[s]**2 for s in affine)
    energy = Fraction(0)
    for a, b, v in cells:
        for c, d, w in cells:
            section = {s for s in affine if all(not dot(s, h) for h in v|w)}
            if not section:
                continue
            q = next(iter(section))
            if all(not dot(s ^ q, b ^ d) for s in section):
                energy += a*c*len(v)*len(w)*len(section)*(-1)**dot(q,b^d)/(1 << (2*n))
    assert energy == expected
print("200 signed rational mixtures and affine Fourier restrictions matched exactly")
