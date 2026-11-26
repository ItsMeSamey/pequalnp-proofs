"""Verify physical optional gates, feedback, arbitrary-mask rebasing and seam costs."""
from random import Random


def comp(p, q):
    return tuple(p[x] for x in q)


def inverse(p):
    return tuple(p.index(x) for x in range(len(p)))


def perm(n, *cycles):
    p = list(range(n))
    for cycle in cycles:
        for a, b in zip(cycle, cycle[1:] + cycle[:1]):
            p[a] = b
    return tuple(p)


def evaluate(gates, feedback, s):
    p = feedback
    for i, g in enumerate(gates):
        if s >> i & 1:
            p = comp(g, p)
    return p


def orbits(p):
    unseen = set(range(len(p)))
    count = 0
    while unseen:
        x = next(iter(unseen))
        while x in unseen:
            unseen.remove(x)
            x = p[x]
        count += 1
    return count


def rebase(gates, f, flips):
    h = tuple(range(len(f)))
    local = []
    for i in reversed(range(len(gates))):
        g = gates[i]
        bit = flips >> i & 1
        local.append(comp(comp(h, inverse(g) if bit else g), inverse(h)))
        if bit:
            h = comp(h, g)
    return local[::-1], comp(h, f)


def check():
    rng = Random(718)
    total = queries = 0
    for m in range(1, 8):
        n, end = 2*m + 2, 1 << m
        a, x0 = 0, 1
        x = [x0] + list(range(2, n, 2))
        y = list(range(3, n, 2))
        pairs = list(range(2, n))
        gates = [perm(n, (x[i+1], y[i], x[i])) for i in range(m)]
        swap = perm(n, (a, x[-1]))
        for positive in (False, True):
            f = perm(n, [a, x0], pairs) if positive else perm(n, [a], [x0] + pairs)
            for theta in range(end):
                flips = theta ^ (end-1)
                gs, ff = rebase(gates, f, flips)
                for s in range(end):
                    p = evaluate(gs, ff, s)
                    assert p == evaluate(gates, f, s ^ flips)
                    assert orbits(p) == 2
                    assert orbits(comp(swap, p)) == (3 if positive and s == theta else 1)
                    total += 1
        for _ in range(100):
            ident = [rng.randrange(-3, 4) + 2 for s in range(end)]
            cross = [rng.randrange(-3, 4) + 1 for s in range(end)]
            baseline = min(ident + cross)
            active = [t for t in range(end) if min(ident + [
                v + 2*(i == t) for i, v in enumerate(cross)]) != baseline]
            assert len(active) <= 1
            queries += 1
    print(f'{total} rebased physical permutations and {queries} signed-weight queries verified')


if __name__ == '__main__':
    check()
