from itertools import product
from random import Random
from project import compile_projection, evaluate
from solve import holds, witness


def valid(x, guards, terminal, offset=0):
    return (all(not x & (1 << (offset + i)) or holds(c, x) for i, c in enumerate(guards))
            and all(holds(c, x) for c in terminal))


def random_clause(rng, bits):
    return [(rng.randrange(1 << bits), rng.randrange(2)) for _ in range(rng.randrange(4))]


def test_search(rng):
    for _ in range(800):
        n = rng.randrange(9)
        f = rng.randrange(min(n, 3) + 1)
        perm = rng.sample(range(n), n)
        feedback, order = perm[:f], perm[f:]
        guards = [random_clause(rng, n) for i in range(n)]
        known = sum(1 << j for j in feedback)
        for i in order:
            known |= 1 << i
            guards[i] = [(m & known, b) for m, b in guards[i]]
        terminal = [random_clause(rng, n) for _ in range(rng.randrange(4))]
        ans = witness(guards, terminal, order, feedback)
        expected = any(valid(x, guards, terminal) for x in range(1 << n))
        assert (ans is not None) == expected
        assert ans is None or valid(ans, guards, terminal)


def test_projection(rng):
    checks = 0
    for _ in range(500):
        obs, h = rng.randrange(6), rng.randrange(6)
        guards = [random_clause(rng, obs + i + 1) for i in range(h)]
        terminal = [random_clause(rng, obs + h) for _ in range(rng.randrange(5))]
        polys = compile_projection(obs, guards, terminal)
        assert all(m.bit_count() <= len(terminal) for p in polys for m in p)
        for x in range(1 << obs):
            want = any(valid(x | (y << obs), guards, terminal, obs) for y in range(1 << h))
            assert evaluate(polys, x) == want
            checks += 1
    return checks


def inner_product(n):
    guards, terminal = [], []
    odd = 0
    for i in range(n):
        a, b, z = 1 << i, 1 << (n+i), 1 << (2*n+i)
        guards.append([(b, 0)])
        terminal.append([(b, 1), (a | z, 1)])
        odd |= z
    terminal.append([(odd, 0)])
    return guards, terminal


if __name__ == "__main__":
    rng = Random(19937)
    test_search(rng)
    checks = test_projection(rng)
    for n in (1, 2, 3, 4):
        guards, terminal = inner_product(n)
        for a, b in product(range(1 << n), repeat=2):
            base = a | (b << n)
            count = sum(valid(base | (y << (2*n)), guards, terminal, 2*n)
                        for y in range(1 << n))
            assert count == ((a & b).bit_count() % 2)
    print(f"Checked 800 feedback instances, {checks} projections, and inner-product fibers n=1..4.")
