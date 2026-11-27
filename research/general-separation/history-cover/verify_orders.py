"""Independently check the history-cover compiler on exhaustively evaluated small circuits."""

from itertools import combinations
from random import Random

from cover import compile_system, conflicts, cuts, search_cover


def direct(n, gates, output, x):
    values = 1 | (x << 1)
    for i, (u, v, w) in enumerate(gates):
        left, right, linear = ((mask & values).bit_count() % 2 for mask in (u, v, w))
        bit = (left * right + linear) % 2
        values |= bit << (n + 1 + i)
    return (output & values).bit_count() % 2


def renamed(n, gates, output, rng):
    pending = set(range(len(gates)))
    new_order = []
    seen = 0
    while pending:
        ready = [i for i in sorted(pending) if ((gates[i][0] | gates[i][1] | gates[i][2]) >> (n + 1)) & ~seen == 0]
        i = rng.choice(ready)
        new_order.append(i)
        seen |= 1 << i
        pending.remove(i)

    def remap(mask):
        result = mask % (1 << (n + 1))
        for new, old in enumerate(new_order):
            result |= ((mask >> (n + 1 + old)) & 1) << (n + 1 + new)
        return result

    return [tuple(remap(mask) for mask in gates[i]) for i in new_order], remap(output)


def cut_oracle(n, gates, output):
    pairs = set()
    actual = list(cuts(n, gates, output))
    assert len(actual) == len(gates) + 1
    for cut in range(len(gates) + 1):
        future = [mask for gate in gates[cut:] for mask in gate] + [output]
        expected = [[(row >> (n + 1 + j)) & 1 for j in range(cut)] for row in future]
        assert actual[cut] == [sum(bit << j for j, bit in enumerate(row)) for row in expected]
        for a, b in combinations(range(cut), 2):
            restrictions = {((row >> (n + 1 + a)) & 1, (row >> (n + 1 + b)) & 1) for row in future}
            if len(restrictions - {(0, 0)}) >= 2:
                pairs.add((a, b))
    return pairs


def verify(n, gates, output, expected, rng):
    edges = conflicts(n, gates, output)
    pairs = {tuple(sorted(edge)) for edge in edges}
    assert pairs == cut_oracle(n, gates, output)
    m = len(gates)
    candidates = [set(c) for j in range(m + 1) for c in combinations(range(m), j)
                  if all(a in c or b in c for a, b in pairs)]
    if pairs:
        try:
            compile_system(n, gates, output, set())
        except ValueError:
            pass
        else:
            raise AssertionError("Compiler accepted an uncovered cut")
    optimum = min(map(len, candidates))
    for t in {0, optimum, max(0, optimum - 1), m}:
        found = search_cover(edges, t)
        assert (found is not None) == (t >= optimum)
        if found is not None:
            assert len(found) <= t and all(a in found or b in found for a, b in pairs)
    for chosen in [candidates[0], candidates[-1], rng.choice(candidates)]:
        system = compile_system(n, gates, output, chosen)
        for x, value in enumerate(expected):
            assert bool(system.evaluate(x)) == bool(value), (n, gates, output, chosen, x)


def main():
    rng = Random(378011)
    cases = [(2, [], 0), (2, [], 7)]
    # u=v=w makes the actual gate zero by Boolean idempotence; retain its formal history.
    cases += [(2, [(2, 4, 0), (8, 8, 8), (8, 16, 8)], 32),
              (2, [(2, 4, 0), (4, 2, 0), (8 ^ 16, 8 ^ 16, 8 ^ 16)], 32)]
    for _ in range(120):
        n = rng.randint(1, 5)
        m = rng.randint(1, 8)
        gates = []
        for i in range(m):
            rows = [rng.randrange(1 << (n + 1)) for _ in range(3)]
            for j in range(i):
                for k in range(3):
                    if rng.randrange(7) == 0:
                        rows[k] ^= 1 << (n + 1 + j)
            gates.append(tuple(rows))
        cases.append((n, gates, rng.randrange(1 << (n + 1 + m))))
    for n, gates, output in cases:
        expected = [direct(n, gates, output, x) for x in range(1 << n)]
        verify(n, gates, output, expected, rng)
        for _ in range(3):
            other, readout = renamed(n, gates, output, rng)
            assert [direct(n, other, readout, x) for x in range(1 << n)] == expected
            verify(n, other, readout, expected, rng)
    print(f"{len(cases)} circuits; {4 * len(cases)} orders passed")


if __name__ == "__main__":
    main()
