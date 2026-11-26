"""Check shortest neutral replacements and direct-sum radii."""
from itertools import combinations
from random import Random


def totals(rows):
    best = {0: ()}
    for v in rows:
        for e, chosen in list(best.items()):
            u = e ^ v
            if u not in best or len(chosen) + 1 < len(best[u]):
                best[u] = chosen + (v,)
    return best


def permitted(rows, sigma):
    return [v for v in rows if (v & sigma).bit_count() % 2 == 0]


def direct_sums(dims):
    offset = 0
    rows = []
    for dim in dims:
        rows.extend(v << offset for v in range(1, 1 << dim))
        offset += dim
    return rows


def check():
    for dims in ((3,), (2, 2), (2, 2, 2), (1, 1, 1, 1)):
        rows = direct_sums(dims)
        radius = max(len(w) for s in range(1 << sum(dims))
                     for w in totals(permitted(rows, s)).values())
        assert radius == len(dims)
    rng = Random(473)
    cases = 0
    for _ in range(100):
        n = rng.randrange(2, 7)
        rows = rng.sample(range(1, 1 << n), rng.randint(1, min(8, (1 << n)-1)))
        allowed = permitted(rows, rng.randrange(1 << n))
        best = totals(allowed)
        expected = {}
        for k in range(len(allowed)+1):
            for subset in combinations(allowed, k):
                e = 0
                for v in subset:
                    e ^= v
                expected.setdefault(e, k)
                total = 0
                for v in best[e]:
                    assert v in allowed
                    total ^= v
                assert total == e
                cases += 1
        assert {v: len(w) for v, w in best.items()} == expected
    print(f"4 exact direct-sum radii and {cases} permitted-subset replacements passed.")


if __name__ == "__main__":
    check()
