"""Bounded exhaustive partition controls using an independent GF(2) rank."""
from random import Random
from separations import find_separation, minimum_rooted_separation


def rank(columns, side):
    span = {0}
    for i in side:
        span |= {columns[i] ^ x for x in span}
    return len(span).bit_length() - 1


def check():
    rng = Random(44109)
    for case in range(600):
        n = rng.randrange(6, 13)
        d = rng.randrange(1, 8)
        cols = [rng.getrandbits(d) for _ in range(n)]
        ground = set(range(n))
        full = rank(cols, ground)
        roots = set(rng.sample(range(n), 6))
        for vertical in (False, True):
            left = roots if vertical else set(rng.sample(range(n), 2))
            right = set() if vertical else {rng.choice(sorted(ground-left))}
            free = sorted(ground-left-right)
            best = None
            for mask in range(1 << len(free)):
                x = left.union(i for j,i in enumerate(free) if mask >> j & 1)
                a, b = rank(cols, x), rank(cols, ground-x)
                val = a+b-full
                if vertical and (min(a,b) <= val or val > 2):
                    continue
                best = val if best is None else min(best,val)
            if vertical:
                answer = find_separation(cols, roots)
                if answer is None:
                    assert best is None
                    continue
                x,y = answer
            else:
                reported,x,y = minimum_rooted_separation(cols,left,right)
                assert reported == best
            assert left <= x and right <= y and x|y == ground and not x&y
            a,b = rank(cols,x),rank(cols,y)
            assert a+b-full == best and (not vertical or min(a,b)>best)
    print("600 forced and 600 vertical minimum-partition checks passed")


if __name__ == '__main__':
    check()
