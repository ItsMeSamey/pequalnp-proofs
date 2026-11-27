from functools import partial
from itertools import product
from random import Random
import sys
from check_first_space import image, span
from graphic import is_graphic_cmr
from paired_space import paired_space, wedge


def check(keys, tags, graphic):
    n = len(keys)
    active = [sum(1 << i for i in range(n) if image(keys[i], chart) == tags[i])
              for chart in product(range(4), repeat=2)]
    feasible = set()
    for sites in active:
        local = [u for u in range(1 << n) if u & ~sites == 0 and image(u, keys) == 0]
        feasible.update(wedge(u, v, n) for u in local for v in local)
    records = paired_space(keys, tags, graphic=graphic)
    for w, u, v, sites in records:
        support = sum(1 << i for i in sites)
        assert not (u | v) & ~support
        assert any(support & ~a == 0 for a in active)
        assert image(u, keys) == image(v, keys) == 0
        assert w == wedge(u, v, n)
    actual = span([w for w, *_ in records])
    assert actual == span(feasible) and len(actual) == 1 << len(records)
    return len(records)


if __name__ == "__main__":
    cmr = partial(is_graphic_cmr, executable=sys.argv[1])
    rng = Random(37896)
    dims = [check([1,1,1,1], ts, cmr) for ts in ([0,0,1,1], [0,0,0,0])]
    for _ in range(10):
        n = rng.randrange(2, 6)
        dims.append(check([rng.randrange(4) for _ in range(n)],
                          [rng.randrange(4) for _ in range(n)], cmr))
    print("12 W bases and original-index co-chart witnesses verified; dimensions", dims)
