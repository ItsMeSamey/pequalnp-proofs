"""Constructive reference for the unknown-plane prefix recognition theorem."""
from collections import Counter
from itertools import combinations, product
from random import Random

from symbolic_planes import plan


def echelon(rows):
    pivots = {}
    basis = []
    for v in rows:
        value, coords = reduce_row(v, pivots)
        if value:
            pivots[value.bit_length()-1] = value, coords ^ (1 << len(basis))
            basis.append(v)
    return basis, pivots


def reduce_row(v, pivots):
    mask = 0
    for j in sorted(pivots, reverse=True):
        if v >> j & 1:
            row, coords = pivots[j]
            v ^= row
            mask ^= coords
    return v, mask


def span(rows):
    space = {0}
    for v in rows:
        space |= {z ^ v for z in space}
    return space


def proposals(blocks, k, stats=None):
    prefix = []
    seen = set()
    for rows in blocks:
        basis, _ = echelon(rows)
        if len(basis) >= 3:
            return span(basis[:3]) - {0} if k else set()
        block = frozenset(span(basis) - {0})
        if not block or block in seen:
            continue
        if plan([*prefix, block], []) is None:
            break
        prefix.append(block)
        seen.add(block)
    else:
        return None
    if not k:
        return set()
    old, _ = plan(prefix, [])
    planes = [p for p in prefix if len(p) == 3]
    fixed = set().union(*(p for p in prefix if len(p) == 1))
    witness = {}
    for a, b in combinations(planes, 2):
        for v in a & b:
            if v not in fixed:
                witness[v] = (a, b)
    forced = fixed | witness.keys()
    owners = {v: p for p in planes for v in p if v in old and v not in forced}
    _, piv = echelon(old)
    xs = []
    active = set()
    for v in block:
        remainder, mask = reduce_row(v, piv)
        if remainder:
            continue
        xs.append(v)
        used = {owners[v] for j, v in enumerate(old) if mask >> j & 1 and v in owners}
        if len(used) > 2*k+2:
            return set()
        active.update(used)
    active = list(active)
    fixed_rows = [v for v in old if owners.get(v) not in active]
    menus = [list(combinations(p-forced, 2-len(p & forced))) for p in active]
    proposed = set()
    for choices in product(*menus):
        axes = fixed_rows + [v for chosen in choices for v in chosen]
        _, piv = echelon(axes)
        assert len(piv) == len(old)
        supports = []
        for x in xs:
            remainder, mask = reduce_row(x, piv)
            assert not remainder
            supports.append([v for j, v in enumerate(axes) if mask >> j & 1])
        large = next((s for s in supports if len(s) > 4*k+4), None)
        if large:
            counts = Counter()
            for v in large:
                if v in witness:
                    a,b = witness[v]
                    counts.update(span(a|b)-{0})
            heavy = {v for v,c in counts.items() if c*2*((1<<k)-1) >= len(large)}
            proposed.update(heavy)
            if stats is not None:
                stats['large'] += 1
        else:
            local = set(block)
            for support in supports:
                for v in support:
                    local.add(v)
                    if v in witness:
                        a,b = witness[v]
                        local.update(a|b)
            proposed.update(span(local)-{0})
            if stats is not None:
                stats['small'] += 1
    return proposed


def find(blocks, k, stats=None):
    directions = proposals(blocks, k, stats)
    if directions is None:
        return []
    for u in sorted(directions):
        high = u.bit_length()-1
        image = [[v ^ u if v >> high & 1 else v for v in block] for block in blocks]
        result = find(image, k-1, stats)
        if result is not None:
            return [u, *result]
    return None


def check():
    rng = Random(833091)
    stats = Counter()
    yes = no = 0
    for _ in range(210):
        r = rng.randrange(2,6)
        k = rng.randrange(3)
        blocks = [[rng.randrange(1 << r) for _ in range(rng.randrange(1,4))]
                  for _ in range(rng.randrange(1,8))]
        got = find(blocks, k, stats)
        expected = any(plan(blocks, U) is not None for j in range(k+1)
                       for U in combinations(range(1, 1 << r), j))
        assert (got is not None) == expected, (blocks,k,got,expected)
        if expected:
            assert plan(blocks, got) is not None
            yes += 1
        else:
            no += 1

    # The long singleton circuit has no two-plane witnesses.
    blocks = [[1 << i] for i in range(10)] + [[(1 << 10)-1]]
    assert find(blocks, 1, stats) is None
    # Ten forced directions, each with the same two neighbor axes: all three
    # nonzero vectors in their neighbor plane pass the heavy threshold.
    a, b = 1 << 10, 1 << 11
    axes = [1 << i for i in range(10)]
    blocks = [[p, f] for f in axes for p in (a,b)] + [[sum(axes)]]
    assert proposals(blocks, 1, stats) == {a, b, a ^ b}
    assert find(blocks, 1, stats) is None
    assert stats['small'] and stats['large']
    print(yes, 'YES', no, 'NO;', dict(stats))


if __name__ == '__main__':
    check()
