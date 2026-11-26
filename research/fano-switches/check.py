"""Enumerate exactly the alternating graph changes preserving three marked guards."""
from itertools import product
from pathlib import Path
import importlib.util
from random import Random

spec = importlib.util.spec_from_file_location("two_markers", Path(__file__).resolve().parents[1] / "two-markers/check.py")
two = importlib.util.module_from_spec(spec)
spec.loader.exec_module(two)


def dot(a, b):
    return (a & b).bit_count() % 2


def image(columns, support):
    value = 0
    for i, column in enumerate(columns):
        if support >> i & 1:
            value ^= column
    return value


def switches(labels, z):
    for code in range(64):
        k = [0, 0, 0]
        bit = 0
        for i in range(3):
            for j in range(i, 3):
                if code >> bit & 1:
                    k[i] |= 1 << j
                    k[j] |= 1 << i
                bit += 1
        if any(dot(row, z) != (row >> i & 1) for i,row in enumerate(k)):
            continue
        yield tuple(sum(dot(image(k, v), w) << j for j,w in enumerate(labels) if j != i)
                    for i,v in enumerate(labels))


def components(adj):
    remaining = (1 << len(adj)) - 1
    while remaining:
        start = remaining & -remaining
        stack = start
        group = 0
        while stack:
            bit = stack & -stack
            group |= bit
            stack = (stack ^ bit) | (adj[bit.bit_length()-1] & ~group)
        remaining ^= group
        yield [i for i in range(len(adj)) if group >> i & 1]


def solve(adj, labels, z):
    """(recognized, witness). A recognized no-instance has witness None."""
    for change in switches(labels,z):
        graph = [a ^ b for a,b in zip(adj,change)]
        states = {0:0}
        for group in components(graph):
            coords = {0:0}
            for i in group:
                c = labels[i]
                if c not in coords:
                    coords.update({a^c: len(coords) + v for a,v in coords.items()})
            if len(coords)>4:
                break
            local = [sum(((graph[i] >> j) & 1) << h for h,j in enumerate(group)) for i in group]
            options = {}
            for value, code in coords.items():
                support = two.witness(local, [coords[labels[i]] for i in group], code)
                if support is not None:
                    options[value] = sum(((support >> h) & 1) << j for h,j in enumerate(group))
            states = {a^b: x|y for a,x in states.items() for b,y in options.items()}
        else:
            return True, states.get(z)
    return False, None


def preserves(d, fiber):
    return all(not any((x>>i&1) and dot(x,row) for i,row in enumerate(d)) for x in fiber)


if __name__ == '__main__':
    checked = 0
    for labels in product(range(8), repeat=3):
        values = [image(labels,x) for x in range(8)]
        if len(set(values)) < 8:
            continue
        # Full-rank square has a singleton fiber; all coordinates must be active.
        z = values[7]
        all_graphs = [tuple(two.graph(3,k)) for k in range(8)]
        assert set(switches(labels,z)) == {d for d in all_graphs if preserves(d,[7])}
        checked += 1
    rng = Random(81927)
    for _ in range(200):
        n = 4
        labels = [rng.randrange(8) for i in range(n)]
        z = rng.randrange(1,8)
        values = [image(labels,x) for x in range(1<<n)]
        fiber = [x for x,y in enumerate(values) if y==z]
        if len(set(values))<8 or any(not any(x>>i&1 for x in fiber) for i in range(n)):
            continue
        graphs = [tuple(two.graph(n,k)) for k in range(1<<(n*(n-1)//2))]
        assert set(switches(labels,z)) == {d for d in graphs if preserves(d,fiber)}
        checked += 1
    recognized = 0
    for _ in range(250):
        n = rng.randrange(1,10)
        labels=[rng.randrange(8) for i in range(n)]
        graph=two.graph(n,rng.getrandbits(n*(n-1)//2))
        z=rng.randrange(8)
        ok,x=solve(graph,labels,z)
        if ok:
            sols=[y for y in range(1<<n) if image(labels,y)==z and preserves(graph,[y])]
            assert (x in sols) if sols else (x is None)
            recognized+=1
    print(checked,"complete switch comparisons;",recognized,"recognized solver cases")
