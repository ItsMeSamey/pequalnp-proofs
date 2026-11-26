"""Compare edge-conditioned Walsh transfer with direct physical matching enumeration."""
from collections import Counter, defaultdict
from itertools import product
from math import prod
from random import Random


def matchings(edges):
    vertices = {v for pair in edges for v in pair}
    def visit(left, chosen):
        if not left:
            yield chosen
            return
        v = min(left)
        for i, (a, b) in enumerate(edges):
            if v in (a, b) and a in left and b in left:
                yield from visit(left - {a, b}, chosen + (i,))
    return list(visit(vertices, ()))


def verify(blocks, joins, trials=12):
    pairs = []
    ports = set()
    children = defaultdict(list)
    links = defaultdict(set)
    copies = {(i, j) for i, edges in enumerate(blocks) for j in range(len(edges))}
    for i, vi, k, vk, permutation in joins:
        ai = [j for j, edge in enumerate(blocks[i]) if vi in edge]
        ak = [j for j, edge in enumerate(blocks[k]) if vk in edge]
        mapping = dict(zip(ai, [ak[p] for p in permutation], strict=True))
        children[i].append((k, mapping))
        assert (i, vi) not in ports and (k, vk) not in ports
        ports.update(((i, vi), (k, vk)))
        for j, l in mapping.items():
            links[i,j].add((k,l))
            links[k,l].add((i,j))
    owners = {}
    physical = []
    while copies:
        todo = [min(copies)]
        chain = set()
        while todo:
            e = todo.pop()
            if e in chain:
                continue
            chain.add(e)
            todo.extend(links[e])
        copies -= chain
        ends = [(i,v) for i,j in chain for v in blocks[i][j] if (i,v) not in ports]
        assert len(ends) == 2
        owners[min(chain)] = len(physical)
        physical.append(tuple(ends))
    local = [matchings(edges) for edges in blocks]
    full = matchings(physical)
    rng = Random(504)
    for trial in range(trials):
        labels = [rng.randrange(8) for _ in physical]
        weights = [rng.choice([-3,-1,0,1,2]) for _ in physical] if trial else [1]*len(physical)
        expected = Counter()
        for m in full:
            sig = 0
            for j in m:
                sig ^= labels[j]
            expected[sig] += prod(weights[j] for j in m)
        transforms = []
        for h in range(8):
            def solve(i, outgoing=None):
                w = [1]*len(blocks[i])
                for j in range(len(w)):
                    if (i,j) in owners:
                        e = owners[i,j]
                        w[j] = weights[e]*(-1)**((h & labels[e]).bit_count()%2)
                for k, mapping in children[i]:
                    msg = solve(k, set(mapping.values()))
                    for j,l in mapping.items():
                        w[j] *= msg[l]
                sums = Counter()
                for m in local[i]:
                    key = None if outgoing is None else next(j for j in m if j in outgoing)
                    sums[key] += prod(w[j] for j in m)
                return sums
            transforms.append(solve(0)[None])
        for sig in range(8):
            assert sum((-1)**((h&sig).bit_count()%2)*z for h,z in enumerate(transforms)) == 8*expected[sig]
    return len(physical),len(full),trials

if __name__ == '__main__':
    k33 = list(product(range(3), range(3,6)))
    c4 = [(0,1),(1,2),(2,3),(3,0)]
    triple = [(0,1)]*3
    print('C6 via two squares',verify([c4]*2,[(0,0,1,1,(0,1))]))
    print('parallel-edge labeled',verify([triple]*2,[(0,0,1,1,(2,0,1))]))
    for n in range(2,7):
        # Root edge (0,3) borders two children; child-to-child coupling matters.
        tree = [(0,0,1,3,(2,1,0))]
        if n>=3:
            tree.append((0,3,2,0,(1,0,2)))
        tree.extend((i-1,3,i,0,(2,0,1)) for i in range(3,n))
        print('K33 splices',n,verify([k33]*n,tree))
    # Deterministic reproduction of the red-count counterexample.
    physical = [(i,(i+1)%6) for i in range(6)]
    assert [len({0,3}.intersection(m)) for m in matchings(physical)] == [1,1]
