"""Evaluate the compiled block equations on every rooted cut of each allowed cover."""
from itertools import permutations
from random import Random


def split_nodes(arcs):
    if len(arcs) < 2:
        return
    mid = len(arcs)//2
    left, right = arcs[:mid], arcs[mid:]
    yield set(left), set(right)
    yield from split_nodes(left)
    yield from split_nodes(right)


def blocks_for_graph(edges, size):
    orders = (sorted(edges), sorted(edges, key=lambda e: (e[1],e[0])))
    for left, right in split_nodes(orders[0]):
        for order in orders:
            items = [e for e in order if e in left or e in right]
            yield [(items[i:i+size], left, right) for i in range(0,len(items),size)]


def parity(block_lists, selected):
    total = 0
    for blocks in block_lists:
        prefix = 0
        for items, left, right in blocks:
            left_selected = [p for p,e in enumerate(items) if e in left and e in selected]
            right_selected = [p for p,e in enumerate(items) if e in right and e in selected]
            inside = sum(j<i for i in left_selected for j in right_selected)
            total ^= (prefix * len(left_selected) + inside) % 2
            prefix ^= len(right_selected) % 2
    return total


def verify(n, edges, size):
    blocks = list(blocks_for_graph(edges, size))
    signed = expected = 0
    for p in permutations(range(n)):
        if any((i,p[i]) not in edges for i in range(n)):
            continue
        visited, i = set(), 0
        while i not in visited:
            visited.add(i)
            i = p[i]
        expected += len(visited)==n
        cover_sum = 0
        for bits in range(0,1<<n,2):
            if any(((bits>>i)^(bits>>p[i]))&1 for i in range(n)):
                continue
            right = [(i,p[i]) for i in range(n) if (bits>>i)&1]
            sign = parity(blocks, set(right))
            assert sign == sum(a[1]>b[1] for t,a in enumerate(right) for b in right[t+1:])%2
            cover_sum += (-1)**((len(right)+sign)%2)
        assert cover_sum == int(len(visited)==n)
        signed += cover_sum
    assert signed == expected


if __name__ == "__main__":
    rng = Random(67811)
    trials = 0
    for n in (1,2,3):
        all_edges = [(i,j) for i in range(n) for j in range(n)]
        for mask in range(1<<len(all_edges)):
            verify(n,{e for i,e in enumerate(all_edges) if mask>>i&1},1+rng.randrange(4))
            trials += 1
    for n in (4,5,6):
        for _ in range(30):
            edges = {(i,j) for i in range(n) for j in range(n) if rng.randrange(3)}
            verify(n,edges,1+rng.randrange(5))
            trials += 1
    print(f"{trials} directed graphs passed, including every loop-allowed graph through 3 vertices")
