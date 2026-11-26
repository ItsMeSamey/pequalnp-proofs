"""Check every distinct ordered pair of K5,5 internal pins at a fixed port."""
from itertools import permutations, product
edges = list(product(range(5), range(5, 10)))
port = edges[0]
cuts = [{e for e in edges if ((s >> e[0]) ^ (s >> e[1])) & 1} for s in range(512)]
count = 0
for i, j in permutations(edges[1:], 2):
    for pc, pd in [(0, 0), (0, 1), (1, 0)]:
        busy = set(port + i + j)
        cycle = set()
        for a, b in ([i, port] if pc else [i]):
            x = next(v for v in range(5) if v not in busy)
            y = next(v for v in range(5, 10) if v not in busy)
            busy.update([x, y])
            cycle.update([(a, b), (a, y), (x, b), (x, y)])
        assert all(sum(v in edge for edge in cycle) % 2 == 0 for v in range(10))
        assert i in cycle and (port in cycle) == bool(pc)
        assert any(j in d and (port in d) == bool(pd) and not cycle & d for d in cuts)
        count += 1
print(count, "ordered pin and port cases verified")
