from itertools import product
from random import Random

rng = Random(19190101)
tests = 0
for sample in range(80):
    count = 10
    nodes = [(rng.randrange(4), rng.randrange(i + 1, count + 2),
              rng.randrange(i + 1, count + 2)) for i in range(count)]
    for fixed in product((0, 1, None), repeat=4):
        representative = [None] * count + [count, count + 1]
        residual = {}
        for i in reversed(range(count)):
            var, low, high = nodes[i]
            if fixed[var] is None:
                representative[i] = i
                residual[i] = var, representative[low], representative[high]
            else:
                representative[i] = representative[(low, high)[fixed[var]]]
        for vector in product((0, 1), repeat=fixed.count(None)):
            live = iter(vector)
            x = [next(live) if bit is None else bit for bit in fixed]
            i = 0
            while i < count:
                var, low, high = nodes[i]
                i = (low, high)[x[var]]
            value = {count: 0, count + 1: 1}
            for node, (var, low, high) in residual.items():
                value[node] = value[(low, high)[x[var]]]
            assert value[representative[0]] == i - count
            tests += 1
print(tests, "assignment checks passed")
