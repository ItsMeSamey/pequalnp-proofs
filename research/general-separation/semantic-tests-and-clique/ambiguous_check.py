from itertools import product
from random import Random

rng = Random(16072026)
instances = restrictions = evaluations = 0
for sample in range(30):
    q = 6
    reject, accept = q, q + 1
    labels = [rng.randrange(3) for _ in range(q)]
    edges = [[{j for j in range(i + 1, q + 2) if rng.randrange(3) == 0}
              for b in range(2)] for i in range(q)]
    instances += 1
    for pins in product((None, 0, 1), repeat=3):
        restrictions += 1
        stop = {reject: {reject}, accept: {accept}}
        residual = {}
        for i in reversed(range(q)):
            targets = [set().union(*(stop[j] for j in edges[i][b])) for b in range(2)]
            if pins[labels[i]] is None:
                residual[i] = targets
                stop[i] = {i}
            else:
                stop[i] = targets[pins[labels[i]]]
        nodes = list(residual)
        for loose in product((0, 1), repeat=pins.count(None)):
            it = iter(loose)
            x = [next(it) if bit is None else bit for bit in pins]
            truth = {reject: 0, accept: 1}
            for i in reversed(range(q)):
                truth[i] = any(truth[j] for j in edges[i][x[labels[i]]])
            valid_extensions = 0
            for f in product((0, 1), repeat=len(nodes)):
                value = {reject: 0, accept: 1, **dict(zip(nodes, f))}
                good = True
                for i, pair in residual.items():
                    for b, targets in enumerate(pair):
                        selected = x[labels[i]] == b
                        good &= all(not selected or not value[j] or value[i]
                                    for j in targets)
                        good &= not selected or not value[i] or any(value[j] for j in targets)
                if good:
                    valid_extensions += 1
                    assert any(value[j] for j in stop[0]) == truth[0]
            assert valid_extensions == 1
            evaluations += 1
print(instances, "programs,", restrictions, "restrictions,", evaluations, "assignments")
