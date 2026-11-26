from itertools import product
from random import Random
from solver import parity, projected, solve


def truth(state, literals):
    return any(parity(state & m) ^ c for m, c in literals)


def reachable(layers):
    states = {0}
    for layer in layers:
        states = {state | sum(options) for state in states
                  for options in product(*([0] + [v for v, lits in opts if truth(state, lits)]
                                           for opts in layer))}
    return states


def check(layers, masks):
    possibilities = reachable(layers)
    values = {tuple(parity(m & state) for m in masks) for state in possibilities}
    for target in product((0, 1), repeat=len(masks)):
        result = solve(layers, list(zip(masks, target)))
        assert (result is not None) == (target in values)
        if result is None:
            continue
        state, choices = result
        assert state in possibilities and tuple(parity(m & state) for m in masks) == target
        recovered = 0
        for chosen, layer in zip(choices, layers, strict=True):
            added = 0
            for j, opts in zip(chosen, layer, strict=True):
                if j != -1:
                    out, lits = opts[j]
                    assert truth(recovered, lits)
                    added |= out
            recovered |= added
        assert recovered == state
    return 1 << len(masks)


if __name__ == '__main__':
    rng = Random(94107)
    queries = 0
    for _ in range(360):
        layers = []
        used = 0
        for level in range(rng.randrange(4)):
            layer = []
            earlier = used
            for i in range(rng.randrange(4)):
                width = rng.randrange(1, 4)
                opts = [(rng.getrandbits(width) << used,
                         [(rng.getrandbits(earlier), rng.randrange(2))
                          for _ in range(rng.randrange(4))])
                        for _ in range(rng.randrange(4))]
                layer.append(opts)
                used += width
            layers.append(layer)
        queries += check(layers, [rng.getrandbits(used) for _ in range(rng.randrange(4))])
    queries += check([[[(1 << i, [(0, 1)])] for i in range(8)]], [1, 2, 4, 8])
    for clauses in [[[(1, 0), (2, 1)], [(1, 1), (3, 0)]], [[], [(1, 1)]], []]:
        covered = set()
        for rows in projected(clauses, force_dense=True):
            covered.update(x for x in range(4) if all(parity(m & x) == rhs for m, rhs in rows))
        assert covered == {x for x in range(4) if all(truth(x, lits) for lits in clauses)}
    print(f"361 layered instances, {queries} marker targets, and forced dense projection passed")
