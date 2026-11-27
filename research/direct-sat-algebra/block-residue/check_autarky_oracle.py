"""Compare the block peel to quantified original-bit semantics."""
from itertools import product
from random import Random
from autarky_block import comparison_autarky, raw_autarky


def holds(word, edge):
    u, v, required = edge
    return word[u] ^ word[v] == required


def permuted_pairs(groups, pairs):
    tagged = [(i, edge) for i, group in enumerate(groups) for edge in group]
    order = [k for pair in pairs for k in pair]
    assert sorted(order) == list(range(len(tagged)))
    return [tagged[k][1] for k in order], [tagged[k][0] for k in order]


def largest_oracle(vertices, edges, ids, eligible):
    truths = [tuple(holds(word, edge) for edge in edges)
              for word in product(range(2), repeat=vertices)]
    possible = []
    for flags in product(range(2), repeat=len(eligible)):
        chosen = {block for block, flag in zip(eligible, flags) if flag}
        inside = [block in chosen for block in ids]
        if any(all(not (inside[i] or inside[i+1]) or
                   (inside[i] and row[i]) or (inside[i+1] and row[i+1])
                   for i in range(0, len(edges), 2)) for row in truths):
            possible.append(chosen)
    largest = set().union(*possible)
    assert largest in possible
    return {i for i, block in enumerate(ids) if block in largest}


def inspect(n, edges, peeled):
    plan = comparison_autarky(n, edges)
    assert {i for i, flag in enumerate(plan._peeled) if flag} == peeled
    keep = tuple(i//2 for i in range(0, len(edges), 2)
                 if not ({i, i+1} & peeled))
    assert tuple(plan.residual_shells) == keep
    assert list(plan.residual_comparisons) == [edges[2*s+j] for s in keep for j in (0, 1)]
    return plan


def all_shells(word, edges):
    return all(holds(word, edges[i]) or holds(word, edges[i+1])
               for i in range(0, len(edges), 2))


def tiny_cases():
    groups = [[(0, 0, 1)], [(0, 1, 0), (0, 1, 1)], [(0, 2, 1)],
              [(0, 3, 0), (0, 3, 1), (0, 3, 1)],
              [(0, 4, 0), (4, 5, 1), (5, 0, 1)]]
    rng = Random(230197)
    for trial in range(50):
        order = list(range(10))
        if trial:
            rng.shuffle(order)
        edges, ids = permuted_pairs(groups, zip(order[::2], order[1::2]))
        yield 6, edges, largest_oracle(6, edges, ids, [0, 1, 2, 4])
    groups = [[(0, 0, 1)], [(0, 1, 0), (0, 1, 1)],
              [(0, 2, 0), (0, 2, 1), (0, 2, 0)]]
    edges, ids = permuted_pairs(groups, [(0, 1), (2, 3), (4, 5)])
    yield 3, edges, largest_oracle(3, edges, ids, [0, 1])


def check_articulations(size):
    groups = [[(i, (i+1) % size, 0) for i in range(size)]]
    groups += [[(i, size+i, sign) for sign in (0, 1, 1)] for i in range(size)]
    pairs = [(i, size+3*i) for i in range(size)]
    pairs += [(size+3*i+1, size+3*((i+1) % size)+2) for i in range(size)]
    edges, ids = permuted_pairs(groups, pairs)
    plan = inspect(2*size, edges, {i for i, block in enumerate(ids) if block == 0})
    alternating = [i % 2 for i in range(size)]
    residual = alternating + [1-bit for bit in alternating]
    assert all_shells(residual, plan.residual_comparisons)
    assert not all_shells(residual, edges)
    assert all_shells(plan.lift(residual), edges)


def main():
    for n, edges, expected in tiny_cases():
        plan = inspect(n, edges, expected)
        for word in product(range(2), repeat=n):
            if all_shells(word, plan.residual_comparisons):
                assert all_shells(plan.lift(word), edges)
    check_articulations(2048)
    assert raw_autarky(1, [(0, 1, 1), (1, 0, 0)]) is None
    pins = [(0, 2, 1), (1, 3, 0)]
    plan = raw_autarky(1, pins)
    word = plan.lift()
    assert all(holds(word, pin) for pin in pins)
    assert (word[0], word[1]) != (word[2], word[3])
    print("51 quantified subset oracles, 2048 articulations, signed pin lifts")


if __name__ == '__main__':
    main()
