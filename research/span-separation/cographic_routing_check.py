"""Differential checks of dense-label routing using only Python's standard library."""
from itertools import product
from random import Random


def xor(values):
    answer = 0
    for value in values:
        answer ^= value
    return answer


def span(vectors):
    sums = {0}
    for v in vectors:
        sums |= {s ^ v for s in sums}
    return sums


def components_connected(part, adjacency):
    if not part:
        return False
    reached = 0
    todo = part & -part
    while todo:
        bit = todo & -todo
        reached |= bit
        todo = (todo ^ bit) | (adjacency[bit.bit_length() - 1] & part & ~reached)
    return reached == part


def part_sums(assignment, labels, b):
    sums = [0] * b
    for group, label in zip(assignment, labels):
        sums[group] ^= label
    return tuple(sums)


def connected(assignment, adjacency, b):
    parts = [0] * b
    for i, group in enumerate(assignment):
        parts[group] |= 1 << i
    return all(components_connected(part, adjacency) for part in parts)


def make_instance(rng, b, s):
    # W has dimension three. Choose a possibly proper, non-coordinate subspace S.
    space_basis = []
    while len(space_basis) < s:
        v = rng.randrange(1, 8)
        if v not in span(space_basis):
            space_basis.append(v)
    subspace = span(space_basis)
    core_sizes = [1 + (rng.random() < .35) for _ in range(b)]
    # Small dimensions keep exhaustive ordered partition enumeration tractable.
    n = min(10, sum(core_sizes) + (b - 1) * s + rng.randint(1, 2))
    if n <= sum(core_sizes) + (b - 1) * s:
        core_sizes = [1] * b
        n = sum(core_sizes) + (b - 1) * s + 1
    order = list(range(n))
    rng.shuffle(order)
    labels = [0] * n
    cores = []
    for size in core_sizes:
        core = [order.pop() for _ in range(size)]
        cores.append(core)
        for v in core:
            labels[v] = rng.choice(sorted(subspace))
    bases = []
    for _ in range(b - 1):
        basis = [order.pop() for _ in range(s)]
        chosen = []
        for v in basis:
            labels[v] = rng.choice(sorted(subspace - span(chosen)))
            chosen.append(labels[v])
        bases.append(basis)
    for v in order[:-1]:
        labels[v] = rng.randrange(8)
    labels[order[-1]] = xor(labels)
    assert xor(labels) == 0

    adjacency = [0] * n

    def edge(i, j):
        if i != j:
            adjacency[i] |= 1 << j
            adjacency[j] |= 1 << i

    for i, core in enumerate(cores):
        for a, c in zip(core, core[1:]):
            edge(a, c)
        for v in range(n):
            if v not in core:
                edge(v, rng.choice(core))
    for i in range(n):
        for j in range(i):
            if rng.random() < .15:
                edge(i, j)
    return adjacency, labels, cores, bases, subspace


def rectify(initial, labels, cores, bases):
    b = len(cores)
    target = part_sums(initial, labels, b)
    a = list(initial)
    for i, core in enumerate(cores):
        for v in core:
            a[v] = i
    for basis in bases:
        for v in basis:
            a[v] = b - 1
    for i, basis in enumerate(bases):
        delta = target[i] ^ part_sums(a, labels, b)[i]
        selected = next(bits for bits in range(1 << len(basis))
                        if xor(labels[v] for j, v in enumerate(basis) if bits >> j & 1) == delta)
        for j, v in enumerate(basis):
            if selected >> j & 1:
                a[v] = i
    assert part_sums(a, labels, b) == target
    return a


def test(rng, b, s):
    adjacency, labels, cores, bases, subspace = make_instance(rng, b, s)
    # Independently compute the unrestricted table and all connected outcomes.
    table = {(0,) * b}
    for label in labels:
        table = {old[:i] + (old[i] ^ label,) + old[i + 1:] for old in table for i in range(b)}
    connected_sums = set()
    representatives = {}
    for assignment in product(range(b), repeat=len(labels)):
        target = part_sums(assignment, labels, b)
        representatives.setdefault(target, assignment)
        if connected(assignment, adjacency, b):
            connected_sums.add(target)
    assert connected_sums == table == set(representatives)
    for a in representatives.values():
        fixed = rectify(a, labels, cores, bases)
        assert connected(fixed, adjacency, b)
    if all(v in subspace for v in labels):
        assert len(table) == len(subspace) ** (b - 1)
    return len(table)


if __name__ == "__main__":
    rng = Random(494)
    cases = 0
    tested = 0
    for b in (2, 3):
        for s in range(3):
            for _ in range(12):
                tested += test(rng, b, s)
                cases += 1
    print(f"{cases} labelled graphs; {tested} ordered sum outcomes checked.")
