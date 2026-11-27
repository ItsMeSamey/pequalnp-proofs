"""Seeded direct-observation wedge check for scalar and read-once observables."""
from collections import Counter, defaultdict
from hashlib import sha256
from itertools import combinations
from random import Random


def audit(n, gates, ports, formula, promise):
    # Aggregator nodes use port-occurrence indices followed by earlier nodes.
    # Invalid original taps must stay false even after adding aggregator gates.
    wires = list(gates)
    limit = n + len(wires)
    translated = [p if p < limit else -1 for p in ports]
    for op, args in formula:
        wires.append((op, tuple(translated[a] for a in args)))
        translated.append(n + len(wires) - 1)
    root = translated[-1]
    domain = 1 << n
    mask = (1 << domain) - 1
    values = [sum(1 << x for x in range(domain) if x & (1 << k))
              for k in range(n)]
    parents = {}
    for i, (op, args) in enumerate(wires, n):
        pins = args[:1] if op == 'N' else args
        parents[i] = [a for a in pins if 0 <= a < i]
        bits = [values[a] if 0 <= a < i else 0 for a in pins]
        if op == 'N':
            value = mask ^ (bits[0] if bits else 0)
        elif op == 'A':
            value = mask
            for bit in bits:
                value &= bit
        else:
            value = 0
            for bit in bits:
                value |= bit
        values.append(value)

    uses = defaultdict(list)
    stack = [(root, -1)] if root >= 0 else []
    while stack:
        producer, user = stack.pop()
        if producer not in uses:
            stack.extend((p, producer) for p in parents.get(producer, ()))
        uses[producer].append(user)
    colors = []
    for donor in range(n):
        wire = donor
        while len(uses.get(wire, ())) == 1:
            wire = uses[wire][0]
        colors.append(wire if wire in uses else -1)

    output = values[root] if root >= 0 else 0
    edges = []
    for a, b in combinations(range(n), 2):
        centers = set()
        for x in range(domain):
            neighbors = (x, x ^ (1 << a), x ^ (1 << b))
            if any(not (promise >> v & 1) for v in neighbors):
                continue
            center, left, right = (output >> v & 1 for v in neighbors)
            if center != left and center != right:
                centers.add(((x >> a) & 1, (x >> b) & 1))
        if len(centers) >= 2:
            if colors[a] == colors[b]:
                raise AssertionError((n, gates, ports, formula, promise, a, b, centers, colors))
            edges.append((a, b))
    return colors, edges, output


def aggregate(rng, count):
    nodes = list(range(count))
    formula = []
    while len(nodes) > 1:
        rng.shuffle(nodes)
        a = nodes.pop()
        if rng.randrange(3) == 0:
            formula.append(('N', (a,)))
            a = count + len(formula) - 1
        formula.append((rng.choice('AO'), (a, nodes.pop())))
        nodes.append(count + len(formula) - 1)
    if rng.randrange(2):
        formula.append(('N', (nodes.pop(),)))
    return formula


def main():
    rng = Random(2057953)
    digest = sha256()
    stats = Counter()
    majority = [('A', (0, 1)), ('O', (0, 1)), ('A', (4, 2)), ('O', (3, 5))]
    for trial in range(1601):
        n = rng.randrange(3, 6)
        gates = []
        for i in range(n, n + rng.randrange(2, 14)):
            pins = tuple(rng.randrange(i + 3) for _ in range(rng.choice((0, 1, 2, 2, 2))))
            gates.append((rng.choice('AON'), pins))
        ports = [rng.randrange(n + len(gates) + 2) for _ in range(rng.randrange(1, 5))]
        if trial % 8 == 0:
            n, gates, ports = 3, majority, [6]
        formula = aggregate(rng, len(ports))
        promise = sum(1 << x for x in range(1 << n) if rng.randrange(5))
        if trial == 0:
            # Omit 000 and 111. The six promised cells still witness all three edges.
            promise, formula = 0x7e, []
        colors, edges, output = audit(n, gates, ports, formula, promise)
        if trial == 0 and edges != [(0, 1), (0, 2), (1, 2)]:
            raise AssertionError(edges)
        stats['circuits'] += 1
        stats['with_edges'] += bool(edges)
        stats['edges'] += len(edges)
        stats['partial_promises'] += promise != (1 << (1 << n)) - 1
        stats['aggregated'] += bool(formula)
        digest.update(repr((n, gates, ports, formula, promise, colors, edges, output)).encode() + b'\n')
    print(dict(stats), digest.hexdigest())


if __name__ == '__main__':
    main()
