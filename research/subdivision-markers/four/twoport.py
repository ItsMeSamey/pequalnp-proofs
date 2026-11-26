"""Exhaustive two-port replacement checks on generated finite decompositions."""
from collections import deque
from dataclasses import dataclass, field
from itertools import combinations, product
from random import Random


def edge(a, b):
    return tuple(sorted((a, b)))


@dataclass
class Node:
    ports: tuple
    bag: tuple
    own: set = field(default_factory=set)
    children: list = field(default_factory=list)


def table():
    return {(b, q): set() for b in range(4) for q in (0, 1)}


def weight(vertices, labels):
    out = 0
    for v in vertices:
        out ^= labels[v]
    return out


def oracle(vertices, edges, ports, labels):
    vs = sorted(vertices)
    rows = {v: 0 for v in vs}
    pos = {v: j for j, v in enumerate(vs)}
    for a, b in edges:
        rows[a] |= 1 << pos[b]
        rows[b] |= 1 << pos[a]
    out = table()
    u, v = ports
    for selected in range(1 << len(vs)):
        odd = {w for w in vs if (selected >> pos[w]) & 1
               and (selected & rows[w]).bit_count() % 2}
        if odd and odd != {u, v}:
            continue
        b = ((selected >> pos[u]) & 1) + 2 * ((selected >> pos[v]) & 1)
        out[b, int(bool(odd))].add(weight((w for w in vs
            if w not in ports and (selected >> pos[w]) & 1), labels))
    return out


def shortest_alt(edges, ports):
    u, v = ports
    adj = {}
    for a, b in edges - {edge(u, v)}:
        adj.setdefault(a, []).append(b)
        adj.setdefault(b, []).append(a)
    predecessor = {u: None}
    queue = deque([u])
    while queue:
        a = queue.popleft()
        if a == v:
            path = []
            while predecessor[a] != u:
                a = predecessor[a]
                path.append(a)
            return path
        for b in adj.get(a, ()):
            if b not in predecessor:
                predecessor[b] = a
                queue.append(b)
    return None


def verify(node, labels, t, counts):
    vertices = set(node.bag)
    edges = node.own.copy()
    child_data = []
    for child in node.children:
        vs, es, tab = verify(child, labels, t, counts)
        assert vertices & vs == set(child.ports) and edges.isdisjoint(es)
        vertices.update(vs)
        edges.update(es)
        path = shortest_alt(es, child.ports)
        d = int(edge(*child.ports) in es)
        p = None if path is None else weight(path, labels)
        child_data.append((child.ports, d, p, tab))
        counts['interface', d, p is not None] = counts.get(('interface', d, p is not None), 0) + 1

    predicted = table()
    for m in range(1 << len(node.bag)):
        taken = {v for j, v in enumerate(node.bag) if (m >> j) & 1}
        own_label = weight(taken.difference(node.ports), labels)
        # The underlying skeleton is simple: unique physical edges and a fresh
        # degree-two proxy for every child admitting an alternate path.
        skeleton = node.own | {edge(*ports) for ports, d, _, _ in child_data if d}
        for proxies in product(*[(0, 1) if p is not None else (0,)
                                 for _, _, p, _ in child_data]):
            odd = set()
            for a, b in skeleton:
                if a in taken and b in taken:
                    odd.symmetric_difference_update((a, b))
            base = own_label
            corrections = []
            for (ports, d, p, tab), z in zip(child_data, proxies):
                u, v = ports
                b = int(u in taken) + 2 * int(v in taken)
                if z and b in (1, 2):
                    break  # selected proxy would itself have odd degree
                e = int(bool(z and b == 3))
                if e:
                    odd.symmetric_difference_update(ports)
                    base ^= p
                q = (d & int(b == 3)) ^ e
                canonical = p if e else 0
                deltas = {w ^ canonical for w in tab[b, q]}
                assert 0 in deltas
                corrections.append(deltas)
            else:
                if odd and odd != set(node.ports):
                    continue
                # Include only transitions with at most t nonzero corrections.
                reachable = {(0, 0)}
                for choices in corrections:
                    reachable = {(x ^ delta, used + bool(delta))
                                 for x, used in reachable for delta in choices
                                 if used + bool(delta) <= t}
                u, v = node.ports
                b = int(u in taken) + 2 * int(v in taken)
                predicted[b, int(bool(odd))].update(base ^ x for x, _ in reachable)

    expected = oracle(vertices, edges, node.ports, labels)
    assert predicted == expected, (node, labels, expected, predicted)
    counts['tables'] = counts.get('tables', 0) + 1
    return vertices, edges, predicted


def random_tree(rng, nodes):
    root = Node((0, 1), (0, 1, 2))
    choices = [root]
    nxt = 3
    for _ in range(nodes - 1):
        parent = rng.choice(choices)
        ports = tuple(rng.sample(parent.bag, 2))
        new = tuple(range(nxt, nxt + rng.randrange(3)))
        nxt += len(new)
        child = Node(ports, ports + new)
        parent.children.append(child)
        choices.append(child)
    # Give each actual edge exactly one eligible owner, independently of depth.
    candidates = {}
    for node in choices:
        for u, v in combinations(node.bag, 2):
            candidates.setdefault(edge(u, v), []).append(node)
    for pair, owners in candidates.items():
        if rng.random() < .56:
            rng.choice(owners).own.add(pair)
    return root, nxt


if __name__ == '__main__':
    rng = Random(367512)
    counts = {}
    for i in range(350):
        root, n = random_tree(rng, rng.randint(1, 6))
        t = i % 4
        verify(root, [rng.randrange(1 << t) for _ in range(n)], t, counts)

    # Two siblings share exactly both ports; reverse order in the second.
    # Enumerate every graph on the five eligible edges and each eligible
    # ownership of the uv edge (root, either sibling, or absent).
    for owned in range(4):
        for sides in range(16):
            root = Node((0, 1), (0, 1))
            a = Node((0, 1), (0, 1, 2))
            b = Node((1, 0), (1, 0, 3))
            root.children.extend([a, b])
            if owned:
                (root, a, b)[owned - 1].own.add((0, 1))
            for j, (child, pair) in enumerate(((a, (0, 2)), (a, (1, 2)),
                                               (b, (0, 3)), (b, (1, 3)))):
                if (sides >> j) & 1:
                    child.own.add(pair)
            verify(root, [0, 0, 1, 2], 2, counts)
    print(counts)
