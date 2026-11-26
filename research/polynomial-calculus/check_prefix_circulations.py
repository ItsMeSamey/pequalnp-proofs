"""Verify prefix guard models, affine exports and odd-cycle witnesses."""
from collections import deque
from itertools import product
from random import Random


def reachable(n, heads, tails):
    reach = [1 << i for i in range(n)]
    for h, group in zip(heads, tails):
        for v in group:
            reach[h] |= 1 << v
    for i in range(n):
        for h in range(n):
            if reach[h] >> i & 1:
                reach[h] |= reach[i]
    return reach


def classify(n, heads, tails):
    reach = reachable(n, heads, tails)
    active = []
    for e, (h, group) in enumerate(zip(heads, tails)):
        inside = [v for v in group if reach[v] >> h & 1]
        if inside:
            if len(group) != 1:
                return None
            active.append((e, h, inside[0]))
    return active


def odd_cycle(n, active, marker):
    adjacency = [[] for _ in range(n)]
    for e, h, v in active:
        adjacency[h].append((e, v))
    for root in range(n):
        start, end = (root, 0), (root, 1)
        previous = {start: None}
        pending = deque([start])
        while pending and end not in previous:
            state = pending.popleft()
            v, parity = state
            for e, w in adjacency[v]:
                after = (w, parity ^ (marker >> e & 1))
                if after not in previous:
                    previous[after] = (state, e)
                    pending.append(after)
        if end not in previous:
            continue
        edges, state = [], end
        while state != start:
            state, e = previous[state]
            edges.append(e)
        # Split the directed walk into simple cycles as vertices repeat.
        vertices, path, positions = [root], [], {root: 0}
        for e in reversed(edges):
            v = next(w for f, w in adjacency[vertices[-1]] if f == e)
            if v in positions:
                i = positions[v]
                cycle = sum(1 << f for f in path[i:] + [e])
                if (marker & cycle).bit_count() % 2:
                    return cycle
                for w in vertices[i + 1:]:
                    del positions[w]
                del vertices[i + 1:]
                del path[i:]
            else:
                positions[v] = len(vertices)
                vertices.append(v)
                path.append(e)
        raise AssertionError('Odd walk had only even cycles')
    return None


def check(n, heads, tails):
    active = classify(n, heads, tails)
    if active is None:
        return 0
    m = len(heads)
    starts = [sum(1 << e for e, group in enumerate(tails) if v in group)
              for v in range(n)]
    prefixes = starts[:]
    rows = []
    for e, h in enumerate(heads):
        rows.append(prefixes[h])
        prefixes[h] ^= 1 << e
    models = set()
    allowed = sum(1 << e for e, _, _ in active)
    span = set()
    for x in range(1 << m):
        genuine = all(not (x >> e & 1) or (x & a).bit_count() % 2
                      for e, a in enumerate(rows))
        enters = [0] * n
        exits = [0] * n
        for e, h, v in active:
            if x >> e & 1:
                exits[h] += 1
                enters[v] += 1
        cyclic = not (x & ~allowed) and enters == exits and max(exits) <= 1
        assert genuine == cyclic
        if genuine:
            models.add(x)
        if not x & ~allowed and all(not (x & q).bit_count() % 2 for q in prefixes):
            span.add(x)
    generated = {0}
    for x in models:
        generated |= {y ^ x for y in generated}
    assert span == generated
    for ell in range(1 << m):
        witness = odd_cycle(n, active, ell)
        assert (witness is not None) == any((x & ell).bit_count() % 2 for x in models)
        if witness is not None:
            assert witness in models and (witness & ell).bit_count() % 2
    return 1


def main():
    pairs = [(h, tuple(v for v in range(2) if mask >> v & 1))
             for h in range(2) for mask in range(4)]
    total = checked = 0
    for seq in product(pairs, repeat=3):
        heads, tails = zip(*seq)
        checked += check(2, heads, tails)
        total += 1
    rng = Random(516)
    for _ in range(360):
        n = rng.randint(3, 5)
        m = rng.randint(3, 8)
        heads = [rng.randrange(n) for _ in range(m)]
        tails = [tuple(sorted(rng.sample(range(n), rng.choice([0, 1, 1, 1, 2]))))
                 for _ in heads]
        checked += check(n, heads, tails)
        total += 1
    print(f'{total} presentations checked; {checked} met the potential criterion. '
          'Every model, exported kernel and marker answer agreed.')


if __name__ == '__main__':
    main()
