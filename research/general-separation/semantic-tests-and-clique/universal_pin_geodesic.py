"""Universal-pin witness search via distance layers of the complementary remainder."""

from collections import deque
from itertools import combinations


def bits(mask):
    while mask:
        bit = mask & -mask
        yield bit.bit_length() - 1
        mask ^= bit


def native_witness(rows, pins, selected):
    return all(selected >> v & 1 for v in pins) and all(
        (rows[v] & selected).bit_count() % 2 == 0 for v in bits(selected)
    )


def solve(rows, hub, p, q):
    """Return an original selected-site mask, or None; rows are simple adjacency masks."""
    n = len(rows)
    universe = (1 << n) - 1
    if len({hub, p, q}) != 3 or any(v < 0 or v >= n for v in (hub, p, q)):
        raise ValueError("three distinct in-range named vertices required")
    if rows[hub] != universe ^ (1 << hub):
        raise ValueError("named hub must be universal")
    remainder = universe ^ (1 << hub)
    adj = [remainder & ~row & ~(1 << i) if i != hub else 0 for i, row in enumerate(rows)]
    pair = (1 << p) | (1 << q)
    if not (adj[p] >> q & 1):
        return pair | (1 << hub)

    adj[p] ^= 1 << q
    adj[q] ^= 1 << p
    dist = {p: 0}
    parent = {}
    queue = deque([p])
    while queue:
        v = queue.popleft()
        for u in bits(adj[v]):
            if u not in dist:
                dist[u] = dist[v] + 1
                parent[u] = v
                queue.append(u)
    if q not in dist:
        return None
    cycle = 1 << p
    v = q
    while v != p:
        cycle |= 1 << v
        v = parent[v]
    if cycle.bit_count() % 2 == 0:
        return cycle | (1 << hub)
    covered = cycle
    for v in bits(cycle):
        covered |= adj[v]
    outside = remainder & ~covered
    if outside:
        return cycle | (outside & -outside) | (1 << hub)

    adj[p] |= 1 << q
    adj[q] |= 1 << p
    layers = [[] for _ in range(max(dist.values()) + 1)]
    for v, level in dist.items():
        layers[level].append(v)

    # Each boundary state retains a single full witness prefix.
    states = {(0, 0, 0): 0}
    for level, layer in enumerate(layers):
        for v in layer:
            bit = 1 << v
            next_states = {}
            for (occupied, odd, parity), witness in states.items():
                if not pair & bit:
                    next_states.setdefault((occupied, odd, parity), witness)
                neighbors = occupied & adj[v]
                new_odd = odd ^ neighbors
                if neighbors.bit_count() % 2:
                    new_odd |= bit
                next_states.setdefault((occupied | bit, new_odd, parity ^ 1), witness | bit)
            states = next_states

        if level:
            forget = sum(1 << v for v in layers[level - 1] if v != p)
            next_states = {}
            for (occupied, odd, parity), witness in states.items():
                if not odd & forget:
                    next_states.setdefault((occupied & ~forget, odd & ~forget, parity), witness)
            states = next_states
    for (_, odd, parity), witness in states.items():
        if not odd and not parity:
            return witness | (1 << hub)
    return None


def raw_from_complement(n, edges):
    universe = (1 << (n + 1)) - 1
    rows = [universe ^ (1 << i) for i in range(n + 1)]
    for i, j in edges:
        rows[i] ^= 1 << j
        rows[j] ^= 1 << i
    return rows


def check(rows, h, p, q):
    pins = (h, p, q)
    answer = solve(rows, *pins)
    ground = any(native_witness(rows, pins, s) for s in range(1 << len(rows)))
    assert (answer is not None) == ground, (rows, pins, answer, ground)
    assert answer is None or native_witness(rows, pins, answer), (rows, pins, answer)
    return answer


def main():
    count = 0
    for n in range(2, 6):
        edges = list(combinations(range(n), 2))
        for mask in range(1 << len(edges)):
            rows = raw_from_complement(n, [edges[j] for j in bits(mask)])
            for p, q in edges:
                check(rows, n, p, q)
                count += 1
    print(f"Exhaustive native comparisons: {count}")
    u, v, a, b, c, d = range(6)
    rows = raw_from_complement(6, [(u,v), (u,a), (a,v), (u,b), (b,v), (u,c), (c,d), (d,v)])
    pins = (6, u, a)
    expected = (1 << 7) - 1
    assert [s for s in range(1 << 7) if native_witness(rows, pins, s)] == [expected]
    assert check(rows, *pins) == expected
    print("Four-path native fixture: unique full seven-site witness")


if __name__ == "__main__":
    main()
