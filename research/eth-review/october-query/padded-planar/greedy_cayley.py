"""Exact physical trial replay. Prior forward-prefix approach: greedy-walsh-batches.md."""
from collections import deque


def kernel(rows, width):
    pivots = {}
    for row in rows:
        if not 0 <= row < 1 << width:
            raise ValueError("row outside physical coordinates")
        while row:
            j = row.bit_length() - 1
            if j not in pivots:
                pivots[j] = row
                break
            row ^= pivots[j]
    basis = []
    for free in range(width):
        if free not in pivots:
            word = 1 << free
            for j, row in sorted(pivots.items()):
                word |= ((word & row).bit_count() % 2) << j
            basis.append(word)
    return basis


def distances(gens, starts, size):
    queue = deque(starts)
    dist = [size + 1] * size
    for a in queue:
        dist[a] = 0
    while queue:
        a = queue.popleft()
        for g in gens:
            b = a ^ g
            if dist[b] > dist[a] + 1:
                dist[b] = dist[a] + 1
                queue.append(b)
    return dist


def scores(masses):
    table = masses.copy()
    stride = 1
    while stride < len(table):
        for start in range(0, len(table), 2 * stride):
            for i in range(start, start + stride):
                a, b = table[i], table[i + stride]
                table[i], table[i + stride] = a + b, a - b
        stride *= 2
    total = table[0]
    return [(total + signed) // 2 for signed in table]


def replay(width, prefix, length, rounds, weight):
    """Yield (ordered list of (coordinate,bit), physical XOR row, exact score)."""
    if width < 1 or length < 0 or rounds < 0:
        raise ValueError("invalid trial dimensions")
    basis = kernel(prefix, width)
    words = [0]
    for vec in basis:
        words += [x ^ vec for x in words]
    masses = [weight(x) for x in words]
    gen = [sum(((b >> e) & 1) << j for j, b in enumerate(basis)) for e in range(width)]
    gens = set(gen) - {0}
    size = len(words)
    forward = distances(gens, [0], size)
    reachable = [a for a in range(size) if forward[a] <= length]
    for _ in range(rounds):
        values = scores(masses)
        best = min(values[a] for a in reachable)
        reverse = distances(gens, [a for a in reachable if values[a] == best], size)
        chosen = []
        a = row = 0
        for left in reversed(range(length)):
            for e in range(width):
                if reverse[a] <= left:
                    chosen.append((e, 0))
                    break
                if reverse[a ^ gen[e]] <= left:
                    chosen.append((e, 1))
                    a ^= gen[e]
                    row ^= 1 << e
                    break
        masses = [0 if (a & u).bit_count() % 2 else w for u, w in enumerate(masses)]
        assert len(chosen) == length and sum(masses) == best
        yield chosen, row, best


def prism_weight(columns, word):
    """Guard at 0; each column then has rung, upper rail, lower rail clockwise."""
    if columns < 4 or not 0 <= word < 1 << (1 + 3 * columns):
        raise ValueError("invalid prism profile")
    def edge(index, first, second):
        violated = (word >> index) & 1
        if first or second:
            return 0 if violated else 2
        return 1  # exactly one gate bit for either prescribed violation
    total = 0
    for initial in range(4):
        dp = [int(s == initial) for s in range(4)]
        for col in range(columns):
            base = 1 + 3 * col
            nxt = [0] * 4
            for s, count in enumerate(dp):
                rung = edge(base, s & 1, s >> 1)
                for t in range(4):
                    nxt[t] += count * rung * edge(base + 1, s & 1, t & 1) * edge(base + 2, s >> 1, t >> 1)
            dp = nxt
        total += dp[initial]
    return total  # guard uniquely determined by bit 0


def prism_profile_oracle(clauses):
    """Recognize a positive guarded prism leaf and preserve physical clause order."""
    from collections import Counter
    if any(len(c) not in (1, 3) or len(set(c)) != len(c) or min(c) < 1 for c in clauses):
        raise ValueError("expected positive guard unit and distinct positive triples")
    units = [i for i, c in enumerate(clauses) if len(c) == 1]
    if len(units) != 1:
        raise ValueError("guard unit not unique")
    guard = units[0]
    degree = Counter(v for c in clauses for v in c)
    if degree[clauses[guard][0]] != 1:
        raise ValueError("guard reused")
    nbr = {}
    indices = {}
    for i, clause in enumerate(clauses):
        if i == guard:
            continue
        spins = [v for v in clause if degree[v] == 3]
        if len(spins) != 2 or sum(degree[v] == 1 for v in clause) != 1:
            raise ValueError("invalid prism edge roles")
        a, b = spins
        edge = frozenset(spins)
        if edge in indices:
            raise ValueError("parallel base edge")
        indices[edge] = i
        nbr.setdefault(a, set()).add(b)
        nbr.setdefault(b, set()).add(a)
    for a in nbr:
        for b in nbr[a]:
            for c in nbr[a] - {b}:
                for d in (nbr[b] & nbr[c]) - {a}:
                    pairs = [(a, b), (c, d)]
                    seen = {a, b, c, d}
                    while len(seen) < len(nbr):
                        (u, v), (x, y) = pairs[-2:]
                        z, = nbr[x] - {u, y}
                        w, = nbr[y] - {v, x}
                        if z in seen or w in seen or w not in nbr[z]:
                            break
                        pairs.append((z, w))
                        seen.update((z, w))
                    if len(pairs) < 4 or 2 * len(pairs) != len(nbr):
                        continue
                    order = [guard]
                    for i, (x, y) in enumerate(pairs):
                        z, w = pairs[(i + 1) % len(pairs)]
                        for edge in ((x, y), (x, z), (y, w)):
                            order.append(indices.get(frozenset(edge), -1))
                    if sorted(order) == list(range(len(clauses))):
                        def weight(word):
                            if not 0 <= word < 1 << len(order):
                                raise ValueError("invalid physical word")
                            canonical = sum(((word >> j) & 1) << i for i, j in enumerate(order))
                            return prism_weight(len(pairs), canonical)
                        return weight
    raise ValueError("base graph is not a simple prism")
