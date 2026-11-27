"""Weighted contraction of signed raw read-at-most-two CNFs over F3."""
from collections import defaultdict
from operator import index


def evaluate(formula, point, *, max_states=None):
    """max_states bounds assignments in any one elimination bucket."""
    z = tuple(index(x) % 3 for x in point)
    if max_states is not None:
        max_states = index(max_states)
        if max_states < 0:
            raise ValueError("negative state budget")
    reads = [0] * len(z)
    occurrences = defaultdict(list)
    active = []
    empty = False
    seen = set()
    for label, raw in enumerate(formula):
        literals = set()
        for variable, polarity in raw:
            i, p = index(variable), index(polarity)
            if not 0 <= i < len(z) or p not in (0, 1):
                raise ValueError("invalid literal")
            reads[i] += 1
            if reads[i] > 2:
                raise ValueError("more than two raw occurrences")
            literals.add((i, p))
        if any((i, 1-p) in literals or z[i] == p for i, p in literals):
            continue
        live = frozenset((i, p) for i, p in literals if z[i] == 2)
        if not live:
            empty = True
        if live in seen:
            continue
        seen.add(live)
        active.append(label)
        for i, p in live:
            occurrences[i].append((label, p))

    def exact(value):
        return {"status": "exact", "value": value}

    if empty:
        return exact(0)
    if not active:
        return exact(1)

    unary = dict.fromkeys(active, 2)
    edges = {}
    for incidence in occurrences.values():
        c, p = incidence[0]
        if len(incidence) == 1:
            unary[c] = 2 * unary[c] % 3
            continue
        d, q = incidence[1]
        table = edges.setdefault((c, d), [1, 1, 1, 1])
        for j, weight in enumerate((1, 2, 2, 2 if p == q else 0)):
            table[j] = table[j] * weight % 3

    graph = {c: set() for c in active}
    for c, d in edges:
        graph[c].add(d)
        graph[d].add(c)
    plan = []
    width = 0
    while graph:
        c = min(graph, key=lambda v: (len(graph[v]), v))
        neighbors = tuple(sorted(graph.pop(c)))
        width = max(width, len(neighbors))
        for d in neighbors:
            graph[d].discard(c)
            graph[d].update(v for v in neighbors if v != d)
        plan.append((c, neighbors))
    required = 1 << (width + 1)
    if max_states is not None and required > max_states:
        return dict(status="unknown", reason="state_budget",
                    required=required, available=max_states)

    factors = [((c,), (1, w)) for c, w in unary.items()]
    factors.extend(edges.items())
    scalar = 1
    for c, neighbors in plan:
        position = {v: i for i, v in enumerate((c,) + neighbors)}
        rest = []
        bucket = []
        for scope, table in factors:
            if c in scope:
                bucket.append(([position[v] for v in scope], table))
            else:
                rest.append((scope, table))
        out = [0] * (1 << len(neighbors))
        for assignment in range(2 * len(out)):
            product = 1
            for bits, table in bucket:
                row = sum(((assignment >> i) & 1) << j
                          for j, i in enumerate(bits))
                product = product * table[row] % 3
                if not product:
                    break
            k = assignment >> 1
            out[k] = (out[k] + product) % 3
        if neighbors:
            rest.append((neighbors, out))
        else:
            scalar = scalar * out[0] % 3
            if not scalar:
                return exact(0)
        factors = rest
    return exact(scalar)
