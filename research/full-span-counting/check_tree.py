"""Independent exhaustive checks of weighted hidden-tree union correction."""
from collections import deque
from itertools import combinations, product
from random import Random


def prufer_tree(code, m):
    degree = [1 + code.count(i) for i in range(m)]
    edges = []
    for v in code:
        u = next(i for i in range(m) if degree[i] == 1)
        edges.append(tuple(sorted((u, v))))
        degree[u] -= 1
        degree[v] -= 1
    last = [i for i in range(m) if degree[i] == 1]
    if len(last) == 2:
        edges.append(tuple(last))
    return tuple(sorted(edges))


def kruskal(weights, m):
    parts = [{i} for i in range(m)]
    edges = []
    for u, v in sorted(weights, key=lambda e: (-weights[e], e)):
        a = next(p for p in parts if u in p)
        b = next(p for p in parts if v in p)
        if a != b:
            edges.append((u, v))
            parts.remove(b)
            a.update(b)
    return tuple(sorted(edges))


def components(active, edges):
    todo = set(active)
    total = 0
    while todo:
        total += 1
        queue = [todo.pop()]
        while queue:
            v = queue.pop()
            for a, b in edges:
                u = b if a == v else a if b == v else None
                if u in todo:
                    todo.remove(u)
                    queue.append(u)
    return total


def interior(u, v, edges):
    queue = deque([(u, (u,))])
    while queue:
        w, path = queue.popleft()
        if w == v:
            return path[1:-1]
        for a, b in edges:
            z = b if a == w else a if b == w else None
            if z is not None and z not in path:
                queue.append((z, path+(z,)))
    raise AssertionError("Disconnected tree")


def verify(rows, m):
    # Every row is a distinct short-core model; equal event sets may recur.
    pairs = list(combinations(range(m), 2))
    events = [{x for x, row in enumerate(rows) if i in row} for i in range(m)]
    weights = {(u, v): len(events[u] & events[v]) for u, v in pairs}
    b_sum = sum(map(len, events))
    union = set().union(*events)
    chosen = kruskal(weights, m)
    predicted = b_sum - sum(weights[e] for e in chosen)
    defects = [max(0, components(row, chosen)-1) for row in rows]
    # Enumerate gap witnesses via intersections and set difference independently
    # of the graph traversal used to obtain the defects.
    gaps = set()
    for u, v in pairs:
        for z in interior(u, v, chosen):
            gaps.update((events[u] & events[v]) - events[z])
    assert gaps == {x for x, defect in enumerate(defects) if defect}
    correction = sum(len(rows[x])-sum(u in rows[x] and v in rows[x]
                                      for u, v in chosen)-1 for x in gaps)
    assert predicted - correction == len(union)
    assert len(rows) - predicted + correction == sum(not row for row in rows)
    best_bad = len(rows) + 1
    best_cost = len(rows)*(m+1)+1
    best_max_weight_bad = None
    for code in product(range(m), repeat=max(0, m-2)):
        tree = prufer_tree(code, m)
        counts = [components(row, tree) for row in rows]
        cost = sum(counts)
        bad = sum(c > 1 for c in counts)
        best_bad = min(best_bad, bad)
        assert cost == b_sum - sum(weights[e] for e in tree)
        if cost < best_cost:
            best_cost, best_max_weight_bad = cost, bad
        elif cost == best_cost:
            best_max_weight_bad = min(best_max_weight_bad, bad)
    assert predicted == best_cost
    assert len(gaps) <= correction <= (m-1)*best_bad
    return correction, best_max_weight_bad


def main():
    # Three pair-events force at least one disconnected row on every tree.
    assert verify([{0, 1}, {0, 2}, {1, 2}, set()], 3) == (1, 1)
    rng = Random(1782)
    cases = 1
    for m in range(1, 7):
        for _ in range(5):
            n = rng.randrange(2, 5)
            literals = [i for i in range(1, n+1)] + [-i for i in range(1, n+1)]
            core = [rng.sample(literals, 2) for _ in range(2)]
            rows = []
            for x in product(range(2), repeat=n):
                if all(any(bool(x[abs(v)-1]) == (v > 0) for v in c) for c in core):
                    rows.append({i for i in range(m) if rng.randrange(2)})
            verify(rows, m)
            cases += 1
    print(f"{cases} examples passed; all labeled trees checked for m=1..6. "
          "Triangle: every maximum tree has one defective row, exact correction=1.")


if __name__ == '__main__':
    main()
