"""Small independent truth-table oracles for physical row CSPs."""
from itertools import combinations, product

import row_csp


def accepts(bits, clauses):
    return all(any(bool(bits[abs(lit) - 1]) == (lit > 0) for lit in clause)
               for clause in clauses)


def projection_check(n, base, rows):
    models = [v for v in product(range(2), repeat=n) if accepts(v, base)]
    assert models
    supports = [[{v for v in models if accepts(v, pins)} for pins in choices]
                for choices in rows]
    domains = [[s for s, support in enumerate(group) if support] for group in supports]
    graph = [{} for group in rows]
    empty = any(not group for group in domains)
    for i, j in combinations(range(len(rows)), 2):
        pairs = set(product(domains[i], domains[j]))
        allowed = {(s, t) for s, t in pairs if supports[i][s] & supports[j][t]}
        empty |= not allowed
        if allowed != pairs:
            graph[i][j] = allowed
            graph[j][i] = {(t, s) for s, t in allowed}
    assert row_csp._relations(n, base, rows) == (None if empty else (domains, graph))
    for choice in product(*domains):
        joint = set(models)
        for i, s in enumerate(choice):
            joint &= supports[i][s]
        assert bool(joint) == all((choice[i], choice[j]) in allowed
                                  for i, links in enumerate(graph)
                                  for j, allowed in links.items())


def color_fixture(size, edges, colors):
    inputs = 2 * size
    gates, clauses, indicators = [], [], []

    def nand(a, b):
        gates.append((a, b))
        return inputs + len(gates) - 1

    for v in range(size):
        a, b = 2*v, 2*v+1
        na, nb = nand(a, a), nand(b, b)
        group = []
        for x, y in product((na, a), (nb, b)):
            neg = nand(x, y)
            group.append(nand(neg, neg) + 1)
        indicators.append(group)
        clauses.extend([(-lit,) for lit in group[colors:]])
    for u, v in edges:
        clauses.extend([(-x, -y) for x, y in zip(indicators[u], indicators[v])])
    return inputs, gates, clauses


def tree_check():
    pairs = list(product(range(2), repeat=2))
    order = [1, 0, 2]
    parent = {1: None, 0: 1, 2: 1}
    for left, right in product(range(1, 15), repeat=2):
        graph = [{}, {}, {}]
        for child, mask in ((0, left), (2, right)):
            ok = {pair for i, pair in enumerate(pairs) if mask & (1 << i)}
            graph[1][child] = ok
            graph[child][1] = {(b, a) for a, b in ok}
        models = {word for word in product(range(2), repeat=3)
                  if all((word[1], word[j]) in graph[1][j] for j in (0, 2))}
        actual = row_csp._tree(order, parent, [[0, 1] for _ in order], graph)
        if models:
            assert tuple(actual[i] for i in range(3)) in models
        else:
            assert actual is None


def original_check(size, edges, colors, cyclic, satisfiable):
    inputs, gates, clauses = color_fixture(size, edges, colors)

    def good(raw):
        bits = list(raw)
        for a, b in gates:
            bits.append(1 - (bits[a] & bits[b]))
        return accepts(bits, clauses)

    models = {raw for raw in product(range(2), repeat=inputs) if good(raw)}
    assert bool(models) == satisfiable
    for cap in (0, None):
        status, stats, raw = row_csp.solve(inputs, gates, clauses=clauses, max_search=cap)
        assert stats["bad"] == size
        assert stats["cyclic_components"] == int(cyclic)
        if cyclic and cap == 0:
            assert status == "skip" and raw is None
        elif models:
            assert status == "sat" and raw in models
        else:
            assert status == "unsat" and raw is None
        if not cyclic:
            assert stats["forest_components"] == 1 and stats["searched"] == 0


def main():
    tree_check()
    choices = [[[(i,)], [(-i,)]] for i in (1, 2, 3)]
    # A hidden wire produces a conflict between two rows with disjoint ports.
    projection_check(4, [(-1, 4), (-4, -2), (2, 3)], choices)
    projection_check(3, [], choices + [[[(1,), (-2,)], [(-1,), (2,)]]])
    projection_check(3, [(1,)], [[[(-1,)]], choices[1]])
    projection_check(3, [(-1, -2)], [[[(1,)]], [[(2,)]]])
    path = [(0, 1), (1, 2)]
    triangle = path + [(2, 0)]
    original_check(3, path, 2, False, True)
    original_check(3, triangle, 2, True, False)
    original_check(3, triangle, 4, True, True)
    print("projection truth tables and three raw NAND fixtures passed")


if __name__ == "__main__":
    main()
