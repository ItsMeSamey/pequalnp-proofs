from itertools import combinations


def variables(mask):
    return [i for i in range(mask.bit_length()) if mask >> i & 1]


def check(edges, h):
    pigeons = [[i for i, (p, _) in enumerate(edges) if p == j] for j in range(h+1)]
    holes = [[i for i, (_, v) in enumerate(edges) if v == j] for j in range(h)]
    first = {hrow[0] for hrow in holes}
    free = [i for i in range(len(edges)) if i not in first]
    label = {e: i for i, e in enumerate(free)}
    rows = []
    # Polynomials are sets of squarefree monomials, themselves bitmasks.
    for p in pigeons:
        expanded = {sum(1 << e for e in t) for j in range(len(p)+1) for t in combinations(p, j)}
        for monomial in list(expanded):
            if monomial.bit_count() >= 2:
                i, j = variables(monomial)[:2]
                assert i in p and j in p
                expanded.remove(monomial)
        assert expanded == {0} | {1 << e for e in p}
    for hrow in holes:
        f = hrow[0]
        p = pigeons[edges[f][0]]
        for i, e in enumerate(hrow[1:], 1):
            prefix = set(p) - {f}
            prefix.symmetric_difference_update(hrow[1:i])
            assert prefix.issubset(free)
            source = {(1 << e) | (1 << k) for k in hrow[:i]}
            source.symmetric_difference_update({1 << e} | {(1 << e) | (1 << k) for k in p})
            target = {1 << e} ^ {(1 << e) | (1 << k) for k in prefix}
            assert source == target
            rows.append((label[e], sum(1 << label[k] for k in prefix)))
    marker = sum(1 << label[e] for e in pigeons[-1])
    for assignment in range(1 << len(free)):
        guard_ok = all(not assignment >> i & 1 or (row & assignment).bit_count() % 2
                       for i, row in rows)
        chosen = {e for e in free if assignment >> label[e] & 1}
        chosen.update(f for f in first if len(chosen.intersection(pigeons[edges[f][0]])) % 2 == 0)
        assert guard_ok == all(len(chosen.intersection(hrow)) <= 1 for hrow in holes)
        if guard_ok:
            assert not marker & assignment
            assert all(len(chosen.intersection(p)) == 1 for p in pigeons[:-1])


if __name__ == '__main__':
    h = 3
    matching = [(i, i) for i in range(h)]
    optional = [(p, v) for p in range(h+1) for v in range(h) if p != v]
    for mask in range(1 << len(optional)):
        check(matching + [edge for i, edge in enumerate(optional) if mask >> i & 1], h)
    print("512 graph compilers passed symbolic identities and exhaustive base and marker checks.")
