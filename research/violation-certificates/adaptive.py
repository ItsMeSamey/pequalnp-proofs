"""Exact adaptive split discovery; returns None if no local witness is found."""
from functools import cache
from itertools import combinations, product
from verify import solve


def simplify(clauses, literal):
    return frozenset(c - {-literal} for c in clauses if literal not in c)


def components(variables, clauses):
    adjacent = {v: set() for v in variables}
    for clause in clauses:
        scope = {abs(l) for l in clause}
        if scope:
            first = min(scope)
            for v in scope:
                adjacent[first].add(v)
                adjacent[v].add(first)
    pending = set(variables)
    groups = []
    while pending:
        start = pending.pop()
        group, stack = {start}, [start]
        while stack:
            reached = adjacent[stack.pop()] & pending
            stack.extend(reached)
            group.update(reached)
            pending.difference_update(reached)
        groups.append(frozenset(group))
    return groups


def refuted(clauses, degree):
    items = list(clauses)
    features = [frozenset().union(*selected) for size in range(1, degree + 1)
                for selected in combinations(items, size)]
    features = list(set(c for c in features if all(-l not in c for l in c)))
    n = len({abs(l) for c in clauses for l in c})
    def moment(cube):
        return 0 if any(-l in cube for l in cube) else 2 ** (n-len(cube))
    rhs = [moment(c) for c in features]
    gram = [[moment(a | b) for b in features] + [moment(a)] for a in features]
    w = solve(gram, len(features))
    return w is not None and sum(a*b for a, b in zip(rhs, w)) == 2**n


def count(variables, clauses, depth=1, degree=1):
    """Use signed integer literals. Include free variables in variables."""
    clauses = frozenset(frozenset(c) for c in clauses if not any(-l in c for l in c))

    @cache
    def visit(vs, cs):
        if frozenset() in cs:
            return 0
        if not cs:
            return 2**len(vs)
        if len(vs) <= 2:
            return sum(all(c & values for c in cs) for values in
                       (set(xs) for xs in product(*[(v, -v) for v in vs])))
        original = len(vs)

        @cache
        def search(current, formula, budget):
            if frozenset() in formula:
                return 0
            groups = components(current, formula)
            if all(3*len(g) <= 2*original for g in groups):
                total = 1
                for g in groups:
                    part = frozenset(c for c in formula if abs(next(iter(c))) in g)
                    value = visit(g, part)
                    if value is None:
                        return None
                    total *= value
                return total
            if refuted(formula, degree):
                return 0
            if budget:
                for v in current:
                    a = search(current-{v}, simplify(formula, v), budget-1)
                    if a is not None:
                        b = search(current-{v}, simplify(formula, -v), budget-1)
                        if b is not None:
                            return a+b
            return None

        return search(vs, cs, depth)
    return visit(frozenset(variables), clauses)


if __name__ == '__main__':
    family = [(1, 2), (-1, 3), (1, -4), (2, 3), (-2, 4), (-3, -4), (1, 3, 4), (-1, -2, 4)]
    total = accepted = 0
    for size in range(len(family)+1):
        for cs in combinations(family, size):
            total += 1
            brute = sum(all(set(c) & set(vals) for c in cs)
                        for vals in product(*[(v, -v) for v in range(1, 5)]))
            value = count(range(1, 5), cs)
            if value is not None:
                assert value == brute, (cs, brute, value)
                accepted += 1
    print('accepted', accepted, 'of', total)
