"""Signed count of affine-constrained 2-CNF by graph branching and Gauss sums.

signed_count(n, clauses, equations=(), quadratic=()) uses signed DIMACS literals:
1 is x_0, -1 is its negation; an empty clause is false. Affine rows (mask, rhs)
mean parity(mask & x) = rhs. Quadratic ANF terms are monomial masks; 0 denotes
the constant. Duplicate phase terms cancel. Uses original_dag_quadratic.gauss.
"""
from collections import defaultdict
from original_dag_quadratic import gauss


def _xor_terms(poly, terms):
    for term in terms:
        if term in poly:
            poly.remove(term)
        else:
            poly.add(term)


def _multiply(a, b):
    result = set()
    for u in a:
        for v in b:
            _xor_terms(result, [u | v])
    return result


def _gaussian_leaf(n, rows, phase):
    pivots = {}
    for mask, rhs in rows:
        while mask:
            i = mask.bit_length() - 1
            if i not in pivots:
                pivots[i] = (mask, rhs)
                break
            other, bit = pivots[i]
            mask ^= other
            rhs ^= bit
        if mask == 0 and rhs:
            return 0

    # An expression is a set of ANF monomial masks on the free coordinates.
    expr = []
    dimension = 0
    for i in range(n):
        if i not in pivots:
            expr.append({1 << dimension})
            dimension += 1
        else:
            mask, rhs = pivots[i]
            current = {0} if rhs else set()
            lower = mask ^ (1 << i)
            while lower:
                bit = lower & -lower
                current ^= expr[bit.bit_length() - 1]
                lower ^= bit
            expr.append(current)
    result = set()
    for term in phase:
        if not term:
            result ^= {0}
            continue
        first = term & -term
        a = expr[first.bit_length() - 1]
        second = term ^ first
        result ^= _multiply(a, expr[second.bit_length() - 1]) if second else a
    return gauss(result, (1 << dimension) - 1)


def _prepare(n, clauses, rows):
    grouped = defaultdict(set)
    for clause in clauses:
        lits = tuple(clause)
        if len(lits) > 2 or any(type(v) is not int or not 1 <= abs(v) <= n for v in lits):
            raise ValueError("invalid 2-CNF clause")
        if not lits:
            return None
        u = lits[0]
        if len(lits) == 1 or u == lits[1]:
            rows.append((1 << (abs(u) - 1), int(u > 0)))
            continue
        if u == -lits[1]:
            continue
        a, b = sorted(lits, key=abs)
        grouped[abs(a)-1, abs(b)-1].add((int(a < 0), int(b < 0)))
    edges = []
    for (a, b), forbidden in grouped.items():
        if len(forbidden) == 1:
            x, y = next(iter(forbidden))
            edges.append((a, b, x, y))
            continue
        feasible = [(x, y) for x in (0, 1) for y in (0, 1) if (x, y) not in forbidden]
        if not feasible:
            return None
        # Any nonempty set of at most two points of the binary plane is affine.
        for i, j in ((1, 0), (0, 1), (1, 1)):
            values = {(i*x) ^ (j*y) for x, y in feasible}
            if len(values) == 1:
                rows.append(((i << a) | (j << b), values.pop()))
    return edges


def _branch(edges, rows, vertex, value):
    fixed = {vertex: value}
    for a, b, x, y in edges:
        if a == vertex and value == x:
            fixed[b] = 1-y
        if b == vertex and value == y:
            fixed[a] = 1-x
    new_rows = rows + [(1 << i, b) for i, b in fixed.items()]
    remaining = []
    for a, b, x, y in edges:
        if a not in fixed and b not in fixed:
            remaining.append((a, b, x, y))
        elif a in fixed and b in fixed:
            if (fixed[a], fixed[b]) == (x, y):
                return None
        elif a in fixed and fixed[a] == x:
            new_rows.append((1 << b, 1-y))
        elif b in fixed and fixed[b] == y:
            new_rows.append((1 << a, 1-x))
    return remaining, new_rows


def _matching(n, edges, rows, phase):
    pairs = []
    for a, b, x, y in edges:
        violation = _multiply({1 << a} ^ ({0} if not x else set()),
                              {1 << b} ^ ({0} if not y else set()))
        pairs.append((violation, [(1 << a, x), (1 << b, y)]))
    # All terms have the same denominator. The joint violation has numerator -2.
    total = 0
    stack = [(0, rows, phase, 1)]
    while stack:
        i, eq, poly, coeff = stack.pop()
        if i >= len(pairs):
            total += coeff * _gaussian_leaf(n, eq, poly)
            continue
        toggle, pins = pairs[i]
        if i+1 < len(pairs):
            other, extra = pairs[i+1]
            toggle = toggle ^ other
            stack.append((i+2, eq+pins+extra, poly, -2*coeff))
        stack.append((i+2, eq, poly, coeff))
        stack.append((i+2, eq, poly ^ toggle, coeff))
    quotient, remainder = divmod(total, 1 << ((len(edges)+1)//2))
    assert remainder == 0
    return quotient


def signed_count(n, clauses, equations=(), quadratic=()):
    if type(n) is not int or n < 0:
        raise ValueError("nonnegative variable count required")
    rows = list(equations)
    for mask, rhs in rows:
        if type(mask) is not int or mask < 0 or mask >> n or rhs not in (0,1):
            raise ValueError("invalid affine row")
    phase = set()
    for term in quadratic:
        if type(term) is not int or term < 0 or term >> n or term.bit_count() > 2:
            raise ValueError("invalid quadratic monomial")
        _xor_terms(phase, [term])
    edges = _prepare(n, clauses, rows)
    if edges is None:
        return 0
    stack = [(edges, rows)]
    total = 0
    while stack:
        edges, rows = stack.pop()
        adj = defaultdict(dict)
        for a,b,x,y in edges:
            adj[a][b] = x
            adj[b][a] = y
        pivot = next((v for v in adj if len(adj[v]) >= 3), None)
        if pivot is None:
            # On a path use a neighbor of an endpoint. Leave isolated edges pooled.
            pivot = next((v for v in adj if len(adj[v]) == 2
                          and any(len(adj[u]) == 1 for u in adj[v])), None)
        if pivot is None:
            pivot = next((v for v in adj if len(adj[v]) == 2), None)
            if pivot is None:
                total += _matching(n, edges, rows, phase)
                continue
            a, b = adj[pivot]
            if a in adj[b]:
                tri = (pivot, a, b)
                mixed = next((v for v in tri if len(set(adj[v].values())) == 2), None)
                if mixed is None:
                    # A local bit is 1 exactly at the offending endpoint value.
                    # Allowed vectors of local bits: 000,100 versus 010,001.
                    x,y,z = (next(iter(adj[v].values())) for v in tri)
                    tail = [e for e in edges if e[0] not in tri and e[1] not in tri]
                    stack.append((tail, rows+[(1 << a, 1-y), (1 << b, 1-z)]))
                    stack.append((tail, rows+[(1 << pivot, 1-x), ((1 << a)|(1 << b), 1^y^z)]))
                    continue
                pivot = mixed
        for val in (0,1):
            child = _branch(edges, rows, pivot, val)
            if child is not None:
                stack.append(child)
    return total


def _direct(n, clauses, rows, phase):
    total = 0
    for x in range(1 << n):
        if not all(any(bool(x & (1 << (abs(v)-1))) == (v > 0) for v in clause) for clause in clauses):
            continue
        if any((x & mask).bit_count() % 2 != rhs for mask, rhs in rows):
            continue
        total += (-1) ** (sum((x & mask) == mask for mask in phase) % 2)
    return total


def selftest():
    from itertools import combinations, product
    from random import Random

    rng = Random(4874)
    cases = 0

    def verify(n, clauses, rows=(), phase=()):
        nonlocal cases
        answer = signed_count(n, clauses, rows, phase)
        assert answer == _direct(n, clauses, rows, phase), (n, clauses, rows, phase, answer)
        cases += 1

    for n in range(6):
        possible = list(combinations(range(1, n+1), 2))
        for graph in range(1 << len(possible)):
            clauses = [(a*rng.choice((-1,1)), b*rng.choice((-1,1)))
                       for i, (a,b) in enumerate(possible) if graph >> i & 1]
            rows = [(rng.randrange(1 << n), rng.randrange(2)) for _ in range(rng.randrange(3))]
            phase = [t for t in range(1 << n) if t.bit_count() <= 2 and rng.randrange(4) == 0]
            verify(n, clauses, rows, phase)

    # Every signing of the triangle, including the two-line leaves.
    for signs in product((-1,1), repeat=6):
        tri = [(signs[0], 2*signs[1]), (2*signs[2], 3*signs[3]), (signs[4], 3*signs[5])]
        verify(5, tri, [(19,1)], [0,3,18,24])
    # Paths, cycles, stars, disjoint pooled edges and an endpoint outside the CNF.
    for n in range(3,10):
        path = [(i,i+1) for i in range(1,n)]
        for edges in (path, path+[(n,1)], [(1,i) for i in range(2,n+1)], path[::2]):
            verify(n+1, edges, [(1 | (1 << n),1)], [0,5,(1 << n)|2])
    for _ in range(150):
        n = rng.randrange(1,9)
        random_lit = lambda: rng.choice((-1,1))*rng.randrange(1,n+1)
        clauses = [tuple(random_lit() for _ in range(rng.choice((1,2,2,2))))
                   for _ in range(rng.randrange(15))]
        phase = [rng.choice([0,1 << rng.randrange(n), (1 << rng.randrange(n))|(1 << rng.randrange(n))])
                 for _ in range(6)]
        verify(n, clauses, [(rng.randrange(1 << n),rng.randrange(2))], phase)
    for mask in range(16):
        pair = [(1,2),(1,-2),(-1,2),(-1,-2)]
        verify(4, [c for i,c in enumerate(pair) if mask>>i&1]+[(3,-3),(4,4)], [], [0,10])
    verify(0, [()], [], [0])
    verify(3, [], [(0,1)], [])
    verify(0, [], [], [0])
    print(cases, "signed truth-table comparisons passed")


if __name__ == "__main__":
    import argparse
    import json
    import sys

    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        selftest()
    else:
        instance = json.load(sys.stdin)
        print(signed_count(**instance))
