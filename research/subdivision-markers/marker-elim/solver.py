"""Product guards (a,c,b,d) require (a.x+c)(b.x+d)=0. All masks are integers."""
from collections import Counter
from itertools import product


def parity(x):
    return x.bit_count() & 1


def chart(n, rows):
    """Return offset and free-direction vectors of an affine system."""
    echelon = {}
    for m, c in rows:
        while m:
            p = m.bit_length() - 1
            if p not in echelon:
                echelon[p] = (m, c)
                break
            v, d = echelon[p]
            m, c = m ^ v, c ^ d
        if not m and c:
            return None
    def fill(x, affine):
        for i in sorted(echelon):
            v, d = echelon[i]
            x |= (parity(v & x) ^ (d if affine else 0)) << i
        return x
    return fill(0, True), [fill(1 << i, False) for i in range(n) if i not in echelon]


class LinearBasis:
    def __init__(self):
        self.rows = {}
        self.normals = []

    def reduce(self, m):
        coeff = 0
        while m and (p := m.bit_length() - 1) in self.rows:
            v, c = self.rows[p]
            m, coeff = m ^ v, coeff ^ c
        return m, coeff

    def add(self, m):
        v, c = self.reduce(m)
        if v:
            self.rows[v.bit_length() - 1] = (v, c ^ (1 << len(self.normals)))
            self.normals.append(m)


def normalized_forbidden(rows):
    """Independent equalities defining a violated flat, or None if empty."""
    basis = {}
    for m, c in rows:
        while m and (p := m.bit_length() - 1) in basis:
            v, d = basis[p]
            m, c = m ^ v, c ^ d
        if m:
            basis[m.bit_length() - 1] = m, c
        elif c:
            return None
    return tuple(basis.values())


def coordinate_basis(flats, dim):
    weights = Counter()
    for flat in flats:
        directions = {m for m, _ in flat}
        if len(flat) == 2:
            directions.add(flat[0][0] ^ flat[1][0])
        weights.update(directions)
    basis = LinearBasis()
    for v in sorted(weights, key=lambda v: (-weights[v], v)):
        basis.add(v)
    for i in range(dim):
        basis.add(1 << i)
    return basis


def obstruction(flats, deleted):
    for flat in flats:
        representatives = {}
        live = 0
        for m, _ in flat:
            live |= m
        live &= ~deleted
        while live:
            bit = live & -live
            live ^= bit
            column = sum(bool(m & bit) << j for j, (m, _) in enumerate(flat))
            if column in representatives:
                return bit, representatives[column]
            representatives[column] = bit
            if len(representatives) == 3:
                return tuple(representatives.values())
    return ()


def backdoor(flats):
    def branch(deleted, remaining):
        conflict = obstruction(flats, deleted)
        if not conflict:
            return deleted
        if remaining:
            for bit in conflict:
                answer = branch(deleted | bit, remaining - 1)
                if answer is not None:
                    return answer
        return None
    depth = 0
    while True:
        answer = branch(0, depth)
        if answer is not None:
            return answer
        depth += 1


def two_sat(n, clauses):
    # Literal 2*i+v means coordinate i equals v.
    graph = [[] for _ in range(2*n)]
    reverse = [[] for _ in graph]
    for clause in clauses:
        if not clause:
            return None
        a, b = clause[0], clause[-1]
        for u, v in ((a ^ 1, b), (b ^ 1, a)):
            graph[u].append(v)
            reverse[v].append(u)
    seen, order = set(), []
    for root in range(2*n):
        if root in seen:
            continue
        stack = [(root, False)]
        while stack:
            u, done = stack.pop()
            if done:
                order.append(u)
            elif u not in seen:
                seen.add(u)
                stack.append((u, True))
                stack.extend((v, False) for v in graph[u] if v not in seen)
    component = {}
    for label, root in enumerate(reversed(order)):
        if root in component:
            continue
        stack = [root]
        component[root] = label
        while stack:
            u = stack.pop()
            for v in reverse[u]:
                if v not in component:
                    component[v] = label
                    stack.append(v)
    result = 0
    for i in range(n):
        a, b = component[2*i], component[2*i + 1]
        if a == b:
            return None
        result |= int(b > a) << i
    return result


def forbidden_clause(flat, deleted, values):
    live = 0
    for m, _ in flat:
        live |= m
    live &= ~deleted
    bits = [i for i in range(live.bit_length()) if live >> i & 1]
    assert len(bits) <= 2
    for xs in product(range(2), repeat=len(bits)):
        y = values | sum(v << i for i, v in zip(bits, xs))
        if all(parity(m & y) == c for m, c in flat):
            return tuple(2*i + (1 ^ v) for i, v in zip(bits, xs))
    return None


def solve(n, guards, markers):
    """Return (witness or None, minimum deletion size in the chosen basis)."""
    sliced = chart(n, markers)
    if sliced is None:
        return None, 0
    offset, directions = sliced
    flats = []
    for a, c, b, d in guards:
        flat = normalized_forbidden([
            (sum(parity(v & m) << i for i, v in enumerate(directions)), 1 ^ e ^ parity(m & offset))
            for m, e in ((a, c), (b, d))])
        if flat is None:
            continue
        if not flat:
            return None, 0
        flats.append(flat)
    dim = len(directions)
    basis = coordinate_basis(flats, dim)
    rewritten = [tuple((basis.reduce(m)[1], c) for m, c in flat) for flat in flats]
    deleted = backdoor(rewritten)
    pinned = [i for i in range(dim) if deleted >> i & 1]
    for xs in product(range(2), repeat=len(pinned)):
        values = sum(v << i for i, v in zip(pinned, xs))
        clauses = [clause for flat in rewritten
                   if (clause := forbidden_clause(flat, deleted, values)) is not None]
        assignment = two_sat(dim, clauses)
        if assignment is None:
            continue
        assignment = (assignment & ~deleted) | values
        free, _ = chart(dim, [(v, assignment >> i & 1) for i, v in enumerate(basis.normals)])
        witness = offset
        for i, v in enumerate(directions):
            if free >> i & 1:
                witness ^= v
        return witness, len(pinned)
    return None, len(pinned)
