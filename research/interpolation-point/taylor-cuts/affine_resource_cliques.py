"""Discover native signed-literal cliques and replay exact resource certificates.

Certificates are lists of (kind, signed_literal_tuple, nonnegative_weight).
The public input is an integer CNF; certificates never supply trusted graph edges.
"""
from collections import Counter, defaultdict
from fractions import Fraction
from itertools import combinations


def native_clauses(n, clauses):
    if type(n) is not int or n < 0:
        raise ValueError("invalid variable count")
    result = set()
    for clause in clauses:
        terms = set()
        for lit in clause:
            if type(lit) is not int or not 1 <= abs(lit) <= n:
                raise ValueError("invalid signed literal")
            terms.add(lit)
        if not any(-lit in terms for lit in terms):
            result.add(tuple(sorted(terms)))
    return result


def incompatibilities(clauses):
    neighbors = defaultdict(set)
    for clause in clauses:
        if len(clause) == 2:
            a, b = (-lit for lit in clause)
            neighbors[a].add(b)
            neighbors[b].add(a)
    return neighbors


def discover_cliques(n, clauses):
    native = native_clauses(n, clauses)
    neighbors = incompatibilities(native)
    found = set()
    for a in neighbors:
        for b in neighbors[a]:
            if a < b:
                candidate = {a, b} | (neighbors[a] & neighbors[b])
                if all(v in neighbors[u] for u, v in combinations(candidate, 2)):
                    found.add(tuple(sorted(candidate)))
    return found


def verify(n, clauses, certificate):
    """Prove UNSAT by reducing a nonnegative sum of rows to a negative constant."""
    try:
        native = native_clauses(n, clauses)
        neighbors = incompatibilities(native)
        coeff = Counter()
        constant = Fraction(0)
        for kind, row, weight in certificate:
            if type(weight) is not int and not isinstance(weight, Fraction):
                return False
            if weight < 0:
                return False
            if not isinstance(row, (tuple, list)) or any(
                type(lit) is not int or not 1 <= abs(lit) <= n for lit in row
            ):
                return False
            if len(set(row)) != len(row):
                return False
            if kind == "clause" and tuple(sorted(row)) in native:
                constant -= weight
                signed_weight = weight
            elif kind == "clique" and all(
                v in neighbors.get(u, ()) for u, v in combinations(row, 2)
            ):
                constant += weight
                signed_weight = -weight
            elif kind == "nonnegative" and len(row) == 1:
                signed_weight = weight
            else:
                return False
            for lit in row:
                if lit < 0:
                    constant += signed_weight
                    coeff[-lit] -= signed_weight
                else:
                    coeff[lit] += signed_weight
        return not any(coeff.values()) and constant < 0
    except (IndexError, TypeError, ValueError):
        return False


def resource_certificate(n, clauses):
    """Find the unit-weight pigeon/slot counting proof; otherwise return None."""
    native = native_clauses(n, clauses)
    cliques = discover_cliques(n, native)
    neighbors = incompatibilities(native)
    likely_events = {lit for lit, adj in neighbors.items() if len(adj) >= 2}
    likely_events.update(c[0] for c in native if len(c) == 1)
    families = [{c for c in native if len(c) >= 3},
                {c for c in native if set(c) <= likely_events}]
    for demands in families:
        occupied = {lit for c in demands for lit in c}
        resources = {c for c in cliques if c not in demands and set(c) <= occupied}
        covered = {lit for c in resources for lit in c}
        resources.update((lit,) for lit in occupied - covered)
        cert = ([("clause", c, 1) for c in sorted(demands)]
                + [("clique", c, 1) for c in sorted(resources)])
        if verify(n, native, cert):
            return cert
    return None
