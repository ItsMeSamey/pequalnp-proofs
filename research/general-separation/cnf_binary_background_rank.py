"""Exact GF(2) rank of ternary clause misses restricted to an original 2-CNF.

Inputs are signed one-based IDs. First occurrences index normalized clauses.
The Boolean result is exact independent of the translation origin. Costs are
polynomial in the explicit input bit length per hitting-set assignment.
The search has at most 2**g leaves for g selected variables, g <= rank.
"""
from dataclasses import dataclass
from collections import Counter
from ring_image_group_horn_strict import _rename


def _model(rows, pins=()):
    """Model via implications; the helper maps a signed pair to its two arcs."""
    pairs, labels = [], set()
    for row in rows:
        if not row:
            return None
        pairs.append(row if len(row) == 2 else (row[0],row[0]))
        labels.update(map(abs,row))
    for lit in pins:
        pairs.append((lit,lit))
        labels.add(abs(lit))
    model = _rename(sorted(labels),pairs)
    if model is not None and not all((abs(x) in model) == (x>0) or (abs(y) in model) == (y>0)
                                     for x,y in pairs):
        raise AssertionError("invalid 2-SAT model")
    return model


@dataclass(frozen=True)
class BackgroundBasis:
    original: tuple
    used: tuple
    feasible: bool
    origin_true_ids: tuple
    background_indices: tuple
    background: tuple
    indices: tuple
    clauses: tuple

    @property
    def rank(self):
        return len(self.indices)


def project(arity,clauses):
    if type(arity) is not int or arity < 0:
        raise ValueError("invalid arity")
    raw = tuple(tuple(row) for row in clauses)
    used, seen = set(), set()
    background, residual = [], []
    for index,row in enumerate(raw):
        if any(type(x) is not int or not 1 <= abs(x) <= arity for x in row):
            raise ValueError("invalid signed literal")
        used.update(map(abs,row))
        lits = set(row)
        if any(-x in lits for x in lits):
            continue
        normalized = tuple(sorted(lits))
        if len(normalized)>3:
            raise ValueError("normalized clause exceeds width three")
        if normalized not in seen:
            seen.add(normalized)
            (background if len(normalized)<=2 else residual).append((index,normalized))
    b_ids = tuple(i for i,_ in background)
    binary = tuple(row for _,row in background)
    used = tuple(sorted(used))
    origin = _model(binary)
    if origin is None:
        return BackgroundBasis(raw,used,False,(),b_ids,binary,(),())

    def translated(row):
        return tuple(-x if abs(x) in origin else x for x in row)

    edges = {v:set() for v in used}
    conflicts = []
    for row in binary:
        lits = translated(row)
        pos = [x for x in lits if x>0]
        neg = [-x for x in lits if x<0]
        if not neg:
            raise AssertionError("zero must satisfy translated background")
        if pos:
            edges[neg[0]].add(pos[0])
        else:
            conflicts.append(frozenset(neg))
    # Encode closures with local integer masks, never using raw IDs as offsets.
    slot = {v:i for i,v in enumerate(used)}
    forbidden = [sum(1 << slot[v] for v in c) for c in conflicts]
    closures = {}
    for v in {abs(x) for _,row in residual for x in row}:
        reached, stack = {v}, [v]
        while stack:
            fresh = edges[stack.pop()] - reached
            reached.update(fresh)
            stack.extend(fresh)
        closures[v] = sum(1 << slot[u] for u in reached)

    # A closure key represents its principal-upset indicator on feasible
    # translated assignments. The evaluation matrix on feasible closure keys
    # ordered by inclusion is unit triangular.
    pivots, selected = {}, []
    for index,row in residual:
        fixed = 0
        optional = []
        for lit in translated(row):
            if lit < 0:
                fixed |= closures[-lit]
            else:
                optional.append(closures[lit])
        terms = set()
        for subset in range(1 << len(optional)):
            key = fixed
            for j,extra in enumerate(optional):
                if subset & (1 << j):
                    key |= extra
            if not any(key & f == f for f in forbidden):
                terms.symmetric_difference_update((key,))
        while terms:
            pivot = max(terms)
            if pivot not in pivots:
                pivots[pivot] = terms
                selected.append((index,row))
                break
            terms ^= pivots[pivot]
    return BackgroundBasis(raw,used,True,tuple(sorted(origin)),b_ids,binary,
                           tuple(i for i,_ in selected),tuple(row for _,row in selected))


def _greedy_hits(rows):
    remaining = [frozenset(map(abs,row)) for row in rows]
    hits = []
    while remaining:
        frequency = Counter(v for row in remaining for v in row)
        chosen = min(frequency, key=lambda v: (-frequency[v], v))
        hits.append(chosen)
        remaining = [row for row in remaining if chosen not in row]
    return tuple(hits)


def solve(arity,clauses,*,max_branches=None):
    """Enumerate hitting-set masks, LSB-first in greedy selection order."""
    if max_branches is not None and (type(max_branches) is not int or max_branches<0):
        raise ValueError("invalid branch cap")
    basis = project(arity,clauses)
    hits = _greedy_hits(basis.clauses)
    stats = dict(rank=basis.rank, hit_variables=hits)
    branches = 0
    if not basis.feasible:
        return dict(status="zero",branches=0,**stats)
    model = set(basis.origin_true_ids)
    if hits:
        for mask in range(1 << len(hits)):
            if max_branches is not None and branches >= max_branches:
                return dict(status="unknown",reason="branch_budget",available=max_branches,
                            required=branches+1,branches=branches,**stats)
            branches += 1
            pins = {v if mask & (1 << j) else -v for j,v in enumerate(hits)}
            reduced = [tuple(x for x in row if -x not in pins) for row in basis.clauses
                       if not any(x in pins for x in row)]
            model = _model((*basis.background,*reduced), sorted(pins))
            if model is not None:
                break
        else:
            return dict(status="zero",branches=branches,**stats)
    if not all(any((abs(x) in model) == (x>0) for x in row) for row in basis.original):
        raise AssertionError("invalid original source witness")
    return dict(status="nonzero",branches=branches,true_ids=tuple(sorted(model)),**stats)
