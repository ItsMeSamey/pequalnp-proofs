"""Clause-miss span, factored exact model count and sparse original witness.

IDs are signed and one-based. count=(mantissa, free_unused_exponent) means
mantissa * 2**free_unused_exponent, including all declared assignments. No
allocation depends on numerical arity. A budget unit is a tested assignment
or an IE subset, including inconsistent subsets and all witness-lifting calls.
Polynomial preprocessing is separate; no exponential table is materialized.
"""
from dataclasses import dataclass


def _echelon(words):
    pivots = {}
    for word in words:
        while word:
            j = word.bit_length()-1
            if j not in pivots:
                pivots[j] = word
                break
            word ^= pivots[j]
    return pivots


@dataclass(frozen=True)
class MissBasis:
    arity: int
    used: tuple
    original: tuple
    normalized: tuple
    indices: tuple

    @property
    def clauses(self):
        return tuple(self.normalized[j] for j in self.indices)


def project(arity, clauses):
    if type(arity) is not int or arity < 0:
        raise ValueError("invalid arity")
    original = tuple(tuple(row) for row in clauses)
    used, normalized = set(), set()
    for row in original:
        for x in row:
            if type(x) is not int or not 1 <= abs(x) <= arity:
                raise ValueError("invalid signed literal")
            used.add(abs(x))
        lits = set(row)
        if not any(-x in lits for x in lits):
            normalized.add(tuple(sorted(lits)))
    rows = tuple(sorted(normalized))
    kills = {}
    for j,row in enumerate(rows):
        for x in row:
            kills[x] = kills.get(x,0) | (1 << j)
    basis = [(1 << len(rows))-1]
    for v in sorted(used):
        if v not in kills and -v not in kills:
            continue
        basis = tuple(_echelon(word & ~kills.get(lit,0)
                               for word in basis for lit in (v,-v)).values())
    indices = tuple(sorted(_echelon(basis)))
    return MissBasis(arity,tuple(sorted(used)),original,rows,indices)


class _Budget(Exception):
    pass


def solve(arity, clauses, *, max_terms=None):
    if max_terms is not None and (type(max_terms) is not int or max_terms < 0):
        raise ValueError("invalid count budget")
    reduction = project(arity,clauses)
    row_basis = reduction.clauses
    names = sorted({abs(x) for row in row_basis for x in row})
    slots = {v:i for i,v in enumerate(names)}
    h,k = len(names),len(row_basis)
    free = arity-len(reduction.used)
    calls = 0
    mode = "enumerate" if (1 << h) <= (h+1)*(1 << k) else "inclusion_exclusion"

    def charge():
        nonlocal calls
        if max_terms is not None and calls >= max_terms:
            raise _Budget
        calls += 1

    # Misses require all negative variables true and all positive variables false.
    requirements = [(sum(1 << slots[-x] for x in row if x < 0),
                     sum(1 << slots[x] for x in row if x > 0)) for row in row_basis]

    def count(fixed_true, fixed_false):
        total = 0
        for subset in range(1 << k):
            charge()
            on,off = fixed_true,fixed_false
            active = subset
            while active and not on & off:
                low = active & -active
                need_on,need_off = requirements[low.bit_length()-1]
                on |= need_on
                off |= need_off
                active ^= low
            if not on & off:
                mass = 1 << (h-(on | off).bit_count())
                total += -mass if subset.bit_count() & 1 else mass
        return total

    model = 0
    try:
        if any(not row for row in row_basis):
            total = 0
        elif not row_basis:
            total = 1
        elif mode == "enumerate":
            total = 0
            for word in range(1 << h):
                charge()
                if all(on & ~word or off & word for on,off in requirements):
                    if total == 0:
                        model = word
                    total += 1
        else:
            total = count(0,0)
            if total:
                off = 0
                for j in range(h):
                    bit = 1 << j
                    if count(model,off | bit):
                        off |= bit
                    else:
                        model |= bit
    except _Budget:
        return dict(status="unknown",reason="count_budget",available=max_terms,
                    required=calls+1,terms=calls,mode=mode,rank=k)
    answer = dict(status="nonzero" if total else "zero",
                  count=(total << (len(reduction.used)-h),free),rank=k,terms=calls,mode=mode)
    if total:
        true = {v for j,v in enumerate(names) if model & (1 << j)}
        if not all(any((abs(x) in true) == (x>0) for x in row) for row in reduction.original):
            raise AssertionError("invalid original source witness")
        answer["true_ids"] = tuple(sorted(true))
    return answer
