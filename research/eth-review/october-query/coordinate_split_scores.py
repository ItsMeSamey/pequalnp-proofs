"""Recover a fixed prefix's physical violation histogram from canonical parity scores."""
from operator import index

from coordinate_split_cnf import evaluation_basis, split_masses


def recover_prefix(m, length, cap, score, *, max_calls, base=None):
    """cap counts distinct accepted words INCLUDING zero, if present.

    score(row) is an exact N(A;row) at one immutable prefix. Physical rows use
    zero-based indices, coefficient-one entries in order, then (0,0) padding.
    base optionally supplies already-paid N(A). With no clauses an unpadded
    empty row is the base query. max_calls counts actual new oracle calls.
    """
    m, length, cap, max_calls = map(index, (m, length, cap, max_calls))
    if min(m, length, cap, max_calls) < 0:
        raise ValueError("negative parameter")
    cache = {}
    calls = hits = max_order = 0

    def result(status, **extra):
        return dict(status=status, calls=calls, cache_hits=hits,
                    max_row_weight=max_order, **extra)

    if base is None:
        if not max_calls:
            return result("query_cap")
        base = index(score(((0, 0),)*length if m else ()))
        calls += 1
    else:
        base = index(base)
    if base < 0:
        raise ValueError("negative prefix count")
    if not base:
        return result("exact", histogram={}, count=0)
    if not cap:
        return result("support_overflow", certified_at_least=1)
    cache[0] = base
    live = {0: base}
    for j in range(m):
        words = list(live)
        basis = evaluation_basis(words, j)
        moments = []
        for mask in basis:
            scope = mask | (1 << j)
            weight = scope.bit_count()
            if weight > len(words).bit_length():
                raise ArithmeticError("graded basis exceeded its degree bound")
            if weight > length:
                return result("row_length", required=weight)
            total = 0
            subset = scope
            while True:
                if subset in cache:
                    hits += 1
                else:
                    if calls == max_calls:
                        return result("query_cap")
                    bits = subset
                    entries = []
                    while bits:
                        bit = bits & -bits
                        entries.append((bit.bit_length()-1, 1))
                        bits ^= bit
                    row = tuple(entries) + ((0, 0),)*(length-len(entries))
                    value = index(score(row))
                    calls += 1
                    if not 0 <= value <= base:
                        raise ValueError("score outside fixed-prefix range")
                    cache[subset] = value
                    max_order = max(max_order, len(entries))
                signed = 2*cache[subset]-base
                total += -signed if subset.bit_count()%2 else signed
                if not subset:
                    break
                subset = (subset-1) & scope
            moment, rem = divmod(total, 1 << weight)
            if rem:
                raise ValueError("nonintegral Boolean moment")
            moments.append(moment)
        ones = split_masses(words, basis, moments)
        updated = {}
        for word, one in zip(words, ones):
            zero = live[word]-one
            if min(zero, one) < 0:
                raise ValueError("negative split mass")
            if zero:
                updated[word] = zero
            if one:
                updated[word | (1 << j)] = one
        if len(updated) > cap:
            return result("support_overflow", certified_at_least=len(updated))
        live = updated
    return result("exact", histogram=live, count=live.get(0, 0))
