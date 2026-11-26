"""Deterministic quotient-type search for supplied balanced filling columns over GF(2).

Vectors are nonnegative integer bit masks. Each ordinary occurrence is a pair
(primal_vector, label_mask); equal columns can have distinct occurrence indices.
"""
from itertools import combinations


def bits(mask):
    while mask:
        one = mask & -mask
        yield one.bit_length() - 1
        mask ^= one


def parity(x):
    return x.bit_count() % 2


def basis(columns):
    """Highest-bit pivots, with masks tracing rows to original occurrences."""
    rows = {}
    for i, value in enumerate(columns):
        trace = 1 << i
        while value:
            pivot = value.bit_length()-1
            if pivot not in rows:
                rows[pivot] = value, trace
                break
            row, change = rows[pivot]
            value ^= row
            trace ^= change
    return rows


def reduce_with_trace(value, rows):
    trace = 0
    # Eliminate every pivot coordinate even when a larger free coordinate is set.
    for pivot in sorted(rows, reverse=True):
        if value >> pivot & 1:
            row, change = rows[pivot]
            value ^= row
            trace ^= change
    return value, trace


def affine_count(dimension, tests):
    rows = {}
    for mask, rhs in tests:
        while mask:
            pivot = mask.bit_length()-1
            if pivot not in rows:
                rows[pivot] = mask, rhs
                break
            v, b = rows[pivot]
            mask ^= v
            rhs ^= b
        else:
            if rhs:
                return 0
    return 1 << (dimension-len(rows))


def count_outside(dimension, tests, bad):
    """Exact count outside the union of affine flats; bad[k] defines a flat."""
    count = 0
    for sub in range(1 << len(bad)):
        stacked = tests.copy()
        for k in bits(sub):
            stacked.extend(bad[k])
        term = affine_count(dimension, stacked)
        count += -term if parity(sub) else term
    return count


def solve(rank, labels, ordinary, fillers, t, target=0, root_label=0, moments=(), dual_tests=(), s=None):
    """Return (dual covector, mask of ordinary occurrences) or None.

    The lift is V plus 'labels' coordinate bits. In addition to d(t)=0 and
    optional d(s)=1, enforce every (vector,rhs) in dual_tests. The returned
    ordinary mask has primal sum t, is annihilated occurrencewise by d, and
    has label sum target XOR root_label XOR (moments applied to d).
    An empty moments argument supplies zero rows.

    'fillers' lists ordinary indices. Its span W must satisfy the promised
    filling property for every d; arbitrary recognition is not performed.
    """
    if rank < 0 or labels < 0:
        raise ValueError("dimensions must be nonnegative")
    ordinary, fillers, moments = list(ordinary), list(fillers), list(moments)
    if not moments:
        moments = [0]*labels
    tests = list(dual_tests) + [(t,0)] + ([(s,1)] if s is not None else [])
    if (len(moments)!=labels or any(not 0<=m<1<<rank for m in moments)
        or any(not 0<=m<1<<rank or b not in (0,1) for m,b in tests)
        or any(not 0<=v<1<<rank or not 0<=w<1<<labels for v,w in ordinary)
        or any(not 0<=w<1<<labels for w in (target,root_label))
        or any(not 0<=i<len(ordinary) for i in fillers)):
        raise ValueError("malformed vector, dimension or occurrence index")
    lifted = [v | (lab<<rank) for v,lab in ordinary]
    W = basis(lifted[i] for i in fillers)
    def project(v):
        return reduce_with_trace(v,W)[0]
    buckets = {}
    for i,a in enumerate(lifted):
        q=project(a)
        if q:
            buckets.setdefault(q,[]).append(i)
    # A quotient-valued affine equation T(d)=type_sum.
    offset = project(t | ((target^root_label)<<rank))
    columns = [project(sum(((m>>j)&1) << (rank+i) for i,m in enumerate(moments)))
               for j in range(rank)]
    equations = [sum(((v>>j)&1)<<i for i,v in enumerate(columns)) for j in range(rank+labels)]
    codim = rank+labels-len(W)
    for size in range(min(codim,len(buckets))+1):
        for family in combinations(buckets,size):
            if len(basis(family))!=size:
                continue
            rhs=offset
            for q in family:
                rhs ^= q
            fixed=tests+[(row,(rhs>>i)&1) for i,row in enumerate(equations)
                         if row or (rhs>>i)&1]
            bad=[[(v,1) for v in sorted({ordinary[i][0] for i in buckets[q]})] for q in family]
            if not count_outside(rank,fixed,bad):
                continue
            d=0
            for j in range(rank):
                bit=1<<j
                if count_outside(rank,fixed+[(bit,0)],bad):
                    fixed.append((bit,0))
                else:
                    fixed.append((bit,1))
                    d |= bit
            requested=target^root_label
            for i,m in enumerate(moments):
                requested ^= parity(m&d)<<i
            residual=t | (requested<<rank)
            selection=0
            for q in family:
                i=next(i for i in buckets[q] if not parity(ordinary[i][0]&d))
                selection ^= 1<<i
                residual ^= lifted[i]
            eligible=[i for i in fillers if not parity(ordinary[i][0]&d)]
            remain, trace=reduce_with_trace(residual,basis(lifted[i] for i in eligible))
            if remain:
                raise ValueError("supplied filler set failed its promised kernel-spanning property")
            for j in bits(trace):
                selection ^= 1<<eligible[j]
            return d,selection
    return None
