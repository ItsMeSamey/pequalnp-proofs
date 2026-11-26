"""Exact binary affine-flat avoidance via the squarefree clique border."""
from itertools import combinations
from affine_quadratic_span import _normalize, _eigenspace


class CliqueBudgetExceeded(ValueError):
    """The supplied clique budget was exceeded."""


def _bits(value):
    while value:
        bit = value & -value
        yield bit
        value ^= bit


def _quadratic_rules(n, flats):
    pairs = sorted((1 << i) | (1 << j) for i,j in combinations(range(n),2))
    monomials = [0] + [1 << i for i in range(n)] + pairs
    bases = {}
    for flat in flats:
        if len(flat) != 2:
            continue
        (a,u),(b,v) = flat
        u ^= 1
        v ^= 1
        linear = (a & b) ^ (b if u else 0) ^ (a if v else 0)
        row = (linear << 1) | (u & v)
        for j,pair in enumerate(pairs,n+1):
            lo = pair & -pair
            hi = pair ^ lo
            if (bool(a & lo) and bool(b & hi)) ^ (bool(b & lo) and bool(a & hi)):
                row |= 1 << j
        while row.bit_length() > n+1:
            j = row.bit_length()-1
            if j not in bases:
                bases[j] = row
                break
            row ^= bases[j]
    pivot_mask = sum(1<<j for j in bases)
    rules = {}
    for j in sorted(bases):
        rest = bases[j] ^ (1 << j)
        for bit in _bits(rest & pivot_mask):
            rest ^= bases[bit.bit_length()-1]
        bases[j] = (1 << j) | rest
        rules[monomials[j]] = tuple(monomials[bit.bit_length()-1] for bit in _bits(rest))
    return rules


def _cliques(n, rules, budget):
    neighbors = [(1<<n)-1 for _ in range(n)]
    for pair in rules:
        i,j = _bits(pair)
        neighbors[i.bit_length()-1] &= ~j
        neighbors[j.bit_length()-1] &= ~i
    cliques = []
    stack = [(0,(1<<n)-1)]
    while stack:
        mask,candidates = stack.pop()
        cliques.append(mask)
        if budget is not None and len(cliques)>budget:
            raise CliqueBudgetExceeded("number of cliques exceeds max_cliques")
        while candidates:
            bit = candidates & -candidates
            candidates ^= bit
            stack.append((mask | bit,candidates & neighbors[bit.bit_length()-1]))
    return cliques


def _multiplication(n, flats, budget):
    rules = _quadratic_rules(n,flats)
    cliques = _cliques(n,rules,budget)
    normal = {c:1<<j for j,c in enumerate(cliques)}
    parents = {}
    for c in cliques:
        for i in range(n):
            z = c | (1 << i)
            if z not in normal:
                parents.setdefault(z,(1<<i,c))
    for z in sorted(parents,key=lambda v:(v.bit_count(),v)):
        i,c = parents[z]
        v = next(v for v in _bits(c) if (i | v) in rules)
        q = c ^ v
        answer = 0
        for lower in rules[i | v]:
            if lower.bit_count() <= 1:
                answer ^= normal[q | lower]
                continue
            a,h = _bits(lower)
            for term in _bits(normal[q | a]):
                basis_mask = cliques[term.bit_length()-1]
                answer ^= normal[basis_mask | h]
        normal[z] = answer
    return cliques,[[normal[c | (1<<i)] for c in cliques] for i in range(n)]


def solve_border(n, flats, *, max_cliques=None):
    """Return (exact count, witness or None). The budget includes the empty clique."""
    if max_cliques is not None and (not isinstance(max_cliques,int) or max_cliques<0):
        raise ValueError("max_cliques must be a nonnegative integer")
    flats = _normalize(n,flats)
    if () in flats:
        return 0,None
    cliques,matrices = _multiplication(n,flats,max_cliques)
    layers = [(0,[1<<i for i in range(len(cliques))])]
    for i,matrix in enumerate(matrices):
        children = []
        for x,space in layers:
            for bit in (0,1):
                kernel = _eigenspace(space,matrix,bit)
                if kernel:
                    children.append((x | (bit<<i),kernel))
        layers = children
    answers = [x for x,_ in layers if all(any((x&m).bit_count()%2 != t for m,t in flat) for flat in flats)]
    return len(answers),next(iter(answers),None)
