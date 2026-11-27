"""Lower-order vertical separation certificates for the first six fixed roots."""
from collections import deque
from itertools import combinations


def _insert(basis, vector):
    while vector:
        pivot = vector.bit_length()
        if pivot not in basis:
            basis[pivot] = vector
            return True
        vector ^= basis[pivot]
    return False


def _basis(columns, positions):
    basis = {}
    for i in positions:
        _insert(basis, columns[i])
    return basis


def _independent(columns, base, indices):
    extension = base.copy()
    return all(_insert(extension, columns[i]) for i in indices)


def _valid(columns, stop):
    return (type(stop) is int and 0 <= stop <= 3 and len(columns) >= 6
            and all(type(v) is int and v >= 0 for v in columns))


def _problems(columns, stop):
    roots, free = tuple(range(6)), tuple(range(6, len(columns)))
    root_basis = _basis(columns, roots)
    rank = len(_basis(columns, range(len(columns))))
    for k in range(stop):
        for y in combinations(free, k+1):
            right = _basis(columns, y)
            if len(right) <= k:
                continue
            available = tuple(i for i in free if i not in y)
            need = max(0, k+1-len(root_basis))
            for extra in combinations(available, need):
                left = _basis(columns, roots+extra)
                if len(left) <= k:
                    continue
                # For every partition extending these anchors, each side's
                # rank increases by at least its share of a common independent
                # set of the contractions. A total rank sum > rank(E)+k
                # therefore rules out every such partition.
                required = max(0, rank+k+1-len(left)-len(right))
                yield left, right, tuple(i for i in available if i not in extra), required


def _witness(columns, left, right, free, required):
    chosen = set()
    while len(chosen) < required:
        outside = [i for i in free if i not in chosen]
        starts = [i for i in outside if _independent(columns, left, (*chosen,i))]
        ends = {i for i in outside if _independent(columns, right, (*chosen,i))}
        parent = dict.fromkeys(starts)
        queue = deque(starts)
        while queue:
            i = queue.popleft()
            if i in ends:
                while i is not None:
                    chosen.symmetric_difference_update((i,))
                    i = parent[i]
                break
            if i in chosen:
                neighbors = (j for j in outside if j not in parent and
                             _independent(columns, left, (*(chosen-{i}),j)))
            else:
                neighbors = (j for j in sorted(chosen) if j not in parent and
                             _independent(columns, right, (*(chosen-{j}),i)))
            for j in neighbors:
                parent[j] = i
                queue.append(j)
        else:
            return None
    return sorted(chosen)


def make_min_proof(columns, stop_order):
    """Return a JSON-compatible ordered witness list, or None on obstruction."""
    if not _valid(columns, stop_order):
        raise ValueError("expected six fixed roots and stop order in 0..3")
    proof = []
    for left,right,free,required in _problems(columns, stop_order):
        witness = _witness(columns,left,right,free,required)
        if witness is None:
            return None
        proof.append(witness)
    return proof


def check_min_proof(columns, stop_order, proof):
    """Check polynomially many explicit lower bounds using only GF(2) rank."""
    if not _valid(columns, stop_order) or not isinstance(proof,(list,tuple)):
        return False
    count = 0
    for left,right,free,required in _problems(columns, stop_order):
        if count == len(proof):
            return False
        w = proof[count]
        if (not isinstance(w,(list,tuple)) or len(w) != required or
                any(type(i) is not int for i in w) or not set(w)<=set(free) or
                not _independent(columns,left,w) or not _independent(columns,right,w)):
            return False
        count += 1
    return count == len(proof)
