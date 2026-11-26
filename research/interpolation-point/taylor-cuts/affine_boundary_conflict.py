"""One-sided conflict detector using original clause ANFs over GF(2)."""


def _violation(clause):
    """A monomial is the bit set of its variable indices; zero denotes one."""
    literals = set(clause)
    if any(not isinstance(l,int) or l==0 for l in literals):
        raise ValueError("expected nonzero signed variable indices")
    if any(-l in literals for l in literals):
        return set()
    negative = sum(1<<(abs(l)-1) for l in literals if l<0)
    row = {negative}
    for l in literals:
        if l>0:
            bit = 1<<(l-1)
            row |= {m|bit for m in row}
    return row


def _boundary_rows(rows, boundary_mask):
    pivots = {}
    retained = []
    for i,row in enumerate(rows):
        row = set(row)
        provenance = 1<<i
        while row:
            bad = [m for m in row if (m & ~boundary_mask) or m.bit_count()>1]
            if not bad:
                retained.append((row,provenance))
                break
            pivot = max(bad)
            if pivot not in pivots:
                pivots[pivot] = row,provenance
                break
            other,labels = pivots[pivot]
            row ^= other
            provenance ^= labels
    return retained


def find_conflict(left,right,boundary):
    """Return (left indices,right indices) deriving 1, else None.
    Inputs are sequences of clauses with signed, one-based literals.
    Each certificate index is zero-based in its respective input sequence.
    """
    variables = set(boundary)
    if any(not isinstance(i,int) or i<1 for i in variables):
        raise ValueError("invalid boundary variable")
    mask = sum(1<<(i-1) for i in variables)
    pivots = {}
    for side,clauses in enumerate((left,right)):
        for row,word in _boundary_rows(map(_violation,clauses),mask):
            labels = [0,0]
            labels[side] = word
            while row:
                pivot = max(row)
                if pivot==0:
                    return tuple(tuple(j for j in range(w.bit_length()) if w>>j&1)
                                 for w in labels)
                if pivot not in pivots:
                    pivots[pivot] = row,labels
                    break
                other,prior = pivots[pivot]
                row = row ^ other
                labels = [a^b for a,b in zip(labels,prior)]
    return None


def replay_conflict(left,right,certificate):
    """Recompute the XOR of source clause indicators, requiring exactly one."""
    if certificate is None or len(certificate)!=2:
        return False
    remainder = set()
    for clauses,indices in zip((left,right),certificate):
        for j in indices:
            if not isinstance(j,int) or not 0<=j<len(clauses):
                return False
            remainder ^= _violation(clauses[j])
    return remainder=={0}
