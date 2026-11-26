"""Minimum rank completion of guard-literal rows specified on nested future suffixes."""

def reduce_row(x, pivots):
    coeff = 0
    for p in sorted(pivots, reverse=True):
        if x >> p & 1:
            v,c = pivots[p]
            x ^= v
            coeff ^= c
    return x,coeff


def complete(n, indexed_masks):
    """Return basis rows V and coefficient rows U in original occurrence order.

    A row belonging to variable i specifies its coefficients strictly above i.
    """
    basis = []
    coeffs = [0] * len(indexed_masks)
    for j,(i,row) in sorted(enumerate(indexed_masks), key=lambda item:item[1][0]):
        suffix = ((1 << n)-1) ^ ((1 << (i+1))-1)
        pivots = {}
        for k,vector in enumerate(basis):
            reduced,used = reduce_row(vector & suffix, pivots)
            if reduced:
                pivots[reduced.bit_length()-1] = reduced, used ^ (1 << k)
        desired = row & suffix
        reduced,used = reduce_row(desired,pivots)
        if reduced:
            coeffs[j] = 1 << len(basis)
            basis.append(desired)
        else:
            coeffs[j] = used
    return basis,coeffs


def combine(basis, coeff):
    vector = 0
    for k,row in enumerate(basis):
        if coeff >> k & 1:
            vector ^= row
    return vector
