"""Decode additive rank drift on a binary subspace of K^d.

recover(field,d,basis,values,r) returns a Fit or None. Inputs to the map are
packed d chunks, low chunk first; values[i] is the image of basis[i].
Requires m > codim(W)+2*r+1, so the nearest rank-r fit is unique.
"""
from dataclasses import dataclass
from quadratic_centroid import independent


@dataclass(frozen=True)
class Fit:
    squares: tuple
    linear: tuple
    residual: tuple
    drift_basis: tuple


def coordinates(field, d, x):
    return tuple((x >> (j*field.m)) & (field.size-1) for j in range(d))


def frob_powers(field, x, last):
    values = [x]
    for _ in range(last):
        values.append(field.mul(values[-1],values[-1]))
    return values


def field_solve(field, rows, width):
    """Solve the supplied field-linear equations; set free variables to zero."""
    pivots = {}
    for left, right in rows:
        v = [*left, right]
        for j in sorted(pivots):
            c = v[j]
            if c:
                v = [a ^ field.mul(c,b) for a,b in zip(v,pivots[j])]
        j = next((j for j in range(width) if v[j]), None)
        if j is None:
            if v[-1]:
                return None
        else:
            inverse = field.inverse(v[j])
            pivots[j] = [field.mul(a,inverse) for a in v]
    result = [0]*width
    for j in sorted(pivots, reverse=True):
        row = pivots[j]
        x = row[-1]
        for k in range(j+1,width):
            x ^= field.mul(row[k],result[k])
        result[j] = x
    return result


def apply_fit(field, squares, linear, x):
    value = 0
    for v,a,b in zip(coordinates(field,len(squares),x),squares,linear):
        value ^= field.mul(a,field.mul(v,v)) ^ field.mul(b,v)
    return value


def recover(field, d, basis, values, r):
    basis, values = tuple(basis), tuple(values)
    if d < 1 or r < 0 or len(values)!=len(basis):
        raise ValueError("invalid dimension, radius or data length")
    m = field.m
    if any(not 0 <= x < 1 << (m*d) for x in basis) or any(not 0 <= y < field.size for y in values):
        raise ValueError("point or output outside field coordinates")
    if len(independent(basis))!=len(basis):
        raise ValueError("domain generators must be binary independent")
    h = m*d-len(basis)
    if m <= h+2*r+1:
        raise ValueError("uniqueness radius requires m > h+2*r+1")
    # Unknowns: r lower coefficients of monic Lambda, followed by d blocks
    # of r+2 coefficients for N_i. The binary basis equations suffice since
    # every evaluated polynomial here is additive.
    def equations():
        for x,y in zip(basis,values):
            ys = frob_powers(field,y,r)
            row = ys[:-1]
            for v in coordinates(field,d,x):
                row.extend(frob_powers(field,v,r+1))
            yield row,ys[-1]
    result = field_solve(field,equations(),r+d*(r+2))
    if result is None:
        return None
    locator = result[:r] + [1]
    squares, linear = [], []
    def unpower(value):
        for _ in range(r):
            value = field.sqrt(value)
        return value
    for i in range(d):
        start = r+i*(r+2)
        coeff = result[start:start+r+2]
        a = unpower(coeff[-1])
        ap = frob_powers(field,a,r)
        b = unpower(coeff[r] ^ (field.mul(locator[r-1],ap[r-1]) if r else 0))
        bp = frob_powers(field,b,r)
        reconstructed = [0]*(r+2)
        for j,z in enumerate(locator):
            reconstructed[j] ^= field.mul(z,bp[j])
            reconstructed[j+1] ^= field.mul(z,ap[j])
        if reconstructed != coeff:
            return None
        squares.append(a)
        linear.append(b)
    residual = tuple(y ^ apply_fit(field,squares,linear,x) for x,y in zip(basis,values))
    image = independent(residual)
    if len(image) > r:
        return None
    return Fit(tuple(squares),tuple(linear),residual,image)


def check():
    from punctured_witness import BinaryField
    from quadratic_target import affine_domain
    from random import Random
    rng = Random(614)
    count = 0
    for modulus in (67, 131):
        field = BinaryField(modulus)
        m = field.m
        for d in (1,2,3):
            n = m*d
            for h in (0,1):
                normals = ()
                while len(normals) < h:
                    normals = independent((*normals,rng.randrange(1<<n)))
                W = affine_domain(n,((row,0) for row in normals))[1]
                # Mix the supplied W basis so it need not expose single-axis vectors.
                for _ in range(3*len(W)):
                    i,j = rng.sample(range(len(W)),2)
                    W[i] ^= W[j]
                a,b = [rng.choices(range(field.size),k=d) for _ in range(2)]
                exact = [apply_fit(field,a,b,x) for x in W]
                trials = [(0,0),(1,0),(1,1),(1,2)]
                if m > h+5:
                    trials.extend([(2,0),(2,1),(2,2)])
                for r,depth in trials:
                    drift = [rng.randrange(1,field.size)]
                    while len(drift)<2:
                        y = rng.randrange(1,field.size)
                        if y!=drift[0]:
                            drift.append(y)
                    faults = [0]*len(W)
                    for j in range(depth):
                        faults[j]=drift[j]
                    values = [y^e for y,e in zip(exact,faults)]
                    fit = recover(field,d,W,values,r)
                    if depth>r:
                        # Alternative codewords have rank distance >=m-h-1>3.
                        assert fit is None
                    else:
                        assert (fit.squares,fit.linear,fit.residual)==(tuple(a),tuple(b),tuple(faults))
                    count += 1
    print(f"{count} mixed-basis rank-drift recovery and rejection cases passed")


if __name__ == "__main__":
    check()
