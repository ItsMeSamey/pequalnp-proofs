"""Parity on a half-field multiplicative coset of a centered alternating Dickson matrix."""
from additive_slope_prefix import _det


def parity(f, matrix, representative):
    d = f.m
    if d % 2 or not representative:
        raise ValueError("need even degree and nonzero coset representative")
    if len(matrix) != d or any(len(row) != d for row in matrix):
        raise ValueError("invalid square matrix")
    if any(matrix[i][i] or any(matrix[i][j] != matrix[j][i] for j in range(i))
           for i in range(d)):
        raise ValueError("matrix must be alternating")
    a = d//2
    qpower = representative
    for _ in range(a):
        qpower = f.mul(qpower,qpower)
    z = f.mul(qpower,f.inverse(representative))
    roots = [f.sqrt(z)]
    for _ in range(1,a):
        roots.append(f.mul(roots[-1],roots[-1]))
    small = [[matrix[i+a][j+a] ^ f.mul(roots[i],matrix[i][j+a])
              ^ f.mul(roots[j],matrix[i+a][j])
              ^ f.mul(f.mul(roots[i],roots[j]),matrix[i][j])
              for j in range(a)] for i in range(a)]
    val = 1 ^ _det(f,[r[:] for r in matrix]) ^ f.mul(z,_det(f,small))
    return val


def find_columns(f, columns):
    """Original-coordinate witness, polynomial space for all even degrees."""
    from additive_safe_slope import _safe
    from additive_slope_prefix import dickson
    from quadratic_target import apply_basis
    from product_slack import linearized
    from selfadjoint_coset_sampler import _center, subfield_basis
    if f.m % 2:
        raise ValueError("even degree required")
    center = _center(f, columns)
    if _safe(f, columns, center):
        return center
    coeffs = list(linearized(f, columns))
    coeffs[0] ^= center
    matrix = dickson(f, coeffs)
    basis = subfield_basis(f)
    theta = next(1<<i for i in range(f.m) if
                 _outside_half_field(f,1<<i))
    size = 1 << len(basis)
    for i in range(-1,size):
        rep = 1 if i < 0 else theta ^ apply_basis(basis,i)
        if parity(f,matrix,rep):
            for j in range(1,size):
                s = center ^ f.mul(rep,apply_basis(basis,j))
                if _safe(f,columns,s):
                    return s
            raise ArithmeticError("selected coset failed witness replay")
    raise ArithmeticError("no odd coset found")


def _outside_half_field(f,x):
    v = x
    for _ in range(f.m//2):
        v = f.mul(v,v)
    return v != x
