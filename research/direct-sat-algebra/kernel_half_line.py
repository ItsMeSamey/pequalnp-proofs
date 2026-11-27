"""Select an odd half-field line from a centered kernel vector."""
from additive_safe_slope import _safe
from commuting_spread import kernel_columns
from quadratic_target import apply_basis
from selfadjoint_coset_sampler import _center, subfield_basis


def selected_line(f, columns):
    if f.m % 2:
        raise ValueError("expected even binary degree")
    center = _center(f, columns)
    kernel = kernel_columns([v ^ f.mul(center,1<<i) for i,v in enumerate(columns)])
    if not kernel:
        return center, None
    x = kernel[0]
    return center, f.inverse(f.mul(x,x))


def find_columns(f, columns):
    center, scale = selected_line(f,columns)
    if scale is None:
        return center
    directions = [f.mul(scale,t) for t in subfield_basis(f)]
    for i in range(1, 1 << len(directions)):
        slope = center ^ apply_basis(directions,i)
        if _safe(f,columns,slope):
            return slope
    raise ArithmeticError("kernel-selected line contained no safe scalar")
