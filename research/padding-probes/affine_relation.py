"""Affine hulls and equation solving for explicitly listed bit tuples."""
from monotone_affine_probe import _endpoint
from orbit_rado import insert


class NonAffine(ValueError):
    """The listed nonempty support omits a member of its affine hull."""


def _width(width):
    if type(width) is not int or width < 0:
        raise ValueError('expected nonnegative bit width')


def _fits(value, width):
    return type(value) is int and value >= 0 and value.bit_length() <= width


def _hull(points, width):
    _width(width)
    support = set()
    for point in points:
        if not _fits(point, width):
            raise ValueError('point outside bit cube')
        support.add(point)
    if not support:
        return None
    offset = min(support)
    pivots = {}
    for point in sorted(support):
        insert(pivots, point ^ offset, 0)
    # Each free coordinate generates one orthogonal normal. Higher pivots
    # depend on lower coordinates, so solve the row equations in ascending order.
    equations = []
    rows = sorted(pivots.items())
    for column in range(width):
        if column in pivots:
            continue
        normal = 1 << column
        for pivot, (row, _) in rows:
            if (row & normal).bit_count() & 1:
                normal |= 1 << pivot
        equations.append((normal, (normal & offset).bit_count() & 1))
    return tuple(equations), len(pivots), len(support)


def affine_hull(points, width):
    """Return (defining equations, dimension), or None on empty support."""
    hull = _hull(points, width)
    return None if hull is None else hull[:2]


def affine_equations(points, width):
    """Return defining equations for exact affine support, or None if empty."""
    hull = _hull(points, width)
    if hull is None:
        return None
    equations, dimension, size = hull
    if size != 1 << dimension:
        raise NonAffine('support is a proper subset of its affine hull')
    return equations


def solve_equations(width, equations):
    """Return a satisfying bit word with free bits zero, or None if inconsistent."""
    _width(width)

    def checked():
        for mask, rhs in equations:
            if not _fits(mask, width) or type(rhs) not in (int, bool) or rhs not in (0, 1):
                raise ValueError('invalid affine equation')
            yield mask, rhs

    return _endpoint(checked(), 0)
