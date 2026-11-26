"""Exact determinants of the two polarized mixed-cut blocks."""
from check_pair_rank import bareiss


def check(q):
    points = [(a, b, 1) for a in range(q) for b in range(q)]
    points += [(a, 1, 0) for a in range(q)] + [(1, 0, 0)]
    n = len(points)
    inc = [[sum(x*y for x, y in zip(p, line)) % q == 0 for line in points]
           for p in points]
    addresses = [(p, line) for p in range(n) for line in range(n)]
    for flag in (False, True):
        block = [(p, line) for p, line in addresses if inc[p][line] == flag]
        matrix = [[int(inc[p][j] != flag and inc[r][line] != flag)
                   for r, j in block] for p, line in block]
        expected = q ** (3*n) if flag else (q+1) * q ** (n*(n-1) - 2*q**3)
        assert abs(bareiss(matrix)) == expected
        print(f"q={q}, incident={flag}, exact {len(block)}-square block determinant passed")


if __name__ == "__main__":
    for order in (2, 3):
        check(order)
