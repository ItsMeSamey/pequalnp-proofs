"""Principal pivot on only the first even segment of the free part of a cycle."""
from diagonal_pin_cube_check import mv, reduce_rows


def check(t):
    n = 4*t + 3
    all_bits = (1 << n) - 1
    free = all_bits ^ 7
    first = ((1 << (2*t)) - 1) << 3
    second = free ^ first
    A = [(1 << ((i-1) % n)) | (1 << ((i+1) % n)) for i in range(n)]
    basis = {}
    for i in range(n):
        x = 1 << i
        y = mv(A, x)
        new_x = (x & ~first) | (y & first)
        new_y = (y & ~first) | (x & first)
        while new_x and new_x.bit_length()-1 in basis:
            left, right = basis[new_x.bit_length()-1]
            new_x ^= left
            new_y ^= right
        assert new_x
        basis[new_x.bit_length()-1] = new_x, new_y
    B = []
    for i in range(n):
        left, right = 1 << i, 0
        while left:
            row, image = basis[left.bit_length()-1]
            left ^= row
            right ^= image
        B.append(right)
    assert all(mv(B, 1 << i) == B[i] for i in range(n))
    assert len(reduce_rows(row & free for row in B[3:])) == 4*t
    assert mv(B, 7 | second) == first
    if t <= 2:
        for matrix, want in ((A, all_bits), (B, 7 | second)):
            witnesses = [x for x in range(7, 1 << n, 8) if not x & mv(matrix, x)]
            assert witnesses == [want]


if __name__ == "__main__":
    for t in range(1, 9):
        check(t)
    print("Eight partial pivots, two exhaustive uniqueness comparisons passed.")
