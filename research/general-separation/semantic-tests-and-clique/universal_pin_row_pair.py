"""Three named sites p,q,z; z universal, p adjacent to A and q to B below z.

Sites are p=0,q=1,z=2 then A, B, D in order. A and B are completely
joined. Each group internally induces a clique or the empty graph.
Input row bits denote actual neighbors in D, with D positions starting at 0.
"""
from itertools import product
from random import Random


def solve(a_rows, b_rows, d_size, d_clique):
    """Return an original vertex mask, or None. Internal A/B edges are immaterial."""
    universe = (1 << d_size) - 1
    for i, left in enumerate(a_rows):
        for j, raw_right in enumerate(b_rows):
            right = raw_right ^ (universe if d_clique else 0)
            x = left & ~right
            y = right & ~left
            if x and y:
                first_d = 3 + len(a_rows) + len(b_rows)
                centers = (1 << (3+i)) | (1 << (3+len(a_rows)+j))
                return 7 | centers | (((x & -x) | (y & -y)) << first_d)
    return None


def physical(a, b, d, cliques):
    start = 3 + len(a) + len(b)
    rows = [0] * (start+d)
    def join(i, j):
        rows[i] |= 1 << j
        rows[j] |= 1 << i
    groups = [range(3, 3+len(a)), range(3+len(a), start), range(start, start+d)]
    for i in range(len(rows)):
        if i != 2:
            join(i, 2)
    for group, clique in zip(groups, cliques):
        if clique:
            for i in group:
                for j in group:
                    if j > i:
                        join(i, j)
    for i in groups[0]:
        join(0, i)
        for j in groups[1]:
            join(i, j)
    for j in groups[1]:
        join(1, j)
    for i, mask in enumerate((*a,*b), 3):
        for j in range(d):
            if mask >> j & 1:
                join(i, start+j)
    return rows


def even(rows, w):
    return all((row & w).bit_count() % 2 == 0 for i,row in enumerate(rows) if w >> i & 1)


def compare(a, b, d, cliques):
    rows = physical(a, b, d, cliques)
    w = solve(a, b, d, cliques[2])
    if w is not None:
        assert w & 7 == 7 and even(rows, w)
    assert (w is not None) == any(even(rows, raw) for raw in range(7, 1 << len(rows), 8))


def main():
    total = 0
    for na, nb, d in product(range(3), range(3), range(4)):
        for masks in product(range(1 << d), repeat=na+nb):
            for flags in product((False, True), repeat=3):
                compare(masks[:na], masks[na:], d, flags)
                total += 1
    rng = Random(14093)
    for _ in range(80):
        d = rng.randint(2, 6)
        a,b = [[rng.randrange(1 << d) for _ in range(rng.randint(1,4))] for _ in range(2)]
        compare(a,b,d,[rng.getrandbits(1) for _ in range(3)])
    for d in (8,32,128):
        a = [1 << i for i in range(d)]
        for clique in (False,True):
            for yes, transformed in ((False,(1 << d)-1), (True,1)):
                b = [transformed ^ (((1 << d)-1) if clique else 0)]
                w = solve(a,b,d,clique)
                assert (w is not None) == yes
                if yes:
                    assert even(physical(a,b,d,(True,False,clique)), w)
    print(total, 'exhaustive; 80 seeded; 12 identity-submatrix controls')


if __name__ == '__main__':
    main()
