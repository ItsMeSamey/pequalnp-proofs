"""Compare the recognizer to literal enumeration over 2-bit vectors."""
from itertools import product
from random import Random

from affine_projective_layer import recognize


def valid(matrix, left, right):
    for row, a in zip(matrix,left):
        for block,b in zip(row,right):
            # Independent multiplication using four binary matrix entries.
            c = 0
            for i in range(2):
                for j in range(2):
                    c ^= (((block >> (2*j+i)) & 1) & ((a>>j)&1)) << i
            if c and c != b:
                return False
    return True


def check(matrix,nc):
    nr = len(matrix)
    brute = any(valid(matrix,vec[:nr],vec[nr:]) for vec in product((1,2,3),repeat=nr+nc))
    got = recognize(matrix,nc)
    assert (got is not None) == brute, matrix
    if got is not None:
        left,right = got
        assert len(left)==nr and len(right)==nc and all(x in (1,2,3) for x in left+right)
        assert valid(matrix,left,right), (matrix,got)
    return int(brute)


if __name__ == '__main__':
    rng = Random(271828)
    for nr,nc in [(0,0),(0,2),(2,0),(1,1),(1,2),(2,1),(2,2),(3,4)]:
        if (nr,nc) in [(2,2),(3,4)]:
            # Identity around three sides and a fixed-point-free map on the fourth.
            special = [9 if i == 0 or j == 0 else 14 for i in range(nr) for j in range(nc)]
            cases = [special] + [rng.choices(range(16),k=nr*nc) for _ in range(1024 if nr==2 else 128)]
        else:
            cases = product(range(16),repeat=nr*nc)
        total = yes = 0
        for case in cases:
            matrix = [case[i*nc:(i+1)*nc] for i in range(nr)]
            total += 1
            yes += check(matrix,nc)
        print(nr,nc,total,yes,total-yes)


def exhaust_two_by_two(normalize_first=True):
    """Use 81-bit exact truth tables. With normalization, first-block frames
    put it in rank form, inducing bijections on the other three free blocks.
    Their 12,288 tests represent 65,536 arrays: 65,104 SAT and 432 UNSAT.
    """
    assignments = list(product((1,2,3),repeat=4))
    masks = []
    for i,j in product(range(2),repeat=2):
        site = []
        for block in range(16):
            mask = 0
            for k,v in enumerate(assignments):
                if valid([[block]],[v[i]],[v[2+j]]):
                    mask |= 1 << k
            site.append(mask)
        masks.append(site)
    yes = 0
    representatives = {0: 1, 1: 9, 9: 6} if normalize_first else dict.fromkeys(range(16), 1)
    for a,b,c,d in product(representatives,range(16),range(16),range(16)):
        truth = masks[0][a] & masks[1][b] & masks[2][c] & masks[3][d]
        matrix = [[a,b],[c,d]]
        got = recognize(matrix,2)
        assert bool(truth) == (got is not None), matrix
        if got is not None:
            left,right = got
            k = 0
            for x in left+right:
                assert 1 <= x <= 3
                k = 3*k+x-1
            assert truth & (1 << k), (matrix,got)
            yes += representatives[a]
    print("2x2 cases/checks/SAT/UNSAT",16**4,len(representatives)*16**3,yes,16**4-yes)
