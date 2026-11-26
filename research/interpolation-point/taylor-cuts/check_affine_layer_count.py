"""Independent cube enumeration including basis changes, offsets and unused bits."""
from itertools import product
from random import Random

from affine_layer_count import count_layer


def check(n, pairs, complement, flats):
    accepted = [x for x in range(1 << n)
                if all(((p & x).bit_count() % 2, (q & x).bit_count() % 2) != (a,b)
                       for p,q,a,b in flats)]
    result = count_layer(n, pairs, complement, flats)
    if result is None:
        return False
    count, witness = result
    assert count == len(accepted) and (witness in accepted if count else witness is None)
    return True


def main():
    rng = Random(1771)
    assert check(0, [], [], [])
    for mask in range(16):
        flats = [(3,6,a,b) for a,b in product(range(2), repeat=2) if mask >> (2*a+b) & 1]
        assert check(5, [(3,6)], [8], flats)
    passed = failed = 0
    for case in range(320):
        n = rng.randrange(2, 9)
        dim = rng.randrange(2,n+1)
        basis = [1 << i for i in range(n)]
        for _ in range(4*n):
            i,j = rng.sample(range(n),2)
            basis[i] ^= basis[j]
        r = rng.randrange(dim//2+1)
        normals = [0]
        for v in basis[:dim]:
            normals += [p ^ v for p in normals]
        flats = [(*rng.sample(normals[1:],2), rng.randrange(2),rng.randrange(2))
                 for _ in range(rng.randrange(16))]
        pairs = list(zip(basis[:2*r:2],basis[1:2*r:2]))
        if check(n,pairs,basis[2*r:dim],flats):
            passed += 1
        else:
            failed += 1
    for bad in [((1,1,0,1),), ((1,4,0,1),), ((1,2,0,2),)]:
        try:
            count_layer(3,[(1,2)],[],bad)
        except ValueError:
            continue
        raise AssertionError("invalid flat accepted")
    print(f"17 fixed and {passed} recognized random counts/witnesses matched; {failed} random recognition rejections")


if __name__ == "__main__":
    main()
