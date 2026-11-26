from itertools import product
from random import Random
from noncomplete_solver import parity, bits, search


def brute(rows, left, right):
    for x in range(1 << len(left)):
        active = list(bits(x))
        if sum(left[i] != 2 for i in active) % 2 != 1:
            continue
        share = sum(left[i] != 0 for i in active) % 2
        col = 0
        for i in active:
            col ^= rows[i]
        for y in range(1 << len(right)):
            if col & y or any(parity(rows[i]&y) for i in active):
                continue
            chosen = list(bits(y))
            if sum(right[j] != 2 for j in chosen) % 2 == 1 and sum(right[j] != 0 for j in chosen) % 2 == share:
                return True
    return False


def test(rows, left, right):
    if all(rows[i] >> j & 1 for i in range(len(left)) if left[i]!=2 for j in range(len(right)) if right[j]!=2):
        return 0
    assert (search(rows,left,right) is not None) == brute(rows,left,right)
    return 1


if __name__ == '__main__':
    count = 0
    for colors in product(range(2), repeat=4):
        for g in range(512):
            count += test([g >> (3*i) & 7 for i in range(3)],colors[:2]+(2,),colors[2:]+(2,))
    rng = Random(627)
    for _ in range(700):
        left = [rng.randrange(3) for _ in range(rng.randrange(2,7))]
        right = [rng.randrange(3) for _ in range(rng.randrange(2,7))]
        count += test([rng.getrandbits(len(right)) for _ in left],left,right)
    # Force the structural branch: all colored endpoints have opposing colors,
    # one missing block pair is fully shared-adjacent, square+isolate absent
    # because the universal colored neighborhoods are actual directed cuts.
    for _ in range(350):
        sl, sr = rng.randrange(2,5), rng.randrange(2,5)
        u, v = rng.randrange(1,3), rng.randrange(1,3)
        left, right = [0]*(1+u)+[2]*sl, [1]*(1+v)+[2]*sr
        coordL = sorted(rng.randrange(7) for _ in range(sl))
        coordR = sorted(rng.randrange(7) for _ in range(sr))
        leftcut = [rng.randrange(8) for _ in range(u)]
        rightcut = [rng.randrange(8) for _ in range(v)]
        rows = [((1<<len(right))-1)^1]
        for k in leftcut:
            rows.append((1<<(v+1))-1 | sum((p<k) << (1+v+j) for j,p in enumerate(coordR)))
        for p in coordL:
            rows.append(1 | sum((p>=k)<<(1+j) for j,k in enumerate(rightcut)) |
                        sum((p<q)<<(1+v+j) for j,q in enumerate(coordR)))
        count += test(rows,left,right)
    print("Checked",count,"noncomplete instances against exhaustive witness search.")
