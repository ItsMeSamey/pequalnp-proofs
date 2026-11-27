"""Exact selected-support parity of six-site witnesses, excluding the universal pin."""
from itertools import combinations, product
from universal_pin_row_pair import physical, even


def run(a,b,dr,flags):
    d = len(dr)
    rows = physical(a,b,d,(*flags,False))
    off = 3+len(a)+len(b)
    for i,row in enumerate(dr):
        rows[off+i] |= row << off
    full = (1 << len(rows))-1
    if not even(rows,full):
        return None
    count = 0
    for i,j in product(range(len(a)),range(len(b))):
        core = 7 | (1 << (3+i)) | (1 << (3+len(a)+j))
        for u,v in combinations(range(d),2):
            count += even(rows,core | (1 << (off+u)) | (1 << (off+v)))
    g = sum((row.bit_count()%2) << i for i,row in enumerate(dr))
    lg = sum((((row & g).bit_count() + (g >> i & 1))%2) << i for i,row in enumerate(dr))
    s = 0
    for x in a:
        s ^= x
    assert count%2 == (1 ^ ((s & lg).bit_count()%2))
    return count


def graphs(n):
    pairs = list(combinations(range(n),2))
    for m in range(1 << len(pairs)):
        rows = [0]*n
        for j,(x,y) in enumerate(pairs):
            if m>>j&1:
                rows[x] |= 1 << y
                rows[y] |= 1 << x
        yield rows


def main():
    yes = 0
    for d in (0,2,4):
        for dr in graphs(d):
            for a,b in product(range(1<<d),repeat=2):
                yes += run([a],[b],dr,(0,0)) is not None
    from random import Random
    rng = Random(4542)
    for _ in range(3000):
        d = rng.choice((2,4,6))
        dr = [0]*d
        for i,j in combinations(range(d),2):
            if rng.randrange(2):
                dr[i] |= 1<<j
                dr[j] |= 1<<i
        a,b = [[rng.randrange(1<<d) for _ in range(rng.choice((1,3)))] for _ in range(2)]
        yes += run(a,b,dr,(rng.randrange(2),rng.randrange(2))) is not None
    for name,dr in [('P4',[2,5,10,4]),('P3+iso',[2,5,2,0]),('paw',[14,5,3,1])]:
        bad = [(x,y) for x,y in product(range(16),repeat=2)
               if run([x],[y],dr,(0,0)) == 0]
        print(name,'no local witness',bad)
    print('verified legal whole selections',yes)


if __name__ == '__main__':
    main()
