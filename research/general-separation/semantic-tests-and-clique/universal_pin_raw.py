"""Recognize and solve a universal-pin graph from raw labelled adjacency masks.

solve_raw(rows,pins) returns ('YES', original witness mask), ('NO',None),
or ('UNKNOWN',None). Malformed graphs raise ValueError.
"""
from itertools import combinations
from random import Random
from universal_pin_row_pair import physical, even, solve


def solve_raw(rows, pins):
    n = len(rows)
    full = (1 << n) - 1
    if len(pins) != 3 or any(type(i) is not int or not 0 <= i < n for i in pins):
        raise ValueError('three valid pin indices required')
    if len(set(pins)) != 3:
        raise ValueError('pin indices must be distinct')
    if any(type(r) is not int or not 0 <= r <= full or r >> i & 1
           for i,r in enumerate(rows)):
        raise ValueError('invalid adjacency row')
    if any((rows[i] >> j ^ rows[j] >> i) & 1 for i,j in combinations(range(n),2)):
        raise ValueError('asymmetric adjacency')
    pinmask = sum(1 << i for i in pins)
    for z in pins:
        if rows[z] != full ^ (1 << z):
            continue
        p,q = [i for i in pins if i != z]
        if rows[p] >> q & 1:
            return 'YES', pinmask
        free = [i for i in range(n) if not pinmask >> i & 1]
        if not (rows[p] & ~pinmask) or not (rows[q] & ~pinmask):
            return 'NO', None
        a,b,d = [],[],[]
        common = False
        for i in free:
            left = rows[p] >> i & 1
            right = rows[q] >> i & 1
            if left and right:
                common = True
            elif left:
                a.append(i)
            elif right:
                b.append(i)
            else:
                d.append(i)
        for i in a:
            for j in b:
                if not rows[i] >> j & 1:
                    return 'YES', pinmask | 1 << i | 1 << j
        if common:
            continue
        def internals(group):
            return {rows[i] >> j & 1 for i,j in combinations(group,2)}
        flags = list(map(internals,(a,b,d)))
        if any(len(flag) > 1 for flag in flags):
            continue
        def masks(group):
            return [sum((rows[i] >> j & 1) << k for k,j in enumerate(d)) for i in group]
        w = solve(masks(a),masks(b),len(d),1 in flags[2])
        if w is None:
            return 'NO', None
        ids = [p,q,z,*a,*b,*d]
        return 'YES', sum(1 << i for j,i in enumerate(ids) if w >> j & 1)
    return 'UNKNOWN', None


def self_test():
    rng = Random(71485)
    for _ in range(240):
        size = rng.randrange(5)
        a,b = [[rng.randrange(1 << size) for _ in range(rng.randrange(4))] for _ in range(2)]
        rows = physical(a,b,size,[rng.randrange(2) for _ in range(3)])
        ids = list(range(len(rows)))
        rng.shuffle(ids)
        permuted = [0]*len(rows)
        for i,row in enumerate(rows):
            permuted[ids[i]] = sum(1 << ids[j] for j in range(len(rows)) if row >> j & 1)
        pins = ids[:3]
        rng.shuffle(pins)
        status,w = solve_raw(permuted,pins)
        exists = any(even(rows,s) for s in range(7,1 << len(rows),8))
        assert status == ('YES' if exists else 'NO')
        if exists:
            assert even(permuted,w) and all(w >> i & 1 for i in pins)
    rows = physical([1,3,0],[1],2,(False,False,False))
    rows[4] |= 1 << 5
    rows[5] |= 1 << 4
    assert even(rows,(1 << 9)-1) and solve_raw(rows,[0,1,2]) == ('UNKNOWN',None)
    assert solve_raw([14,13,3,3],[0,1,2]) == ('YES',7)
    assert solve_raw([0,0,0],[0,1,2]) == ('UNKNOWN',None)
    for rows,pins in [([0,0,0],[1,1,2]),([2,0,0],[0,1,2]),([0,0,8],[0,1,2]),
                      ([0,0,0],[0,True,2]),([1,0,0],[0,1,2])]:
        try:
            solve_raw(rows,pins)
        except ValueError:
            continue
        raise AssertionError((rows,pins))
    print('240 permutations; multiple universal pins, hidden YES, declines and malformed inputs passed')


if __name__ == '__main__':
    self_test()
