"""Three-pin decision on uniform exclusive sides and cluster/co-cluster neutral sites.

Use solve_raw(rows,pins) for original-label YES masks, certified NO, or UNKNOWN.
The universal_pin_raw dependency validates simple graphs and handles elementary cases.
"""
from itertools import combinations, product
from random import Random
from universal_pin_raw import solve_raw as row_pair
from universal_pin_row_pair import even, physical


def cluster(rows, sites, complement=False):
    for a,b,c in combinations(sites,3):
        edges = ((rows[a] >> b & 1) + (rows[b] >> c & 1) + (rows[c] >> a & 1))
        if edges == (1 if complement else 2):
            return False
    return True


def solve_raw(rows, pins):
    status, witness = row_pair(rows, pins)
    if status != 'UNKNOWN':
        return status, witness
    full = (1 << len(rows)) - 1
    for z in pins:
        if rows[z] != full ^ (1 << z):
            continue
        p,q = [i for i in pins if i != z]
        groups = [[],[],[],[]]
        for i in range(len(rows)):
            if i not in pins:
                groups[(rows[p] >> i & 1) + 2*(rows[q] >> i & 1)].append(i)
        d,a,b,common = groups
        if common:
            continue
        # The earlier solver already handled a missing A-B edge and adjacent pins.
        for x,y in product(a,b):
            for i,j in combinations(d,2):
                xi, xj = (rows[x] >> i) & 1, (rows[x] >> j) & 1
                yi, yj = (rows[y] >> i) & 1, (rows[y] >> j) & 1
                adjacent = (rows[i] >> j) & 1
                if xi != xj and yi != yj and (xi ^ yi ^ adjacent) == 1:
                    return 'YES', sum(1 << v for v in (p,q,z,x,y,i,j))
        uniform = all(len({rows[i] >> j & 1 for i,j in combinations(group,2)}) <= 1
                      for group in (a,b))
        if uniform and (cluster(rows,d) or cluster(rows,d,True)):
            return 'NO', None
    return 'UNKNOWN', None


def graph(a,b,dr,flags):
    rows = physical(a,b,len(dr),(*flags,False))
    off = len(rows)-len(dr)
    for i,row in enumerate(dr):
        rows[off+i] |= row << off
    return rows


def self_test():
    rng = Random(216430)
    counts = {}
    for _ in range(360):
        d = rng.randrange(1,7)
        parts = [rng.randrange(3) for _ in range(d)]
        flip = rng.randrange(2)
        dr = [sum(1 << j for j in range(d) if i != j and ((parts[i] == parts[j]) ^ flip))
              for i in range(d)]
        a,b = [[rng.randrange(1 << d) for _ in range(rng.randint(1,3))] for _ in range(2)]
        rows = graph(a,b,dr,[rng.randrange(2) for _ in range(2)])
        ids = list(range(len(rows)))
        rng.shuffle(ids)
        rr = [0]*len(rows)
        for i,row in enumerate(rows):
            rr[ids[i]] = sum(1 << ids[j] for j in range(len(rows)) if row >> j & 1)
        pins = ids[:3]
        rng.shuffle(pins)
        status,w = solve_raw(rr,pins)
        exists = any(even(rows,s) for s in range(7,1 << len(rows),8))
        assert status == ('YES' if exists else 'NO')
        if exists:
            assert even(rr,w) and all(w >> i & 1 for i in pins)
        counts[flip,status] = counts.get((flip,status),0)+1
    assert len(counts) == 4
    # All possible edges from two extra vertices to each other and to the four-site obstruction.
    for orig,ra,rb,fill in [([2,5,10,4],2,4,0),([2,5,2,0],1,11,2),
                            ([12,8,9,7],1,4,0)]:
        # Third graph is the complement of P3+iso; flip the B row, including both fillers.
        for extra in range(512):
            dr = orig[:] + [0,0]
            pairs = [(i,j) for j in (4,5) for i in range(j)]
            for bit,(i,j) in enumerate(pairs):
                if extra >> bit & 1:
                    dr[i] |= 1 << j
                    dr[j] |= 1 << i
            aa = ra | (48 if fill & 1 else 0)
            bb = rb | (48 if fill & 2 else 0)
            rows = graph([aa],[bb],dr,(False,False))
            assert even(rows,(1<<9)-1)
            assert solve_raw(rows,[0,1,2]) == ('UNKNOWN',None)
    assert solve_raw([0,0,0],[0,1,2]) == ('UNKNOWN',None)
    print('360 labelled cluster/co-cluster controls', counts, 'and 1536 embedded obstructions')


if __name__ == '__main__':
    self_test()
