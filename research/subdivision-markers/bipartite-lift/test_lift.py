from itertools import product
from random import Random
from lift import apply, basis, build, dot, extend, optimum, transpose


def rank_check(rows,l):
    n = len(rows)
    r = n-l
    cross,left,right,claimed = optimum(rows,l)
    actual = len(basis(left)) + len(basis(right))
    best = n+1
    for trial in product(range(1 << r),repeat=l):
        residual = [a ^ (b << l) for a,b in zip(rows,trial)] + [a ^ b for a,b in zip(rows[l:],transpose(trial,r))]
        best = min(best,len(basis(residual[:l]))+len(basis(residual[l:])))
    assert best == actual == claimed


def lift_check(rows,l,exhaust):
    n = len(rows)
    graph = build(rows,l)
    shore,edges,markers,hub,spokes = graph
    assert all(shore[a] != shore[b] for a,b in edges)
    assert len(edges) == len({tuple(sorted(e)) for e in edges})
    adj = [0]*len(shore)
    for a,b in edges:
        adj[a] |= 1 << b
        adj[b] |= 1 << a
    expected = {x for x in range(1 << n) if not x & apply(rows,x)}
    def valid(s):
        return all((s >> i & 1) == dot(s,mask) for i,mask in markers) and not s & apply(adj,s)
    for x in range(1 << n):
        assert valid(extend(x,graph)) == (x in expected)
    if exhaust:
        actual = {s & ((1 << n)-1) for s in range(1 << len(shore)) if valid(s)}
        assert actual == expected


if __name__ == '__main__':
    count = 0
    for n in range(4):
        for rows in product(range(1 << n),repeat=n):
            for l in range(n+1):
                rank_check(rows,l)
                count += 1
    rng = Random(419)
    for _ in range(300):
        n = rng.randrange(1,7)
        l = rng.randrange(n+1)
        rows = [rng.randrange(1 << n) for i in range(n)]
        rank_check(rows,l)
        lift_check(rows,l,n <= 3)
    print(count,"exhaustive matrix-partitions plus 300 seeded rank and lifting cases passed")
