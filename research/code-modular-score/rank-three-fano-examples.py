from itertools import combinations

def catalogue(charges, edge_words):
    n = len(charges)
    edges = {tuple(map(int, pair)) for pair in edge_words.split()}
    def connected(block):
        seen = {min(block)}
        while True:
            new = seen | {v for x,y in edges for u,v in ((x,y),(y,x)) if u in seen and v in block}
            if new == seen:
                return new == block
            seen = new
    result = set()
    def search(v, blocks):
        if v < n:
            for i in range(len(blocks)):
                blocks[i].add(v)
                search(v+1, blocks)
                blocks[i].remove(v)
            search(v+1, blocks + [{v}])
            return
        if not all(connected(block) for block in blocks): return
        span = {0}
        for block in blocks:
            val = 0
            for u in block: val ^= charges[u]
            span |= {x ^ val for x in span}
        result.add(frozenset(span))
    search(0, [])
    return result

simplex = [1,2,4,7]
cases = [
    (simplex, '01 12 23 03', (1,3)),
    (simplex, '01 12 23 03 02', (1,2)),
    (simplex, '01 02 03 12 13 23', (0,1)),
    ([1,2,4,1,6], '01 12 23 34 04', (0,0)),
    ([1,0,2,4,7], '01 04 12 13 14 23 34', (1,1)),
    ([1,2,2,1,4,4], '01 05 12 23 24 25 34 45', (1,0))]
points = {frozenset((0,i)) for i in range(1,8)}
planes = {frozenset((0,i,j,i^j)) for i,j in combinations(range(1,8),2)}
for charges, edges, expected in cases:
    value = catalogue(charges,edges)
    mp, mh = points-value, planes-value
    assert (len(mp),len(mh)) == expected
    assert all(point <= plane for point in mp for plane in mh)
    print(len(charges), expected)
