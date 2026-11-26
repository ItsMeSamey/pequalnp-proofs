from itertools import product, combinations
from functools import reduce
from operator import xor

def test(columns, target):
    # Target-normalizing invertible map on F2^2 is a transposition.
    def normalize(c):
        if target and c in (target, 3):
            return 3 if c == target else target
        return c
    n = len(columns)
    adj = [0] * (n+3)
    def edge(i, j):
        adj[i] |= 1<<j
        adj[j] |= 1<<i
    if target:
        edge(n,n+1)
    for i, column in enumerate(columns):
        for j in {0:(),1:(0,2),2:(1,2),3:(0,1)}[normalize(column)]:
            edge(i,n+j)
    for vis in range(1<<n):
        expect = reduce(xor,(c for i,c in enumerate(columns) if vis>>i&1),0) == target
        actual = False
        for free in (0,1):
            s = vis | ((3+4*free)<<n)
            actual |= all(not ((s>>i&1) and (s & row).bit_count()%2) for i,row in enumerate(adj))
        assert expect == actual

if __name__ == '__main__':
    cnt=0
    for n in range(6):
        for cols in product(range(4),repeat=n):
            for target in range(4):
                test(cols,target)
                cnt+=1
    cols=list(range(1,7))
    pairs=[set(p) for p in combinations(cols,2) if reduce(xor,p)==7]
    assert len(pairs)==3 and set.union(*pairs)==set(cols)
    triple={1,2,4}
    assert reduce(xor,triple)==7 and not any(p<=triple for p in pairs)
    print(cnt,'full rank-at-most-two projected comparisons and rank-three obstruction passed')
