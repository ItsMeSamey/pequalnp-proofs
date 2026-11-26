"""Cross-check normalized closure in the ordinary polynomial ring with pins."""
from itertools import combinations_with_replacement
from random import Random
from analyze import compare
from hull import add


def raw(adj,d):
    n=len(adj)
    mons=[t for k in range(d+1) for t in combinations_with_replacement(range(n),k)]
    idx={t:i for i,t in enumerate(mons)}
    low=sum(len(t)<d for t in mons)
    def encode(ts):
        p=0
        for t in ts:
            p ^= 1<<idx[tuple(sorted(t))]
        return p
    basis={}
    q=[encode([(i,i),(i,)]) for i in range(n)]
    q.extend(encode((i,j) for j in range(n) if row>>j&1) for i,row in enumerate(adj))
    q.extend(encode([(),(i,)]) for i in (0,1))
    for p in q:
        f=add(basis,p)
        if not f or f.bit_length()>low:
            continue
        terms=[mons[j] for j in range(f.bit_length()) if f>>j&1]
        q.extend(encode(t+(j,) for t in terms) for j in range(n))
    return {k:v for k,v in basis.items() if k<=n+1}


def test(adj):
    points,exact,q,c=compare(adj)
    for d,expected in ((2,q),(3,c)):
        original=raw(adj,d)
        assert len(original)==len(expected)
        assert all(not add(original,p) for p in expected.values())
        assert all(not((h&p).bit_count()%2) for p in points for h in original.values())


if __name__=="__main__":
    test([82,49,104,20,11,6,5])
    test([386,25,352,194,34,20,12,9,5])
    rng=Random(852)
    for _ in range(50):
        n=rng.randint(3,8);adj=[0]*n
        adj[0]=2;adj[1]=1
        for i in range(n):
            for j in range(max(2,i+1),n):
                if rng.randrange(2):
                    adj[i]|=1<<j
                    adj[j]|=1<<i
        test(adj)
    print("104 ordinary-ring comparisons passed")
