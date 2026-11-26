from random import Random
from solver import solve, unary_forest


def check(guards, labels, oracle):
    reached = {}
    for x in range(1 << len(labels)):
        if all(not (x >> i & 1) or any(((mask & x).bit_count() % 2) ^ c
               for mask, c in row) for i, row in enumerate(guards)):
            out = 0
            for i, label in enumerate(labels):
                if x >> i & 1:
                    out ^= label
            reached[x] = out
    for h in range(8):
        w = oracle(h)
        assert (w is not None) == (h in reached.values())
        assert w is None or reached[w] == h


if __name__ == '__main__':
    rng = Random(913)
    for _ in range(250):
        n = rng.randrange(1,10)
        labels = [rng.randrange(8) for i in range(n)]
        guards = [[(rng.randrange(1 << i),rng.randrange(2))
                   for _ in range(rng.randrange(4))] for i in range(n)]
        check(guards,labels,lambda h:solve(guards,labels,h))
        parents = [rng.randrange(-1,i) for i in range(n)]
        allowed = [tuple(rng.randrange(2) for _ in range(2)) for i in range(n)]
        guards = [[((1 << p) if p >= 0 else 0,1^v) for v in (0,1)
                   if a[v] and (p >= 0 or v == 0)] for p,a in zip(parents,allowed)]
        check(guards,labels,lambda h:unary_forest(parents,allowed,labels,h))
    n = 1000
    labels = [0]*(n-1)+[1]
    assert unary_forest(list(range(-1,n-1)), [(1,1)]+[(0,1)]*(n-1),
                        labels,1) == (1 << n)-1
    dense = [[((1 << i)-1,1)] for i in range(n)]
    assert solve(dense,labels,1) == 1 << (n-1)
    print("500 random instances, all eight targets, plus two depth-1000 instances passed")
