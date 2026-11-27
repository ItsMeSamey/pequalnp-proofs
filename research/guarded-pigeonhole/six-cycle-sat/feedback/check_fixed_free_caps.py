from itertools import permutations
from one_long_forbidden_cycle import normalize, cycles, forbidden


def insert(sigma, wire, large):
    p = list(sigma)
    n = len(p)
    old = p.index(wire)
    if not large:
        p.extend([n+2, n+1, wire])
    else:
        # Subdivide edge 1--2 of K4 by vertex 0.
        edges = [(0,1),(0,2),(1,3),(1,4),(2,3),(2,4),(3,4)]
        slots = [1,0,0,0,0]
        p.extend([-1]*15)
        p[n+2] = wire
        for u,v in edges:
            i,j = slots[u],slots[v]
            slots[u]+=1
            slots[v]+=1
            p[n+3*u+(i-1)%3] = n+3*v+j
            p[n+3*v+(j-1)%3] = n+3*u+i
    p[old] = n
    return p


def trace(p, mask, n):
    perm = [p[i-i%3+(i+((mask>>(i//3))&1))%3] for i in range(len(p))]
    return [tuple(v for v in orbit if v<n) for orbit in cycles(perm) if min(orbit)<n]


if __name__ == "__main__":
    tests=0
    for sigma in permutations(range(3)):
        for wire in range(3):
            for large in (False,True):
                p=insert(sigma,wire,large)
                expected=cycles(forbidden(sigma))
                lengths=[len(c)+(wire in c) for c in expected] + [2]*(7 if large else 1)
                assert sorted(lengths)==sorted(map(len,cycles(forbidden(p))))
                for m in range(1<<(len(p)//3)):
                    assert trace(p,m,3)==trace(sigma,m&1,3)
                    tests+=1
    print(tests,"single-insertion mask comparisons")
