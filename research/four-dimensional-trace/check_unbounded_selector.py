"""Exhaustively verify connectedness, flux image, and the forced OR on small members."""
from itertools import combinations


def components(vertices, edges):
    groups = [{v} for v in vertices]
    for a, b in edges:
        left = next(g for g in groups if a in g)
        right = next(g for g in groups if b in g)
        if left != right:
            left.update(right)
            groups.remove(right)
    return groups


def biconnected(vertices, edges):
    return all(len(components(vertices - {x}, [(a,b) for a,b in edges if x not in (a,b)])) == 1
               for x in vertices)


def check(n):
    L,R,Z,U,D = range(5)
    v = list(range(5,5+n))
    wL,wR = 5+n,6+n
    vertices = set(range(7+n))
    path = [L]+v+[R]
    edges = list(zip(path,path[1:])) + [(t,a) for t in (U,D) for a in v]
    edges += [(Z,v[1]),(Z,v[2])] + [(wL,t) for t in (L,U,v[0])] + [(wR,t) for t in (R,U,v[-1])]
    assert biconnected(vertices,edges)
    hub = lambda x: 0 if x < 5 else x
    projected = [(hub(a),hub(b)) for a,b in edges]
    assert all(a!=b for a,b in projected) and biconnected({hub(x) for x in vertices},projected)
    A=(1<<L)|(1<<R)
    B=(1<<U)|(1<<D)
    image=set()
    for x in range(1<<(n+2)):
        colors=(x<<5)|B
        eligible=[(a,b) for a,b in edges if ((colors>>a)^(colors>>b))&1==0]
        masks=[sum(1<<a for a in g if a<5) for g in components(vertices,eligible)]
        fiber={p for p in range(32) if all((p&m).bit_count()%2==0 for m in masks)}
        assert (B in fiber)==bool(x&((1<<n)-1)) and (A in fiber)!=(B in fiber)
        image.update(fiber)
    assert image=={p for p in range(32) if p.bit_count()%2==0 and (p&B).bit_count()%2==0}-{A^B}


for n in range(4,9):
    check(n)
print("All colorings verified for n=4,...,8; both matroids connected throughout.")
