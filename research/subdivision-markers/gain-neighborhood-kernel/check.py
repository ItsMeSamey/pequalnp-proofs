"""Direct named-kernel controls, including a nonregular all-negative clique."""
from itertools import combinations
from random import Random
from compress import Compression, Host, canonical, named_kernel


def subspaces(q):
    spaces = {()}
    for z in range(1,1 << q):
        spaces |= {canonical(space+(z,)) for space in spaces}
    return spaces


def random_host(rng, n):
    classes = tuple(rng.randrange(2) for _ in range(n))
    table = {(i,j):rng.choice((None,0,1,2,3)) for i in range(2) for j in range(i,2)}
    edges = [(i,j,table[tuple(sorted((classes[i],classes[j])))]) for i,j in combinations(range(n),2)]
    roots = tuple(rng.randrange(1 << (n+3)) for _ in range(3))
    return Host(n, tuple(e for e in edges if e[2] is not None), classes, roots)


def exhaustive():
    nsets = nqueries = 0
    rng = Random(1953)
    for _ in range(45):
        G = random_host(rng, rng.randrange(2,6))
        C = Compression(G)
        available = set()
        for x in range(1 << len(G.edges)):
            expect = named_kernel(G,x)
            small = C.transfer(x, back=False)
            assert expect == named_kernel(C.small,small)
            assert expect == named_kernel(G,C.transfer(small,back=True))
            available.add(expect)
            nsets += 1
        for K in subspaces(len(G.roots)):
            x = C.witness(K)
            assert (x is not None) == (K in available)
            nqueries += 1
    return nsets,nqueries


def clique(n,roots):
    return Host(n, tuple((i,j,1) for i,j in combinations(range(n),2)), (0,)*n, tuple(roots))


def selected(host,edges):
    wanted = set(edges)
    return sum(1 << i for i,(a,b,_) in enumerate(host.edges) if (a,b) in wanted)


def large():
    tiny = clique(5,(3,5,9,1 << 5))
    assert all(named_kernel(tiny,x) != (7,8) for x in range(1 << len(tiny.edges)))
    n = 76
    g = 1 << n
    G = clique(n,(3,5,9,g))
    C = Compression(G)
    assert C.small.n == 68
    # Contraction of an edge realizes precisely its gain-coupled root line.
    assert named_kernel(G,selected(G,[(0,1)])) == (9,)
    assert named_kernel(C.small,C.transfer(selected(G,[(0,1)]),back=False)) == (9,)
    # An odd triangle on other vertices makes the pure gain available.
    forest_plus_cycle = selected(G,[(0,1),(4,5),(4,6),(5,6)])
    assert named_kernel(G,forest_plus_cycle) == (1,8)
    assert named_kernel(C.small,C.transfer(forest_plus_cycle,back=False)) == (1,8)
    # F7 after contracting (0,1),(1,2),(3,4),(5,6) and restricting to seven entries.
    ix = {e[:2]:i for i,e in enumerate(G.edges)}
    cols = G.columns()
    contraction = [cols[ix[e]] for e in ((0,1),(1,2),(3,4),(5,6))]
    seven = [cols[ix[e]] for e in ((0,2),(0,3),(1,3),(0,5),(1,5),(3,5),(4,5))]
    def rank(S):
        return len(canonical(contraction+S))-len(contraction)
    assert rank(seven)==3 and all(rank([x])==1 for x in seven)
    assert all(rank([x,y])==2 for x,y in combinations(seven,2))
    # Dense roots. Both directions cross the truncation threshold.
    roots = ((1 << n)-1,g)
    D = Compression(clique(n,roots))
    assert D.small.n == 16
    rng = Random(56)
    for src,back in ((D.original,False),(D.small,True)):
        dst = D.small if not back else D.original
        for _ in range(35):
            mask = sum(1 << i for i in rng.sample(range(len(src.edges)),rng.randrange(0,35)))
            assert named_kernel(dst,D.transfer(mask,back=back)) == named_kernel(src,mask)
    return G.n,C.small.n,D.small.n


if __name__ == "__main__":
    probe = Compression(Host(2,((0,1,0),),(0,0),(3,)))
    assert probe.witness(iter([1])) == 1
    print("Exhaustive masks and target decisions:",exhaustive())
    print("Nonregular clique, 4-root and dense 2-root reductions:",large())
