"""Independent direct enumeration of labelled perfect matchings and independent sets."""
from itertools import combinations, product
from labelled_konig_deficiency import solve


def matchings(n, edges):
    def visit(free):
        if not free:
            yield ()
            return
        u = min(free)
        for i, (a, b, _) in enumerate(edges):
            if u in (a, b) and a in free and b in free:
                for rest in visit(free - {a, b}):
                    yield (i, *rest)
    return list(visit(set(range(n))))


def independent_number(n, edges):
    return max(mask.bit_count() for mask in range(1 << n)
               if all(not (mask >> u & mask >> v & 1) for u, v, _ in edges))


def check(n, edges, width):
    by_target = {}
    for ids in matchings(n, edges):
        goal = tuple(sum(edges[i][2][j] for i in ids) % 3 for j in range(width))
        by_target.setdefault(goal, set()).add(frozenset(ids))
    delta = n//2 - independent_number(n, edges)
    for goal in product(range(3), repeat=width):
        for cap in sorted({max(delta, 0), 0}):
            status, ids, _ = solve(n,edges,goal,deficiency_cap=cap)
            expected = ("UNKNOWN" if by_target and cap < delta else
                        "SAT" if goal in by_target else "UNSAT")
            assert status == expected, (n,edges,goal,cap,status,expected)
            if ids is not None:
                assert len(ids) == n//2 and frozenset(ids) in by_target[goal]
            else:
                assert expected != "SAT"


def main():
    for n in (0,2,4):
        pairs = list(combinations(range(n), 2))
        for mask in range(1 << len(pairs)):
            edges = [(u,v,((j + mask) % 3,)) for j,(u,v) in enumerate(pairs) if mask >> j & 1]
            check(n, edges, 1)
    for labels in product(range(3),repeat=3):
        edges = [(0,1,(labels[0],1)), (0,1,(labels[1],2)), (2,3,(labels[2],0)),
                 (0,2,(1,0)),(1,3,(0,1)),(0,3,(2,0)),(1,2,(2,1))]
        check(4, edges, 2)
    k=4
    edges=[(a,b,((a+b)%3,)) for a,b in combinations(range(2*k),2) if a<k+1]
    all_matches=matchings(2*k,edges)
    assert set(range(len(edges)))==set(i for ids in all_matches for i in ids)
    assert independent_number(2*k,edges)==k-1
    check(2*k,edges,1)
    print("67 simple supports, 27 two-coordinate parallel controls and all-edges-allowed split graph passed")


if __name__=="__main__":
    main()
