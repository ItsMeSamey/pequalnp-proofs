"""Small exhaustive frame checks, witness replay, and larger recognition controls."""
from itertools import combinations, permutations, product
from random import Random
from time import monotonic
from prism_colour_quotient import solve_prism

FRAME=tuple(permutations(range(3)))


def graph(n, links):
    edges=[(3*i+p,3*i+q) for i in range(n) for p,q in combinations(range(3),2)]
    for i,j,perm in links:
        edges.extend((3*i+k,3*j+perm[k]) for k in range(3))
    return edges


def verify(n,edges,result):
    if result.status=="SAT":
        assert len(result.witness)==n and set(result.witness)<=set(range(3))
        assert all(result.witness[u]!=result.witness[v] for u,v in edges)
    if result.sign_cycle:
        assert result.sign_cycle[0]==result.sign_cycle[-1]
        graph_edges={tuple(sorted(e)) for e in edges}
        sign=1
        for i,j in zip(result.sign_cycle,result.sign_cycle[1:]):
            perm=[next(q for q,v in enumerate(result.layers[j]) if tuple(sorted((u,v))) in graph_edges)
                  for u in result.layers[i]]
            sign*=1 if (perm[1]-perm[0])%3==1 else -1
        assert sign==-1


def main():
    start=monotonic()
    rng=Random(313)
    cases=0
    for n in range(1,6):
        for _ in range(80):
            links=[(u,v,rng.choice(FRAME)) for u,v in combinations(range(n),2) if rng.randrange(3)]
            expected=any(all(all(f[i][k]!=f[j][p[k]] for k in range(3)) for i,j,p in links)
                         for f in product(FRAME,repeat=n))
            edges=graph(n,links)
            result=solve_prism(3*n,edges,core_limit=n)
            assert result.status==("SAT" if expected else "UNSAT")
            verify(3*n,edges,result)
            cases+=1
    for n in (4,5,16,101,500):
        for twist in (False,True):
            links=[(i,(i+1)%n,(1,0,2) if twist and i==n-1 else (0,1,2)) for i in range(n)]
            edges=graph(n,links)
            result=solve_prism(3*n,edges)
            assert result.status==("UNSAT" if twist else "SAT")
            verify(3*n,edges,result)
    size=45
    links=[(u,v,(1,2,0)) for u in range(size*size)
           for v in ([u+1] if u%size<size-1 else [])+([u+size] if u+size<size*size else [])]
    edges=graph(size*size,links)
    result=solve_prism(3*size*size,edges)
    assert result.status=="SAT" and not result.core
    verify(3*size*size,edges,result)
    tri=graph(3,[(i,j,(0,1,2)) for i,j in combinations(range(3),2)])
    assert solve_prism(9,tri,recognition_limit=0).status=="UNKNOWN"
    assert solve_prism(9,tri).status=="SAT"
    clique=graph(4,[(i,j,(0,1,2)) for i,j in combinations(range(4),2)])
    partition=[(3*i,3*i+1,3*i+2) for i in range(4)]
    assert solve_prism(12,clique,layers=partition).status=="UNKNOWN"
    assert solve_prism(12,clique,layers=partition,core_limit=4).status=="UNSAT"
    malformed=graph(2,[])+[(0,3)]
    assert solve_prism(6,malformed).status=="UNSUPPORTED"
    assert solve_prism(3,[(0,1),(1,2),(2,0)],layers=[(1,0,2)]).status=="SAT"
    assert solve_prism(0,[]).witness==()
    print(f"{cases} brute-force comparisons, 10 ring controls, {3*size*size}-vertex grid, recognition and core limits passed in {monotonic()-start:.3f}s")


if __name__=="__main__":
    main()
