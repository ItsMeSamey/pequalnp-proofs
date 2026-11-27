"""Original-edge exhaustive oracle for vector-residue perfect matching."""
from itertools import product
from random import Random
from ternary_vector_routes import solve


def targets(graph,n,b):
    by_vertex = [[] for _ in range(n)]
    for i,(u,v,_) in enumerate(graph):
        by_vertex[u].append((v,i))
        by_vertex[v].append((u,i))
    results = set()
    def visit(remaining,weight):
        if not remaining:
            results.add(weight)
            return
        v=min(remaining)
        for u,i in by_vertex[v]:
            if u in remaining:
                gain=graph[i][2]
                visit(remaining-{u,v},tuple((x+y)%3 for x,y in zip(weight,gain)))
    visit(set(range(n)),(0,)*b)
    return results


def replay(graph,n,t,answer):
    status, ids, stats=answer
    if status=="SAT":
        assert len(set(ids))==len(ids) and all(0<=i<len(graph) for i in ids)
        assert sorted(v for i in ids for v in graph[i][:2])==list(range(n))
        assert tuple(sum(graph[i][2][j] for i in ids)%3 for j in range(len(t)))==t
    return status,stats


def main():
    rng=Random(77631)
    count=0
    stats_seen=[]
    def audit(n,graph,b,kwargs=None,capped=False,collect=False):
        nonlocal count
        feasible=targets(graph,n,b)
        for t in product(range(3),repeat=b):
            status,stats=replay(graph,n,t,solve(n,graph,t,**(kwargs or {})))
            if collect:
                stats_seen.append((t,status,stats))
            if status=="UNKNOWN":
                assert capped
            else:
                assert (status=="SAT")== (t in feasible), (n,graph,t,kwargs,status)
            count+=1
    audit(0,[],0)
    audit(0,[],2)
    audit(4,[(0,2,(1,2))],2)
    audit(4,[(0,1,()),(2,3,())],0)
    # Basis toggles on disjoint two-vertex components, lifted as parallel-edge choices.
    n=10
    graph=[]
    for i in range(n):
        g=tuple(int(j==i%2) for j in range(2))
        graph.extend([(i,n+i,(0,0)),(n+i,i,g)])
    audit(2*n,graph,2,{"threshold":1},collect=True)
    # A long nonzero first-coordinate cycle and multiple independent second-coordinate
    # choices, including labelled parallel loops inside scalar-neutral components.
    n=6
    graph=[(i,n+i,(0,0)) for i in range(n)]
    for u,v,g in [(0,1,(1,0)),(1,2,(0,0)),(2,0,(0,0)),
                  (2,3,(0,1)),(3,2,(0,2)),(2,2,(0,2)),(2,2,(0,1)),
                  (3,3,(0,1)),(5,5,(0,1))]:
        graph.append((u,n+v,g))
    audit(2*n,graph,2,{"threshold":1},collect=True)
    audit(2*n,graph,2,{"threshold":1,"portal_cap":0},capped=True,collect=True)
    # Many portal incidence records collide at the same outside head or tail.
    n=5
    graph=[(i,n+i,(0,0)) for i in range(n)]
    for u,v in [(0,2),(1,2),(2,0),(2,1),(0,3),(0,4),(3,0),(4,0),(1,3),(4,1)]:
        graph.append((u,n+v,((u+2*v)%3,(u*v+1)%3)))
    audit(2*n,graph,2,{"threshold":1})
    # Reproducible arbitrary labels; shuffle original vertex IDs, row orientation and edge IDs.
    for trial in range(45):
        n=rng.randrange(1,6)
        b=(1,2,2,3)[trial%4]
        graph=[]
        ids=list(range(2*n))
        rng.shuffle(ids)
        for u,v in product(range(n),repeat=2):
            for _ in range((u==v)+(rng.randrange(4)==0)+(rng.randrange(7)==0)):
                w=tuple(rng.randrange(3) for j in range(b))
                a,c=ids[u],ids[n+v]
                graph.append((a,c,w) if rng.randrange(2) else (c,a,w))
        rng.shuffle(graph)
        audit(2*n,graph,b,{"threshold":1+trial%2})
    assert any(s["bases"]>0 for _,_,s in stats_seen[:9])
    assert any(s["calls"]>1 and s["portal_nodes"]>0 for _,_,s in stats_seen[9:18])
    assert any(r=="UNKNOWN" and s["cap_hits"]>0 for _,r,s in stats_seen[18:])
    print(count,"target cases passed")
    print("branch statistics for independent and coupled controls:",stats_seen[1],stats_seen[10],stats_seen[19])


if __name__=="__main__":
    main()
