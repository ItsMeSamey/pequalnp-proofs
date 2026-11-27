from itertools import combinations,product
from random import Random
from labelled_near_barrier import solve


def oracle(n,edges,b):
    def walk(rem):
        if not rem:
            yield (0,)*b
            return
        u=min(rem)
        for a,c,g in edges:
            if a in rem and c in rem and u in (a,c):
                for t in walk(rem-{a,c}):
                    yield tuple((x+y)%3 for x,y in zip(t,g))
    return set(walk(set(range(n))))

if __name__=='__main__':
    rng=Random(8713)
    cases=0
    for j in range(85):
        n=2*rng.randrange(5)
        b=1+j%2
        B=rng.sample(range(n),rng.randrange(n+1))
        edges=[(u,v,tuple(rng.randrange(3) for _ in range(b))) for u,v in combinations(range(n),2)
               for k in range(1+int(rng.randrange(7)==0)) if rng.randrange(3)]
        possible=oracle(n,edges,b)
        for t in product(range(3),repeat=b):
            status,w,d=solve(n,edges,t,B)
            assert status==('SAT' if t in possible else 'UNSAT'),(edges,B,t)
            cases+=1
    # Odd triangles completely joined to a clique of r+2 vertices.
    r=3
    B=set(range(r+2))
    tris=[set(range(r+2+3*j,r+5+3*j)) for j in range(r)]
    n=4*r+2
    edges=[(u,v,(1,)) for u,v in combinations(sorted(B),2)]
    edges += [(u,v,(0,)) for tr in tris for u,v in combinations(sorted(tr),2)]
    edges += [(u,v,(0,)) for u in B for tr in tris for v in tr]
    # Slack two allows one internal clique edge or a triple hit in a triangle.
    for t in range(3):
        status,w,d=solve(n,edges,(t,),B,component_cap=3,slack_cap=2)
        assert status==('SAT' if t in (0,1) else 'UNSAT') and d['slack']==2
        if t==0:
            assert max(sum((edges[i][0] in B and edges[i][1] in tr) for i in w) for tr in tris)==3
    assert solve(n,edges,(0,),B,slack_cap=1)[0]=='UNKNOWN'
    assert solve(n,edges,(0,),B,component_cap=2)[0]=='UNKNOWN'
    print(cases,'brute target comparisons plus clique joined to disjoint triangles and caps passed')
