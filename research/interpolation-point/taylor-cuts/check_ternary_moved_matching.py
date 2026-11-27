from itertools import combinations,product
from random import Random
from ternary_moved_matching import solve

def oracle(n,edges):
    def walk(vertices):
        if not vertices:
            yield ()
            return
        u=min(vertices)
        for i,(a,b,g) in enumerate(edges):
            if u in (a,b) and a in vertices and b in vertices:
                for tail in walk(vertices-{a,b}):
                    yield (i,)+tail
    return list(walk(set(range(n))))

if __name__=='__main__':
    rnd=Random(1218)
    cases=0
    for graph in range(120):
        m=rnd.randrange(1,5)
        b=rnd.randrange(3)
        left=set(range(m)) if graph%2 else None
        def lab(): return tuple(rnd.randrange(3) for _ in range(b))
        edges=[(u,u+m,lab()) for u in range(m)]
        for u,v in combinations(range(2*m),2):
            if left is not None and (u in left)==(v in left):
                continue
            for j in range(rnd.randrange(3)):
                if rnd.random()<0.6:
                    edges.append((u,v,lab()))
        base=range(m)
        best={}
        for matching in oracle(2*m,edges):
            t=tuple(sum(edges[i][2][j] for i in matching)%3 for j in range(b))
            k=len(set(base)-set(matching))
            best[t]=min(k,best.get(t,m+1))
        for t in product(range(3),repeat=b):
            cap=rnd.randrange(m+1)
            for c in (None,cap):
                s,w,d=solve(2*m,edges,base,t,left=left,cap=c)
                expected='SAT' if best.get(t,m+1)<=d['limit'] else ('UNSAT' if d['limit']==d['bound'] else 'UNKNOWN')
                assert s==expected,(s,expected)
                if w is not None:
                    assert len(set(base)-set(w))==best[t]
                cases+=1
    m=12
    edges=[(i,m+i,(0,)) for i in range(m)]+[(i,m+(i+1)%m,(int(i==0),)) for i in range(m)]
    assert solve(2*m,edges,range(m),(1,),left=range(m),cap=3)[0]=='UNKNOWN'
    assert solve(2*m,edges,range(m),(1,),left=range(m))[0]=='SAT'
    print(cases,'random differential calls and sparse cycle cap controls passed')
