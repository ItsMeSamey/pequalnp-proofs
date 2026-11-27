"""Exercise target-specific quotients, noncommuting generator repair and scalar avoidance."""
from itertools import combinations,product
from labelled_affine_orbit import solve


def main():
    points=list(product(range(3),repeat=2))
    edges=[(0,1,s) for s in points]
    def action(A,t):
        perm=[points.index(tuple((sum(x*y for x,y in zip(row,s))+z)%3 for row,z in zip(A,t))) for s in points]
        return A,t,(0,1),perm,(t,(0,0))
    acts=[action(((1,1),(0,1)),(0,0)),action(((1,0),(0,1)),(0,1))]
    def last(n,edges,target):
        return 'SAT',(max(i for i,e in enumerate(edges) if e[2]==target),),{}
    for t in points:
        s,w,stats=solve(2,edges,t,acts,backend=last)
        assert s=='SAT' and edges[w[0]][2]==t and stats['flat_rank']==2
    line={(x,1,0) for x in range(3)}
    zero=(0,0,0)
    gains=sorted(set(product(range(3),repeat=3))-line-{zero})
    edges=[(0,j+1,s) for j,s in enumerate(gains)]+[(u,v,zero) for u,v in combinations(range(1,24),2)]
    lookup={(u,v):i for i,(u,v,_) in enumerate(edges)}
    perm=[0]+[1+gains.index(((x+y)%3,y,z)) for x,y,z in gains]
    ep=[lookup[tuple(sorted((perm[u],perm[v])))] for u,v,g in edges]
    A=((1,1,0),(0,1,0),(0,0,1))
    def spokes(n,E,t):
        for i,(u,v,g) in enumerate(E[:23]):
            if g==t:
                rim=sorted(set(range(1,n))-{v})
                return 'SAT',(i,)+tuple(lookup[x,y] for x,y in zip(rim[::2],rim[1::2])),{}
        return 'UNSAT',None,{}
    for t in product(range(3),repeat=3):
        s,w,stats=solve(24,edges,t,[(A,zero,perm,ep,[zero]*24)],backend=spokes)
        assert (s=='SAT')==(t in gains)
        if w: assert tuple(sum(edges[i][2][j] for i in w)%3 for j in range(3))==t
        if t in line: assert stats['flat_rank']==1
    for attained in [(0,), (1,2)]:
        edges=[(0,1,(x,)) for x in attained]
        ep=[attained.index(-x%3) for x in attained]
        act=[(((2,),),(0,),(0,1),ep,[(0,),(0,)])]
        def avoid(n,E,v):
            ids=[i for i,e in enumerate(E) if e[2]!=v]
            return ('SAT',(ids[-1],),{}) if ids else ('UNSAT',None,{})
        for t in [(1,),(2,)]:
            s,w,stats=solve(2,edges,t,act,avoid=avoid)
            assert stats['mode']=='avoid' and (s=='SAT')==(t[0] in attained)
            if w: assert edges[w[0]][2]==t
    print("9 noncommuting repairs, 27 K24 targets, 4 scalar avoidance cases passed")


if __name__=="__main__":
    main()
