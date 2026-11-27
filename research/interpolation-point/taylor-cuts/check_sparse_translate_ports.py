from itertools import combinations
from functools import lru_cache
from sparse_translate_ports import solve


def main():
    modules=[list(range(6*j,6*j+6)) for j in range(3)]
    edges=[(u,v,0) for M in modules for u,v in combinations(M,2) if (u,v)!=(0,1)]
    links=[]
    for j in range(3):
        for p in range(3):
            links.append((6*j+3+p,6*((j+1)%3)+p,int(j==0 and p==0)))
    edges+=links
    @lru_cache(None)
    def actual(V):
        if not V:
            return {0}
        x=min(V)
        return {(h+g)%3 for u,v,g in edges if x in (u,v) and u in V and v in V
                for h in actual(V-{u,v})}
    gains=actual(frozenset(range(18)))
    assert gains=={0,1}
    bad=allowed=0
    for mask in range(1<<9):
        used={x for i,(u,v,g) in enumerate(links) if mask>>i&1 for x in (u,v)}
        if all(len(set(M)-used)%2==0 for M in modules):
            allowed+=1
            bad+=int(set(modules[0])-used=={0,1})
    assert (allowed,bad)==(128,4)
    for t in range(3):
        s,w,m=solve(18,edges,modules,t)
        assert s==('SAT' if t in gains else 'UNSAT')
        if w is not None:
            assert m['delta']=='1/32' and m['support']==2
            assert sum(edges[i][2] for i in w)%3==t
            assert solve(18,edges,modules,t,potentials=[0]*18)[1]==w
        else:
            assert m['support']==0
    assert solve(18,edges,modules,1,subset_cap=0)[0]=='UNKNOWN'
    # Boundary D delta = 1: two modules with two parallel macro links,
    # no first-module interior edge, both link bits equal, both selected necessary.
    tiny=[(2,3,0),(0,2,1),(1,3,0)]
    s,w,m=solve(4,tiny,[[0,1],[2,3]],0)
    assert s=='UNKNOWN' and m['delta']=='1/2' and m['support']==2
    try:
        solve(18,edges,modules,1,potentials=[1]*18)
    except ValueError:
        pass
    else:
        raise AssertionError('bad supplied endpoint potentials accepted')
    print('18-vertex cyclic host: 4/128 parity points unliftable, 2×1/32<1, both witnesses replayed; target 2 NO, equality and cap UNKNOWN')

if __name__=='__main__':
    main()
