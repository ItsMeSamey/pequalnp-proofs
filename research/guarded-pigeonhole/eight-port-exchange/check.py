from itertools import product, permutations
from pathlib import Path
import sys
import networkx as nx
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'pappus-dm'))
from composer import decide,has_pm,edge

def rebase(g,ports,colors,base):
    holders=[v for v,c in zip(ports,colors) if c==base]
    assert len(ports)==len(set(ports)) and len(holders)==4
    other=[k for k in range(3) if k!=base]
    fixed=[(v,other.index(c)) for v,c in zip(ports,colors) if c!=base]
    free=g.subgraph(set(g)-set(holders))
    shore=nx.bipartite.color(g)
    unknown=False
    for choice in product((0,1),repeat=4):
        prescribed={};consistent=True
        for u,b in zip(holders,choice):
            assert len(g[u])==2
            for w,c in zip(sorted(g[u]),(b,1-b)):
                e=edge(u,w)
                if e in prescribed and prescribed[e]!=c:consistent=False
                prescribed[e]=c
        if not consistent:continue
        ext=fixed+[(v,c) for e,c in prescribed.items() for v in e if v in free]
        answer,front,sizes=decide(free,ext,shore)
        assert max(front,default=0)<=6
        if answer=='SAT':return answer
        unknown|=answer=='UNKNOWN'
    return 'UNKNOWN' if unknown else 'UNSAT'

def family(n):
    g=nx.Graph()
    for i in range(n):
        for j,k in product(range(3),repeat=2):
            if j==k and j<2:continue
            g.add_edge(6*i+j,6*i+3+k)
        if i:
            g.add_edges_from((6*i-3+j,6*i+j) for j in (0,1))
    ports=[];colors=[]
    for j in (0,1):
        path=[6*n-3+j]+list(range(6*n+4*j,6*n+4*j+4))+[j]
        nx.add_path(g,path)
        ports+=path[1:-1];colors+=[0,1,1,0]
    return g,ports,colors

def homogeneous(n):
    g,p,c=family(n)
    assert all(has_pm(g.subgraph(set(g)-{u,v})) for u,v in g.edges)
    assert rebase(g,p,c,0)=='SAT'
    free=g.subgraph(set(g)-{v for v,k in zip(p,c) if k==0})
    possible={edge(u,v) for u,v in free.edges if has_pm(free.subgraph(set(free)-{u,v}))}
    a=nx.Graph();a.add_edges_from(possible)
    assert sorted(map(len,nx.connected_components(a)))==[2,2]+[6]*n
    # Enumerate the local matchings independently. Compute endpoint relations from residue.
    tile=g.subgraph(range(6))
    local=[]
    for perm in permutations(range(3,6)):
        m=[(u,v) for u,v in enumerate(perm)]
        if not all(tile.has_edge(*e) for e in m):continue
        f=tile.copy();f.remove_edges_from(m)
        cap=nx.has_path(f,0,1)
        local.append((set(m),cap))
    assert sorted(c for m,c in local)==[False,False,True]
    cap=next(m for m,c in local if c)
    assert all(nx.is_connected(nx.Graph(list(cap^m))) for m,c in local if not c)
    if n<=5:
        from matching_multipole import extend_matching
        for states in product(local,repeat=n):
            m={(6*i+u,6*i+v) for i,(pm,_) in enumerate(states) for u,v in pm}
            m.update((6*n+4*j+1,6*n+4*j+2) for j in (0,1))
            ok=extend_matching(g,p,c,0,m) is not None
            assert ok==all(not bad for _,bad in states)
    return len(g)

if __name__=='__main__':
    for n in [1,2,3,4,5,8,12]:
        print('tiles',n,'vertices',homogeneous(n),'exact distance',n)
