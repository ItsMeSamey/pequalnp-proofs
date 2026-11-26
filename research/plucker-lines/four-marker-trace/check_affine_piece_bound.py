"""Check the positive-slice and connectivity claims in the staged family."""
from itertools import product

def graph(n):
    L,R,O,U,D=range(5)
    h=[U]+list(range(5,5+n))+[D]
    y,z=5+n,6+n
    pairs=[(7+n+2*i,8+n+2*i) for i in range(n)]
    edges=[(U,y),(U,z),(y,h[1]),(z,h[1]),(L,y),(y,O),(O,z),(z,R)]
    for i,(a,b) in enumerate(pairs,1):
        edges += [(h[i],a),(h[i],b),(a,h[i+1]),(b,h[i+1]),(a,b),(L,a),(R,b)]
    for v in h[1:-1]:edges.extend([(L,v),(R,v)])
    return edges,h[1:-1]+[y,z],pairs

def components(vertices,edges,skip=None):
    graph={v:set() for v in vertices if v!=skip}
    for a,b in edges:
        if a!=skip and b!=skip:graph[a].add(b);graph[b].add(a)
    unseen=set(graph);out=[]
    while unseen:
        todo=[unseen.pop()];cc=set(todo)
        for a in todo:
            ext=graph[a]&unseen;unseen-=ext;todo.extend(ext);cc|=ext
        out.append(cc)
    return out

def check(n):
    E,slicevars,pairs=graph(n);V=set.union(*(set(e) for e in E))
    assert all(len(components(V,E,v))==1 for v in V)
    collapse=lambda v:0 if v<5 else v
    Q=[(collapse(a),collapse(b)) for a,b in E]
    W={collapse(v) for v in V}
    assert all(a!=b for a,b in Q)
    assert all(len(components(W,Q,v))==1 for v in W)
    p=1|2|8|16 # LRUD
    K={s for s in range(32) if (s&7).bit_count()%2==0 and (s>>3).bit_count()%2==0}
    attained=set();positive=0
    for x in range(1<<(len(V)-5)):
        col=24|(x<<5)
        mono=[(a,b) for a,b in E if ((col>>a)^(col>>b))&1==0]
        cc=components(V,mono)
        term=[sum(1<<v for v in part if v<5) for part in cc]
        possible={s for s in K if all((s&t).bit_count()%2==0 for t in term)}
        attained|=possible
        if all(col>>v&1 for v in slicevars):
            wanted=all((col>>a&1) or (col>>b&1) for a,b in pairs)
            assert (24 in possible)==wanted
            assert (3 in possible)==(not wanted)
            positive+=wanted
    assert attained==K-{p}
    assert positive==3**n

if __name__=="__main__":
    for n in (1,2,3):check(n)
    print("Staged families with 1, 2 and 3 ordinary stages passed")
