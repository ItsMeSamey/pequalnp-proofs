"""Construct a proper word in an all-odd host with a universal two-port limb."""
from itertools import combinations
from collections import deque
from eleven_site_limb_search import summary


def eliminate(rows):
    n=len(rows)
    a=[v|(1<<(n+i)) for i,v in enumerate(rows)]
    pivot=[]
    for j in range(n):
        i=len(pivot)
        h=next((h for h in range(i,n) if a[h]>>j&1),None)
        if h is None:continue
        a[i],a[h]=a[h],a[i]
        for k in range(n):
            if k!=i and a[k]>>j&1:a[k]^=a[i]
        pivot.append(j)
    if len(pivot)==n:return [v>>n for v in a],0
    j=next(i for i in range(n) if i not in pivot)
    return None,(1<<j)|sum(((a[i]>>j)&1)<<p for i,p in enumerate(pivot))


def escape(krows, pins, ports):
    """K has physical exterior edges, with the interior deleted; return sites to delete."""
    n=len(krows)
    R=[i for i in range(n) if i not in ports]
    C=[i for i in range(n) if i not in pins]
    G=set(R)&set(C)
    matrix=[sum(((krows[i]>>v)&1)<<j for j,v in enumerate(C)) for i in R]
    inv,ker=eliminate(matrix)
    if inv is not None:
        adj={i:[j for j in G if inv[C.index(i)]>>R.index(j)&1] for i in G}
        assert G and all(adj.values())
        shortest=None
        for start in G:
            queue=deque([[start]])
            seen={start}
            while queue:
                path=queue.popleft()
                if start in adj[path[-1]]:
                    if shortest is None or len(path)<len(shortest):shortest=path
                    break
                for v in adj[path[-1]]:
                    if v not in seen:
                        seen.add(v)
                        queue.append(path+[v])
        for v in shortest:
            matrix[R.index(v)]^=1<<C.index(v)
        _,ker=eliminate(matrix)
    assert ker
    cut=sum(((ker>>i)&1)<<v for i,v in enumerate(C))
    assert not any(cut>>p&1 for p in pins)
    assert all((krows[i]&cut).bit_count()%2==0 for i in R if not cut>>i&1)
    return cut


if __name__=='__main__':
    import networkx as nx
    torso=[28,60,11,775,515,962,1312,800,1256,1208,832]
    assert min(map(min,summary(torso)))>0
    tested=0
    for g in nx.graph_atlas_g():
        n=len(g)
        if n not in (3,5):continue
        for x,y in combinations(range(n),2):
            for z in range(n):
                K=[sum(1<<j for j in g[i]) for i in range(n)]+[(1<<x)|(1<<y),1<<z]
                for v,j in ((x,n),(y,n),(z,n+1)):K[v]|=1<<j
                if any(v.bit_count() not in (3,5) for v in K[:n]):continue
                for pins in combinations(range(n+2),2):
                    cut=escape(K,pins,(n,n+1))
                    word=((1<<(n+2))-1)^cut
                    u=word>>n
                    drift=sum(((word&r).bit_count()&1)<<j for j,r in enumerate(K[n:]))
                    assert any(all(((torso[i]&w).bit_count()+(drift>>i&1))%2
                                   for i in range(11) if w>>i&1)
                               for w in range(u,1<<11,4))
                    tested+=1
    print('lifted proper words',tested)
