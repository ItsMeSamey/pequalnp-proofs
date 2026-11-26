"""Check all rational Gram entries using an explicit integer factor, PG(2,5)."""
from collections import Counter,deque
from itertools import product


def girth(adj):
    best=len(adj)+1
    for source in range(len(adj)):
        parent={source:-1};depth={source:0};queue=deque([source])
        while queue:
            u=queue.popleft()
            for v in adj[u]:
                if v not in depth:
                    parent[v]=u;depth[v]=depth[u]+1;queue.append(v)
                elif parent[u]!=v and parent[v]!=u:
                    best=min(best,depth[u]+depth[v]+1)
    return best


def gram(u,v):
    return sum(x*v.get(i,0) for i,x in u.items())


if __name__=='__main__':
    pts=[v for v in product(range(5),repeat=3) if any(v) and next(x for x in v if x)==1]
    adj=[set() for _ in range(2*len(pts))]
    for i,x in enumerate(pts):
        for j,y in enumerate(pts,len(pts)):
            if sum(a*b for a,b in zip(x,y))%5==0:
                adj[i].add(j);adj[j].add(i)
    n=len(adj)
    assert n==62 and all(len(row)==6 for row in adj) and girth(adj)==6
    B=[]
    for v,row in enumerate(adj):
        dist2=set().union(*(adj[u] for u in row))-{v}-row
        assert len(dist2)==30
        b={i:1 for i in dist2}
        b.update({i:-3 for i in row});b[v]=6
        b.update({v+j*n:2 for j in (1,2,3)})
        B.append(b)
    raw=Counter()
    for v in range(n):
        for w in range(n):
            t=gram(B[v],B[w])
            if v==w:
                assert t==132
            elif w in adj[v]:
                assert t==-66
            else:
                assert t>=-36
                raw[t]+=1
    # All moment vectors below share denominator sqrt(9*132).
    a={-1:8,-2:8,-3:2}
    root={i:3*b for i,b in a.items()}
    colours=[]
    for b in B:
        row=[]
        for c in range(3):
            feat=dict(a)
            for i,x in b.items():
                feat[3*i+c]=x
                feat[3*i+(c+1)%3]=-x
            row.append(feat)
        colours.append(row)
    assert gram(root,root)==1188
    for v in range(n):
        for c in range(3):
            assert gram(root,colours[v][c])==396
        for w in range(n):
            t=gram(B[v],B[w])
            for c in range(3):
                entries=[gram(colours[v][c],colours[w][d]) for d in range(3)]
                assert entries==[132+(2 if d==c else -1)*t for d in range(3)]
                assert min(entries)>=0 and sum(entries)==396
                if v==w:assert entries[c]==396 and sum(x!=0 for x in entries)==1
                if w in adj[v]:assert entries[c]==0 and sorted(entries)==[0,198,198]
    print(f'{n} vertices, 186 edges, girth 6; {9*n*n} pair entries and integer PSD factor checked; nonedge T numerators {dict(raw)}')
