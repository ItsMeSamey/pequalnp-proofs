"""Bounded reference checks of binary graph transformations and terminal BFS."""
from collections import deque
from itertools import combinations
from random import Random
import networkx as nx


def bitset(vertices):
    return sum(1<<i for i in vertices)


def ids(mask):
    while mask:
        bit=mask&-mask
        yield bit.bit_length()-1
        mask^=bit


def parity(mask):
    return mask.bit_count()%2


def feasible(adj,x,c=0):
    return all(parity(adj[i]&x)==(c>>i&1) for i in ids(x))


def path(adj,start,end,allowed):
    if not (allowed>>start&allowed>>end&1):return None
    prev={start:None}
    queue=deque([start])
    while queue:
        i=queue.popleft()
        if i==end:
            total=0
            while i is not None:
                total|=1<<i
                i=prev[i]
            return total
        for j in ids(adj[i]&allowed):
            if j not in prev:
                prev[j]=i
                queue.append(j)
    return None


def component(adj,i,allowed):
    seen=1<<i
    queue=[i]
    while queue:
        new=adj[queue.pop()]&allowed&~seen
        seen|=new
        queue.extend(ids(new))
    return seen


def bfs_pins(adj,pins):
    full=(1<<len(adj))-1
    T=bitset(pins)
    local=sorted(pins,key=lambda x:(adj[x]&T).bit_count())
    degrees=[(adj[i]&T).bit_count() for i in local]
    if degrees in ([0,0,0],[2,2,2]):return T
    if degrees==[1,1,2]:
        u,w,v=local
        allowed=full&~((1<<v)|(adj[v]&~T))
        p=path(adj,u,w,allowed)
        return None if p is None else p|T
    w,u,v=local
    B=adj.copy()
    B[u]^=1<<v
    B[v]^=1<<u
    safe=full&~((1<<w)|B[w])
    p=path(B,u,v,safe)
    if p is not None:return p|T
    cu=component(B,u,safe)
    cv=component(B,v,safe)
    assert not cu&cv
    for a in ids(B[w]):
        for b in ids(B[w]&~((1<<a)|B[a])):
            p=path(B,u,a,(cu|(1<<a))&~B[b])
            s=path(B,b,v,(cv|(1<<b))&~B[a])
            if p is not None and s is not None:return p|s|T
    return None


def bfs_tests():
    cases=0
    for G in nx.graph_atlas_g():
        n=len(G)
        if not 3<=n<=7 or max(dict(G.degree()).values())>3:continue
        adj=[bitset(G[i]) for i in range(n)]
        supports=[x for x in range(1<<n) if feasible(adj,x)]
        for pins in combinations(range(n),3):
            sol=bfs_pins(adj,pins)
            exists=any(x&bitset(pins)==bitset(pins) for x in supports)
            assert exists==(sol is not None)
            if sol is not None:assert feasible(adj,sol) and sol&bitset(pins)==bitset(pins)
            cases+=1
    print('subcubic atlas pin triples',cases)


def pin_graph(adj,rows,pin_edges):
    n=len(adj)
    result=adj.copy()+list(rows)
    for j,row in enumerate(rows):
        for i in ids(row):result[i]|=1<<(n+j)
    for a,b in pin_edges:
        result[n+a]|=1<<(n+b)
        result[n+b]|=1<<(n+a)
    return result


def even_to_pins(adj,rows,t):
    n=len(adj);r=len(rows)
    assert t and r>=2
    orig=rows.copy();old_t=t
    pivot=next(ids(t))
    if pivot:
        rows[0],rows[pivot]=rows[pivot],rows[0]
        t^=(1<<pivot)|1
    for j in range(1,r):
        if (t>>j&1)!=(j==1):
            rows[j]^=rows[0]
            t^=1<<j
    assert t==3
    total=0
    for row in rows:total^=row
    first=rows[0]
    twist=[adj[i]^(total if first>>i&1 else 0)^(first if total>>i&1 else 0) for i in range(n)]
    lifted=pin_graph(twist,rows,[(0,1)])
    pins=((1<<r)-1)<<n
    for x in range(1<<n):
        y=bitset(i for i,row in enumerate(orig) if parity(row&x))
        assert feasible(lifted,x|pins)==(feasible(adj,x) and y==old_t)


def mixed_to_pins(adj,c,a,b):
    n=len(adj)
    lifted=pin_graph(adj,[a,b,c^a^b],[(0,2)])
    for x in range(1<<n):
        ok=feasible(adj,x,c) and parity(a&x) and not parity(b&x)
        assert feasible(lifted,x|(7<<n))==bool(ok)


def three_to_two(adj,a,b,d):
    twist=[v^(a if b>>i&1 else 0)^(b if a>>i&1 else 0) for i,v in enumerate(adj)]
    for x in range(1<<len(adj)):
        orig=feasible(adj,x) and parity(a&x) and parity(b&x) and not parity(d&x)
        mixed=feasible(twist,x,a^b) and parity(a&x) and not parity(d&x)
        assert bool(orig)==bool(mixed)


def reductions():
    n=3
    pairs=list(combinations(range(n),2))
    count=0
    for g in range(1<<len(pairs)):
        adj=[0]*n
        for k,(i,j) in enumerate(pairs):
            if g>>k&1:adj[i]|=1<<j;adj[j]|=1<<i
        for c in range(8):
            for a in range(1,8):
                for b in range(1,8):
                    if a==b:continue
                    mixed_to_pins(adj,c,a,b)
                    count+=1
        for a,b in combinations(range(1,8),2):
            for target in (1,2,3):even_to_pins(adj,[a,b],target)
            for d in range(1,8):
                if d not in (a,b,a^b):three_to_two(adj,a,b,d)
    rng=Random(330)
    for _ in range(120):
        n=rng.randrange(4,8)
        adj=[0]*n
        for i,j in combinations(range(n),2):
            if rng.randrange(2):adj[i]|=1<<j;adj[j]|=1<<i
        r=rng.randrange(2,n+1)
        rows=[1<<j for j in range(n)]
        for _ in range(3*n):
            a,b=rng.sample(range(n),2)
            rows[a]^=rows[b]
        even_to_pins(adj,rows[:r],rng.randrange(1,1<<r))
    print(count,'mixed two-readout instances; rank-two twist and converse checked')


if __name__=='__main__':
    reductions()
    bfs_tests()
