from itertools import combinations
import networkx as nx

def compatible(a,b):
    return len({a[d]^b[d] for d in a.keys()&b.keys()})<=1

def ordered_sweep(stars,s,t,cycles):
    # cycles contains (two star indices, two disk indices), in certified nested order.
    g=nx.Graph()
    S,T=('d',s),('d',t);g.add_nodes_from([S,T])
    for h,a in enumerate(stars):
        for d in a:g.add_edge(('h',h),('d',d))
    if not cycles:return nx.has_path(g,S,T)
    P=[];bounds=[];opts=[];owner={}
    for i,(pair,ds) in enumerate(cycles):
        bounds.append({('h',h) for h in pair}|{('d',d) for d in ds})
        for node in bounds[-1]:
            assert node not in owner
            owner[node]=i
        pool={h for h,a in enumerate(stars) if set(ds)&a.keys()}
        P.append(pool)
        candidates=[]
        for r in range(min(len(pool),4)+1):
            for q in combinations(sorted(pool),r):
                if any(sum(d in stars[h] for h in q)>2 for d in ds):continue
                if all(compatible(stars[h],stars[k]) for h,k in combinations(q,2)):
                    candidates.append(frozenset(q))
        opts.append(candidates)
    for h,k in combinations(range(len(stars)),2):
        assert compatible(stars[h],stars[k]) or any(h in p and k in p for p in P)
    m=len(cycles);pieces=[nx.Graph() for _ in range(m+1)]
    for c in nx.connected_components(g.subgraph(set(g)-set(owner))):
        ns={owner[w] for v in c for w in g[v] if w in owner}
        assert not ns or max(ns)-min(ns)<=1
        j=max(ns,default=0)
        pieces[j].add_nodes_from(c)
        pieces[j].add_edges_from((v,w) for v in c for w in g[v])
    for a,b in g.edges:
        if a in owner and b in owner:
            assert abs(owner[a]-owner[b])<=1
            pieces[max(owner[a],owner[b])].add_edge(a,b)
    def advance(part,piece,back,front,deleted):
        temp=piece.copy()
        temp.add_nodes_from(back|front|{S,T})
        temp.remove_nodes_from(('h',h) for h in deleted)
        for group in part:
            v=next(iter(group));temp.add_edges_from((v,w) for w in group if v!=w)
        return frozenset(frozenset(c&(front|{S,T})) for c in nx.connected_components(temp) if c&(front|{S,T}))
    states={(frozenset(),frozenset())}
    for i in range(m+1):
        new=set();cur=P[i] if i<m else set();old=P[i-1] if i else set()
        b=bounds[i-1] if i else set();f=bounds[i] if i<m else set()
        for q,part in states:
            for r in (opts[i] if i<m else [frozenset()]):
                if q&(cur&old)!=r&(cur&old):continue
                new.add((r,advance(part,pieces[i],b,f,(old-q)|(cur-r))))
        states=new
    return any(any(S in c and T in c for c in part) for q,part in states)
