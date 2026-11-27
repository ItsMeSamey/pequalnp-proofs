"""Pinned induced-even sets for a supplied star-cut perturbation of a simple line graph."""
from itertools import combinations

def extend(edges, support, required, odd):
    demand=set(odd); adj={v:[] for v in support}
    for i,(u,v) in enumerate(edges):
        if u not in support or v not in support:continue
        if i in required:demand.symmetric_difference_update((u,v))
        else:adj[u].append((v,i)); adj[v].append((u,i))
    used=set(required); visited=set()
    for root in support:
        if root in visited:continue
        order=[root]; visited.add(root); parent={}
        for u in order:
            for v,i in adj[u]:
                if v not in visited:
                    parent[v]=(u,i); visited.add(v); order.append(v)
        for u in reversed(order[1:]):
            if u in demand:
                v,i=parent[u]; used.add(i); demand.symmetric_difference_update((u,v))
        if root in demand:return None
    return used

def solve(n, edges, q, bilinear, apex_labels, apex_adj, pins, external_tree=None):
    """Edge IDs precede apex IDs. Matrix and adjacency rows are binary bit masks."""
    pins=set(pins)
    q=tuple(q); m=len(edges); h=len(q); a=len(apex_labels)
    vertices=set(range(n)); boundary=set(q)
    need_edges={i for i in pins if i<m}
    need_apex=sum(1<<(i-m) for i in set(pins) if i>=m)
    diag=sum(((row>>i)&1)<<i for i,row in enumerate(bilinear))
    def signatures(p):
        if external_tree is not None:
            from external import external_table
            yield from external_table(apex_adj,apex_labels,need_apex,p,external_tree).items()
            return
        for z in range(1<<a):
            if z&need_apex!=need_apex:continue
            if any(z>>i&1 and ((apex_adj[i]&z).bit_count()+(label&p).bit_count())%2
                   for i,label in enumerate(apex_labels)):continue
            g=0
            for i,label in enumerate(apex_labels):
                if z>>i&1:g^=label
            yield g,z
    for p in range(1<<h):
        for g,z in signatures(p):
            additional=diag^g
            correction=additional^sum(((row&p).bit_count()%2)<<i for i,row in enumerate(bilinear))
            class1={v for i,v in enumerate(q) if (correction^p)>>i&1}
            qodd={v for i,v in enumerate(q) if p>>i&1}
            for cnt in range(len(need_edges)+1):
                for part in combinations(need_edges,cnt):
                    req1=set(part); req0=need_edges-req1
                    left=class1|{u for i in req1 for u in edges[i]}
                    right=(boundary-class1)|{u for i in req0 for u in edges[i]}
                    if left&right:continue
                    target1=(left-boundary)|(qodd&class1)
                    initial=set()
                    for i in req1:initial.symmetric_difference_update(edges[i])
                    cap=len(initial^target1)
                    pool=vertices-left-right
                    for j in range(min(cap,len(pool))+1):
                        for extra in combinations(pool,j):
                            used=left.union(extra)
                            f=extend(edges,used,req1,target1.union(extra))
                            if f is None:continue
                            g=extend(edges,vertices-used,req0,qodd-class1)
                            if g is not None:return f|g|{m+i for i in range(a) if z>>i&1}
    return None
