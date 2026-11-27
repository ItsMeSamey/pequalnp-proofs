"""Edmonds' augmenting-path and odd-blossom algorithm for unweighted graphs."""
from collections import deque


def maximum_cardinality_matching(vertices, edge_pairs):
    """Return matched endpoint pairs on distinct hashable labels or range(vertices)."""
    if isinstance(vertices,int) and vertices<0:
        raise ValueError("negative vertex count")
    labels=tuple(range(vertices) if isinstance(vertices,int) else vertices)
    n=len(labels)
    index={v:i for i,v in enumerate(labels)}
    if len(index)!=n:raise ValueError("duplicate vertex")
    neighbors=[set() for _ in labels]
    for x,y in edge_pairs:
        if x not in index or y not in index:raise ValueError("unknown endpoint")
        u,v=index[x],index[y]
        if u!=v:
            neighbors[u].add(v)
            neighbors[v].add(u)
    adj=[sorted(row) for row in neighbors]
    mate=[-1]*n

    def augment(root):
        parent=[-1]*n
        base=list(range(n))
        outer=[False]*n
        outer[root]=True
        queue=deque([root])

        def common_base(u,v):
            ancestors=set()
            while True:
                u=base[u]
                ancestors.add(u)
                if mate[u]==-1:break
                u=parent[mate[u]]
            while base[v] not in ancestors:
                v=parent[mate[base[v]]]
            return base[v]

        def link_side(v,join,child,marked):
            # Store the lifted alternating route through this side of the blossom.
            while base[v]!=join:
                partner=mate[v]
                marked[base[v]]=marked[base[partner]]=True
                parent[v]=child
                child=partner
                v=parent[partner]

        while queue:
            u=queue.popleft()
            for v in adj[u]:
                if base[u]==base[v] or mate[u]==v:continue
                if outer[v]:
                    join=common_base(u,v)
                    marked=[False]*n
                    link_side(u,join,v,marked)
                    link_side(v,join,u,marked)
                    for i in range(n):
                        if marked[base[i]]:
                            base[i]=join
                            if not outer[i]:
                                outer[i]=True
                                queue.append(i)
                elif parent[v]==-1:
                    parent[v]=u
                    if mate[v]==-1:
                        while v!=-1:
                            p=parent[v]
                            previous=mate[p]
                            mate[p],mate[v]=v,p
                            v=previous
                        return True
                    partner=mate[v]
                    outer[partner]=True
                    queue.append(partner)
        return False

    while any(mate[i]==-1 and augment(i) for i in range(n)):
        pass
    return tuple((labels[u],labels[v]) for u,v in enumerate(mate) if u<v)
