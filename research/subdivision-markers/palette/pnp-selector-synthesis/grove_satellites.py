"""Exact satellite replacement using one supplied characteristic-two field."""
from itertools import combinations
from grove331_overlay import laplacian


def evaluate(field,n,core_vertices,core_edges,satellites,evaluate_core):
    """Core callback receives original vertex IDs with effective edge weights."""
    if field.q<2*n+1:raise ValueError("larger supplied field required")
    core=set(core_vertices);base=tuple(tuple(e) for e in core_edges)
    if any(u not in core or v not in core for u,v,w in base):raise ValueError("core edge")
    pieces=[];seen=set(core)
    for vertices,ports,edges in satellites:
        ports=tuple(ports);V=set(vertices);interior=sorted(V-set(ports))
        if not 1<=len(set(ports))==len(ports)<=3 or V&core!=set(ports) or seen&set(interior):
            raise ValueError("invalid attachment")
        seen.update(interior);order=interior+list(ports);pos={u:i for i,u in enumerate(order)}
        E=[(pos[u],pos[v],w) for u,v,w in edges]
        h=len(interior);adj=[[] for u in order]
        for i,(u,v,w) in enumerate(E):
            adj[u].append((v,i));adj[v].append((u,i))
        reached=set(range(h,len(order)));queue=list(reached);tree=set()
        for u in queue:
            for v,i in adj[u]:
                if v not in reached:
                    reached.add(v);queue.append(v);tree.add(i)
        if len(tree)!=h:raise ValueError("satellite component without port")
        pieces.append((ports,E,h,tree))
    if seen!=set(range(n)):raise ValueError("vertices not accounted for")
    points=[];values=[]
    for t in range(2*n+1):
        effective=list(base);factor=1
        for ports,E,h,tree in pieces:
            L=laplacian(h+len(ports),[(u,v,w^(t if i in tree else 0)) for i,(u,v,w) in enumerate(E)])
            pivot=field.det([row[:h] for row in L[:h]])
            if not pivot:break
            factor=field.mul(factor,pivot)
            for i,j in combinations(range(len(ports)),2):
                R=list(range(h))+[h+i];C=list(range(h))+[h+j]
                bordered=field.det([[L[u][v] for v in C] for u in R])
                effective.append((ports[i],ports[j],field.mul(bordered,field.inv(pivot))))
        else:
            value=field.mul(factor,evaluate_core(effective))
            if not t:return value
            points.append(t);values.append(value)
            if len(points)==n-2:break
    if len(points)!=n-2:raise ValueError("insufficient interpolation points")
    result=0
    for a,wa in zip(points,values):
        coeff=1
        for b in points:
            if a!=b:coeff=field.mul(coeff,field.mul(b,field.inv(a^b)))
        result^=field.mul(wa,coeff)
    return result
