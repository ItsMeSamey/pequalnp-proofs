"""Exact graph recognition and gain reduction for triangle layers with matching edges."""
from collections import deque
from dataclasses import dataclass
from itertools import combinations, product


@dataclass
class Result:
    status: str
    reason: str
    witness: tuple | None = None
    layers: tuple = ()
    gains: tuple = ()
    orientations: tuple = ()
    sign_cycle: tuple = ()
    core: tuple = ()


def _matching(first, second, adj):
    """False for a malformed cross relation, None for no edges, else its permutation."""
    rows = [tuple(j for j,v in enumerate(second) if v in adj[u]) for u in first]
    if not any(rows):
        return None
    if any(len(row)!=1 for row in rows):
        return False
    perm=tuple(row[0] for row in rows)
    return perm if len(set(perm))==3 else False


def _validate(layers, n, adj, edges):
    owner = {}
    for i,layer in enumerate(layers):
        if len(layer)!=3 or len(set(layer))!=3:
            return None
        for pos,v in enumerate(layer):
            if not isinstance(v,int) or not 0<=v<n or v in owner:
                return None
            owner[v]=(i,pos)
        if any(v not in adj[u] for u,v in combinations(layer,2)):
            return None
    if len(owner)!=n:
        return None
    cross={}
    for u,v in edges:
        i,a=owner[u]
        j,b=owner[v]
        if i==j:
            continue
        if i>j:
            i,j,a,b=j,i,b,a
        cross.setdefault((i,j),[]).append((a,b))
    matchings=[]
    for (i,j),rows in sorted(cross.items()):
        if sorted(a for a,b in rows)!=[0,1,2] or sorted(b for a,b in rows)!=[0,1,2]:
            return None
        matchings.append((i,j,tuple(b for a,b in sorted(rows))))
    return tuple(matchings)


def solve_prism(n, edges, *, layers=None, recognition_limit=None, core_limit=0):
    """Vertices are 0..n−1. Limits bound search nodes and residual vertices, respectively."""
    if type(n) is not int or n<0 or type(core_limit) is not int or core_limit<0:
        raise ValueError("invalid graph size or core limit")
    if recognition_limit is not None and (type(recognition_limit) is not int or recognition_limit<0):
        raise ValueError("invalid recognition limit")
    adj=[set() for _ in range(n)]
    graph_edges=set()
    for u,v in edges:
        if type(u) is not int or type(v) is not int or not (0<=u<n and 0<=v<n) or u==v:
            raise ValueError("expected simple loop-free graph")
        graph_edges.add((min(u,v),max(u,v)))
        adj[u].add(v)
        adj[v].add(u)
    if layers is not None:
        chosen=tuple(tuple(layer) for layer in layers)
        matchings=_validate(chosen,n,adj,graph_edges)
        if matchings is None:
            return Result("UNSUPPORTED","invalid supplied partition")
    else:
        if n%3:
            return Result("UNSUPPORTED","order not divisible by three")
        by_vertex=[[] for _ in range(n)]
        triangles=[]
        for u,v in sorted(graph_edges):
            for w in sorted(adj[u]&adj[v]):
                if w>v:
                    tri=(u,v,w)
                    triangles.append(tri)
                    for x in tri:
                        by_vertex[x].append(tri)
        if any(not choices for choices in by_vertex):
            return Result("UNSUPPORTED","vertex outside all triangles")
        if all(len(choices)==1 for choices in by_vertex):
            chosen=tuple(triangles)
            matchings=_validate(chosen,n,adj,graph_edges)
            if matchings is None:
                return Result("UNSUPPORTED","nonmatching between forced layers")
        else:
            stack=[(frozenset(range(n)),())]
            visited=0
            while stack:
                if recognition_limit is not None and visited>=recognition_limit:
                    return Result("UNKNOWN","partition search limit")
                available,partial=stack.pop()
                visited+=1
                if not available:
                    chosen=partial
                    matchings=_validate(chosen,n,adj,graph_edges)
                    assert matchings is not None
                    break
                choices=None
                for v in sorted(available):
                    current=[t for t in by_vertex[v] if all(x in available for x in t)
                             and all(_matching(s,t,adj) is not False for s in partial)]
                    if choices is None or len(current)<len(choices):
                        choices=current
                    if not choices:
                        break
                for tri in reversed(choices):
                    stack.append((available.difference(tri),partial+(tri,)))
            else:
                return Result("UNSUPPORTED","no matching partition")

    count=len(chosen)
    links=[[] for _ in chosen]
    for i,j,perm in matchings:
        sign=1 if (perm[1]-perm[0])%3==1 else -1
        links[i].append((j,sign))
        links[j].append((i,sign))
    sign=[0]*count
    parent=[-1]*count
    for root in range(count):
        if sign[root]:
            continue
        sign[root]=1
        queue=deque([root])
        while queue:
            u=queue.popleft()
            for v,delta in links[u]:
                if not sign[v]:
                    sign[v]=sign[u]*delta
                    parent[v]=u
                    queue.append(v)
                elif sign[v]!=sign[u]*delta:
                    def path_to_root(z):
                        path=[]
                        while z>=0:
                            path.append(z)
                            z=parent[z]
                        return path
                    a,b=path_to_root(u),path_to_root(v)
                    ancestors=set(a)
                    common=next(i for i in b if i in ancestors)
                    cycle=a[:a.index(common)+1]+list(reversed(b[:b.index(common)]))+[u]
                    return Result("UNSAT","odd matching sign cycle",layers=chosen,sign_cycle=tuple(cycle))
    gains=tuple((i,j,(-sign[j]*perm[0])%3) for i,j,perm in matchings)
    neighbors=[{} for _ in chosen]
    for i,j,gain in gains:
        neighbors[i][j]=gain
        neighbors[j][i]=(-gain)%3
    live=set(range(count))
    degrees=[len(nbrs) for nbrs in neighbors]
    pending=deque(i for i,val in enumerate(degrees) if val<=2)
    peeled=[]
    while pending:
        u=pending.popleft()
        if u not in live:
            continue
        live.remove(u)
        peeled.append(u)
        for v in neighbors[u]:
            if v in live:
                degrees[v]-=1
                if degrees[v]==2:
                    pending.append(v)
    core=tuple(sorted(live))
    output=dict(layers=chosen,gains=gains,orientations=tuple(sign),core=core)
    if len(core)>core_limit:
        return Result("UNKNOWN","residual exceeds core limit",**output)
    core_edges=[(i,j,g) for i,j,g in gains if i in live and j in live]
    for candidate in product(range(3),repeat=len(core)):
        rotation=dict(zip(core,candidate))
        if any((rotation[j]-rotation[i])%3==g for i,j,g in core_edges):
            continue
        for u in reversed(peeled):
            excluded={(rotation[v]-g)%3 for v,g in neighbors[u].items() if v in rotation}
            rotation[u]=next(c for c in range(3) if c not in excluded)
        witness=[None]*n
        for i,layer in enumerate(chosen):
            for k,v in enumerate(layer):
                witness[v]=(sign[i]*k+rotation[i])%3
        if any(witness[u]==witness[v] for u,v in graph_edges):
            raise AssertionError("invalid lifted graph colouring")
        return Result("SAT","lifted gain colouring",witness=tuple(witness),**output)
    return Result("UNSAT","exhausted residual core",**output)
