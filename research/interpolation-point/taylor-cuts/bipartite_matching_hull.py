"""Exact affine hull of ternary perfect-matching gains on a bipartite multigraph."""
from collections import deque
from secrets import randbelow
import networkx as nx
from ternary_frame import reduce
from ternary_labelled_matching import search


def prepare(n,edges,width):
    """Return None on no perfect matching; otherwise base, origin, basis and cycle IDs."""
    graph=nx.Graph()
    graph.add_nodes_from(range(n))
    lookup={}
    for k,(u,v,g) in enumerate(edges):
        if not (0<=u<n and 0<=v<n and u!=v and len(g)==width and all(x in (0,1,2) for x in g)):
            raise ValueError("invalid edge")
        graph.add_edge(u,v)
        lookup[u,v]=lookup[v,u]=k
    colors=nx.bipartite.color(graph)
    left={u for u in graph if not colors[u]}
    match=nx.bipartite.maximum_matching(graph,top_nodes=left)
    if len(match)!=n:
        return None
    base={u:lookup[u,match[u]] for u in left}
    origin=tuple(sum(edges[k][2][j] for k in base.values())%3 for j in range(width))
    digraph=nx.DiGraph()
    digraph.add_nodes_from(left)
    arcs={}
    for k,(u,v,g) in enumerate(edges):
        if u not in left:
            u,v=v,u
        if k!=base[u]:
            end=match[v]
            digraph.add_edge(u,end,id=k)
            arcs[k]=(u,end)
    pivots={}
    witnesses=[]
    def split(walk):
        if not walk:
            return
        stack=[arcs[walk[0]][0]]
        path=[]
        position={stack[0]:0}
        for k in walk:
            end=arcs[k][1]
            path.append(k)
            if end not in position:
                position[end]=len(stack)
                stack.append(end)
                continue
            index=position[end]
            cycle=path[index:]
            gain=tuple(sum(edges[e][2][j]-edges[base[arcs[e][0]]][2][j]
                           for e in cycle)%3 for j in range(width))
            residual=reduce(gain,pivots)
            p=next((j for j,x in enumerate(residual) if x),None)
            if p is not None:
                pivots[p]=tuple(x*residual[p]%3 for x in residual)
                witnesses.append(tuple(cycle))
            for v in stack[index+1:]:
                del position[v]
            del stack[index+1:]
            del path[index:]
    for component in nx.strongly_connected_components(digraph):
        sub=digraph.subgraph(component)
        root=min(component)
        def paths(reverse):
            order=deque([root])
            paths={root:[]}
            while order:
                u=order.popleft()
                for v in (sub.predecessors(u) if reverse else sub.successors(u)):
                    if v not in paths:
                        paths[v]=([sub[v][u]["id"]]+paths[u] if reverse
                                  else paths[u]+[sub[u][v]["id"]])
                        order.append(v)
            return paths
        forward,backward=paths(False),paths(True)
        for u in component:
            split(forward[u]+backward[u])
        for k,(u,v) in arcs.items():
            if u in component and v in component:
                split(forward[u]+[k]+backward[v])
    return tuple(sorted(base.values())),origin,pivots,tuple(witnesses)


def solve(n,edges,target,*,rounds=1,randbelow_fn=randbelow,backend=search):
    """Return status, original edge IDs or None, and actual affine rank or None."""
    edges=[(a,b,tuple(v)) for a,b,v in edges]
    target=tuple(target)
    if n<0 or any(x not in (0,1,2) for x in target):
        raise ValueError("invalid dimensions or target")
    hull=prepare(n,edges,len(target))
    if hull is None:
        return "UNSAT",None,None
    base,origin,pivots,_=hull
    rank=len(pivots)
    if any(reduce(tuple((a-b)%3 for a,b in zip(target,origin)),pivots)):
        return "UNSAT",None,rank
    if target==origin:
        return "SAT",base,rank
    coords=sorted(pivots)
    restricted=[(u,v,tuple(g[j] for j in coords)) for u,v,g in edges]
    status,ids=backend(n,restricted,tuple(target[j] for j in coords),rounds=rounds,randbelow_fn=randbelow_fn)
    if status=="SAT":
        if (sorted(a for k in ids for a in edges[k][:2])!=list(range(n)) or
            tuple(sum(edges[k][2][j] for k in ids)%3 for j in range(len(target)))!=target):
            raise ArithmeticError("witness failed original target")
    return status,ids,rank
