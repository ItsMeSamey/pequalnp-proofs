"""Bipartite cubic multipoles with indexed internal edges and boundary halfedges."""
from collections import Counter
from itertools import product
import networkx as nx


def shape(graph,ports):
    if graph.is_directed():raise ValueError('expected undirected internal graph')
    shore=nx.algorithms.bipartite.color(graph)
    degree=Counter(ports)
    if any(v not in graph for v in ports) or any(graph.degree(v)+degree[v]!=3 for v in graph):
        raise ValueError('not cubic with the specified halfedges')
    return shore


def local_valid(graph,ports,colors):
    if len(ports)!=len(colors) or any(c not in (0,1,2) for c in colors):return False
    return len(set(zip(ports,colors)))==len(ports)


def incident(graph,v):
    if graph.is_multigraph():
        return [(frozenset((v,w)),k) for w,ks in graph[v].items() for k in ks]
    return [(frozenset((v,w)),None) for w in graph[v]]


def certified_disk_order(graph,ports,order):
    """Return a facial rotation certificate check; a failure merely disables the shortcut."""
    if len(order)<3:return True
    aug=nx.Graph(graph)
    pins=[object() for _ in ports]
    hub=object()
    rim=[pins[i] for i in order]
    aug.add_edges_from(zip(ports,pins))
    aug.add_edges_from(zip(rim,rim[1:]+rim[:1]))
    aug.add_edges_from((hub,v) for v in pins)
    planar,embedding=nx.check_planarity(aug)
    if not planar:return False
    # Restrict the certified spherical rotation system after deleting the hub.
    rotation={v:[u for u in embedding.neighbors_cw_order(v) if u is not hub]
              for v in embedding if v is not hub}
    for seq in (rim,rim[::-1]):
        if all(rotation[v][(rotation[v].index(seq[i-1])-1)%len(rotation[v])]==seq[(i+1)%len(seq)]
               for i,v in enumerate(seq)):
            return True
    return False


def valid_coloring(graph,ports,colors,edge_colors):
    if len(edge_colors)!=graph.number_of_edges():return False
    for v in graph:
        values=[edge_colors.get(e) for e in incident(graph,v)]
        values += [t for p,t in zip(ports,colors) if p==v]
        if set(values)!={0,1,2}:return False
    return True


def extend_matching(graph,ports,colors,base,matching):
    """Return a full coloring for this base matching, or None."""
    if not local_valid(graph,ports,colors):return None
    taken={v for v,t in zip(ports,colors) if t==base}
    witness={}
    for edge in matching:
        u,v=edge[:2]
        if u in taken or v in taken or not graph.has_edge(u,v):return None
        taken.update((u,v))
        k=(edge[2] if len(edge)>2 else next(iter(graph[u][v]))) if graph.is_multigraph() else None
        eid=(frozenset((u,v)),k)
        if eid not in incident(graph,u):return None
        witness[eid]=base
    if taken!=set(graph):return None
    other=[c for c in range(3) if c!=base]
    # Every residual incidence has a mate at its vertex. They must receive opposite bits.
    adjacency={}
    forced={}
    for v in graph:
        residual=[e for e in incident(graph,v) if e not in witness]
        for i,(w,c) in enumerate(zip(ports,colors)):
            if w==v and c!=base:
                residual.append(i)
                forced[i]=other.index(c)
        a,b=residual
        adjacency.setdefault(a,[]).append(b)
        adjacency.setdefault(b,[]).append(a)
    assigned={}
    for initial in list(forced)+list(adjacency):
        if initial in assigned:continue
        assigned[initial]=forced.get(initial,0)
        stack=[initial]
        while stack:
            a=stack.pop()
            if a in forced and forced[a]!=assigned[a]:return None
            for b in adjacency[a]:
                value=1^assigned[a]
                if b in assigned:
                    if assigned[b]!=value:return None
                else:
                    assigned[b]=value
                    stack.append(b)
    witness.update({e:other[b] for e,b in assigned.items() if isinstance(e,tuple)})
    assert valid_coloring(graph,ports,colors,witness)
    return witness


def solve(graph,ports,colors,outer_order=None):
    """Return SAT/witness, UNSAT, or UNKNOWN. Optional disk order is checked before using its negative implication."""
    shore=shape(graph,ports)
    if not local_valid(graph,ports,colors):return 'UNSAT',None
    delta=sum(1 if shore[v] else -1 for v in graph)
    if any(sum(1 if shore[v] else -1 for v,t in zip(ports,colors) if t==c)!=delta for c in range(3)):
        return 'UNSAT',None
    if outer_order is not None and sorted(outer_order)!=list(range(len(ports))):
        raise ValueError('disk order must list all halfedge positions')
    if outer_order is not None and not certified_disk_order(graph,ports,outer_order):outer_order=None
    for base in sorted(range(3),key=lambda c:-colors.count(c)):
        other=[c for c in range(3) if c!=base]
        boundary=[i for i,c in enumerate(colors) if c!=base]
        universal=len(boundary)<=2
        if outer_order is not None:
            signs=[shore[ports[i]]^other.index(colors[i]) for i in outer_order if colors[i]!=base]
            universal|=all(signs[i]!=signs[i-1] for i in range(len(signs)))
        H=graph.subgraph(set(graph)-{v for v,t in zip(ports,colors) if t==base})
        mat=nx.algorithms.bipartite.maximum_matching(H,top_nodes={v for v in H if shore[v]})
        if len(mat)!=len(H):return 'UNSAT',None
        witness=extend_matching(graph,ports,colors,base,[(v,mat[v]) for v in H if shore[v]])
        if witness is not None:return 'SAT',witness
        if universal:return 'UNSAT',None
    return 'UNKNOWN',None
