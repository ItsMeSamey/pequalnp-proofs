"""Deterministic label decision on dense hosts with supplied base matching."""
from colorful_port_matching import search_coloring
from dense_pair_hashes import colorings


def solve(n,edges,base,target,*,left=None,deleted=(),coloring_cap=None):
    edges=tuple((u,v,tuple(g)) for u,v,g in edges)
    base=tuple(base)
    target=tuple(target)
    if n<0 or n%2 or coloring_cap is not None and (
            type(coloring_cap) is not int or coloring_cap<0):
        raise ValueError("invalid order or coloring budget")
    if any(i<0 or i>=len(edges) for i in base) or sorted(
            v for i in base for v in edges[i][:2])!=list(range(n)):
        raise ValueError("invalid base matching")
    if any(x not in (0,1,2) for x in target):
        raise ValueError("invalid target")
    live=set(range(n))
    bad=set(deleted)
    if not bad<=live:
        raise ValueError("invalid deleted vertices")
    side=None if left is None else set(left)
    if side is not None and (not side<=live or len(side)!=n//2):
        raise ValueError("invalid bipartition")
    live-=bad
    nb=[set() for _ in range(n)]
    for u,v,g in edges:
        if not(0<=u<n and 0<=v<n and u!=v and len(g)==len(target)
               and all(x in (0,1,2) for x in g)):
            raise ValueError("invalid labelled edge")
        if side is not None and (u in side)==(v in side):
            raise ValueError("edge inside bipartition")
        if u in live and v in live:
            nb[u].add(v)
            nb[v].add(u)
    sizes=(len(live&side),len(live-side)) if side is not None else None
    delta=max(((len(live)-1 if side is None else sizes[int(v in side)])-len(nb[v])
               for v in live),default=0)
    block=delta+3
    bound=min(n//2,block*len(bad)+2*len(target)*(2*block-3))
    stats={"missing_degree":delta,"support_bound":bound,"colorings":0}
    if tuple(sum(edges[i][2][j] for i in base)%3 for j in range(len(target)))==target:
        return "SAT",base,stats
    if not bound:
        return "UNSAT",None,stats
    if coloring_cap==0:
        return "UNKNOWN",None,stats
    for paint in colorings(len(base),bound):
        if coloring_cap is not None and stats["colorings"]>=coloring_cap:
            return "UNKNOWN",None,stats
        stats["colorings"]+=1
        witness=search_coloring(n,edges,base,target,paint)
        if witness is not None:
            return "SAT",witness,stats
    return "UNSAT",None,stats
