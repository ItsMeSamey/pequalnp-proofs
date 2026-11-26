"""Check a reference-bit completion or search for a small independent odd-cycle transversal."""
from collections import deque
from affine_projective_layer import _two_sat


def reference_colouring(adj,reference,*,chosen=(),excluded=()):
    n=len(adj)
    if len(reference)!=n or any(x not in (0,1) for x in reference):
        raise ValueError("one reference bit per vertex required")
    clauses=[]
    for u in range(n):
        for v in adj[u]:
            if u<v:
                clauses.append((2*u,2*v))
                if reference[u]==reference[v]:clauses.append((2*u+1,2*v+1))
    for u in chosen:clauses.append((2*u+1,2*u+1))
    for u in excluded:clauses.append((2*u,2*u))
    third=_two_sat(n,clauses)
    return None if third is None else tuple(2 if b else reference[i] for i,b in enumerate(third))


def _bipartite_or_cycle(adj,removed):
    n=len(adj);colour=[-1]*n;parent=[-1]*n
    for root in range(n):
        if root in removed or colour[root]>=0:continue
        queue=deque([root]);colour[root]=0
        while queue:
            u=queue.popleft()
            for v in adj[u]:
                if v in removed:continue
                if colour[v]<0:
                    parent[v]=u;colour[v]=colour[u]^1;queue.append(v)
                elif colour[v]==colour[u]:
                    path=[];a=u
                    while a>=0:
                        path.append(a);a=parent[a]
                    seen=set(path);tail=[];a=v
                    while a not in seen:
                        tail.append(a);a=parent[a]
                    return None,path[:path.index(a)+1]+tail[::-1]
    return tuple(2 if i in removed else c for i,c in enumerate(colour)),None


def stable_oct_colour(adj,k,*,chosen=(),excluded=()):
    """Return a three-colouring with at most k third-colour vertices, or None."""
    if k<0:raise ValueError("negative budget")
    start=frozenset(chosen);no=frozenset(excluded)
    if len(start)>k or start&no or any(start&set(adj[u]) for u in start):return None
    stack=[start]
    while stack:
        taken=stack.pop()
        col,cycle=_bipartite_or_cycle(adj,taken)
        if col is not None:return col
        if len(taken)<k:
            stack.extend(taken|{v} for v in cycle if v not in no and not taken.intersection(adj[v]))
    return None
