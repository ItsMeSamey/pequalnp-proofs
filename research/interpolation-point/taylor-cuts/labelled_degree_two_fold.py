"""Exact degree-at-most-two preprocessing of ternary-labelled perfect matching."""
from dataclasses import dataclass


def add(g,h):
    return tuple((x+y)%3 for x,y in zip(g,h))


@dataclass
class Fold:
    n: int
    edges: tuple
    offsets: dict
    histories: tuple
    original_n: int
    original_edges: tuple
    target: tuple
    folded: int

    def queries(self):
        for offset in self.offsets:
            yield offset,tuple((x-y)%3 for x,y in zip(self.target,offset))

    def lift(self, ids, offset):
        """Validate a residual witness and expand its stored original edge IDs."""
        ids=tuple(ids)
        if offset not in self.offsets or any(type(i) is not int or not 0<=i<len(self.edges) for i in ids):
            raise ValueError("invalid residual offset or edge ID")
        if sorted(v for i in ids for v in self.edges[i][:2])!=list(range(self.n)):
            raise ValueError("residual witness is not a perfect matching")
        word=self.offsets[offset]
        for i in ids:
            if self.histories[i]&word:
                raise AssertionError("overlapping expanded matching")
            word|=self.histories[i]
        original=tuple(i for i in range(len(self.original_edges)) if word>>i&1)
        if (sorted(v for i in original for v in self.original_edges[i][:2])!=list(range(self.original_n))
            or any(sum(self.original_edges[i][2][j] for i in original)%3!=t for j,t in enumerate(self.target))):
            raise ValueError("lifted witness does not satisfy original matching and label")
        return original


def fold(n, edges, target):
    """Return None on structural infeasibility, otherwise a residual with offsets.

    Edge IDs are their original indices. Distinct labels at forced degree-one pairs
    are accumulated in a ternary-sum DP and may give multiple residual queries.
    """
    if type(n) is not int or n<0:
        raise ValueError("invalid order")
    target=tuple(target)
    original=tuple((u,v,tuple(g)) for u,v,g in edges)
    def valid(g):
        return all(type(x) is int and x in (0,1,2) for x in g) and len(g)==len(target)
    if not valid(target) or any(type(u) is not int or type(v) is not int or not 0<=u<n or
                              not 0<=v<n or u==v or not valid(g) for u,v,g in original):
        raise ValueError("invalid endpoint or label")
    if n%2:
        return None
    alive=set(range(n))
    table={}
    def store(a,b,g,history):
        table.setdefault(tuple(sorted((a,b))),{}).setdefault(g,history)
    for i,(u,v,g) in enumerate(original):
        store(u,v,g,1<<i)
    offsets={(0,)*len(target):0}
    next_vertex=n
    folds=0
    while alive:
        adjacent={u:set() for u in alive}
        for u,v in table:
            adjacent[u].add(v)
            adjacent[v].add(u)
        v=min(alive,key=lambda u:(len(adjacent[u]),u))
        around=sorted(adjacent[v])
        if not around:
            return None
        if len(around)>2:
            break
        def variants(a,b):
            return table[tuple(sorted((a,b)))].items()
        if len(around)==1:
            u=around[0]
            updates={}
            for g,w in variants(u,v):
                for offset,prior in offsets.items():
                    updates.setdefault(add(offset,g),prior|w)
            offsets=updates
            removed={u,v}
        else:
            u,w=around
            removed={u,v,w}
            z=next_vertex
            next_vertex+=1
            alive.add(z)
            for y,other in ((u,w),(w,u)):
                for k in adjacent[y]-removed:
                    for g,left in variants(y,k):
                        for h,right in variants(v,other):
                            store(z,k,add(g,h),left|right)
            folds+=1
        alive.difference_update(removed)
        table={pair:gs for pair,gs in table.items() if not removed.intersection(pair)}
    names={v:i for i,v in enumerate(sorted(alive))}
    residual=[]
    histories=[]
    for (u,v),gs in sorted(table.items()):
        for g,w in sorted(gs.items()):
            residual.append((names[u],names[v],g))
            histories.append(w)
    return Fold(len(alive),tuple(residual),offsets,tuple(histories),n,original,target,folds)


def search(n,edges,target,backend):
    """backend(core_n, core_edges, residual_target) returns (status, IDs)."""
    result=fold(n,edges,target)
    if result is None:
        return "UNSAT",None
    if not result.n:
        return ("SAT",result.lift((),result.target)) if result.target in result.offsets else ("UNSAT",None)
    stalled=False
    for offset,goal in result.queries():
        status,ids=backend(result.n,result.edges,goal)
        if status=="SAT":
            return "SAT",result.lift(ids,offset)
        if status not in ("UNSAT","UNKNOWN"):
            raise ValueError("unexpected residual solver status")
        stalled |= status=="UNKNOWN"
    return ("UNKNOWN" if stalled else "UNSAT"),None


def dense_search(n,edges,target,*,cap=None):
    """Fold, choose one unlabelled base on the core, run the dense moved-pair solver."""
    import networkx as nx
    from ternary_moved_matching import solve
    result=fold(n,edges,target)
    if result is None:
        return "UNSAT",None
    if not result.n:
        return ("SAT",result.lift((),result.target)) if result.target in result.offsets else ("UNSAT",None)
    graph=nx.Graph()
    graph.add_nodes_from(range(result.n))
    first={}
    for i,(u,v,_) in enumerate(result.edges):
        graph.add_edge(u,v)
        first.setdefault((min(u,v),max(u,v)),i)
    matching=nx.max_weight_matching(graph,maxcardinality=True)
    if 2*len(matching)!=result.n:
        return "UNSAT",None
    base=tuple(first[min(u,v),max(u,v)] for u,v in matching)
    left=None
    if nx.is_bipartite(graph):
        colors=nx.algorithms.bipartite.color(graph)
        left={v for v,c in colors.items() if c}
    stalled=False
    for offset,goal in result.queries():
        status,ids,_=solve(result.n,result.edges,base,goal,left=left,cap=cap)
        if status=="SAT":
            return "SAT",result.lift(ids,offset)
        stalled |= status=="UNKNOWN"
    return ("UNKNOWN" if stalled else "UNSAT"),None
