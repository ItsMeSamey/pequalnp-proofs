"""Two deleted vertices in a full-perfect-matching-neutral labelled multigraph."""
from collections import defaultdict,deque
from functools import lru_cache
import networkx as nx


def solve(n,edges,holes,target,*,state_cap=None,audit_neutral=False):
    """The promise is on all full matchings of the original graph. Caps count GE subproblems."""
    edges=tuple((u,v,tuple(g)) for u,v,g in edges)
    target=tuple(target)
    holes=tuple(holes)
    vertices=frozenset(range(n))
    if n<0 or len(holes)!=2 or len(set(holes))!=2 or not set(holes)<=vertices or (
        state_cap is not None and (type(state_cap) is not int or state_cap<0)):
        raise ValueError('invalid dimension, holes or state cap')
    if any(x not in (0,1,2) for x in target) or any(u not in vertices or v not in vertices or u==v
            or len(g)!=len(target) or any(x not in (0,1,2) for x in g) for u,v,g in edges):
        raise ValueError('invalid edge labels')
    zero=(0,)*len(target)
    stats=dict(subproblems=0,macro_states=0,ordinary_calls=0)
    graph=nx.Graph()
    graph.add_nodes_from(vertices)
    ids=defaultdict(list)
    for i,(u,v,g) in enumerate(edges):
        graph.add_edge(u,v)
        ids[frozenset((u,v))].append(i)
    def plus(x,y):
        return tuple((a+b)%3 for a,b in zip(x,y))
    def minus(x,y):
        return tuple((a-b)%3 for a,b in zip(x,y))
    def gain(trace):
        g=zero
        for i in trace:
            g=plus(g,edges[i][2])
        return g
    @lru_cache(None)
    def ordinary(V):
        stats['ordinary_calls']+=1
        pm=nx.max_weight_matching(graph.subgraph(V),maxcardinality=True)
        if 2*len(pm)!=len(V):
            return None
        return tuple(ids[frozenset(pair)][0] for pair in pm)
    baseline=ordinary(vertices)
    if baseline is None:
        stats['reason']='full graph has no perfect matching'
        return 'UNKNOWN',None,stats
    if audit_neutral:
        @lru_cache(None)
        def audit(V):
            if not V:
                return {zero}
            u=min(V)
            return {plus(edges[i][2],g) for v in graph[u] if v in V for i in ids[frozenset((u,v))]
                    for g in audit(V-{u,v})}
        if len(audit(vertices))!=1:
            raise ValueError('full perfect matching neutrality fails')
    class Cap(Exception):
        pass

    @lru_cache(None)
    def table(K,a):
        if state_cap is not None and stats['subproblems']>=state_cap:
            raise Cap
        stats['subproblems']+=1
        M=tuple(i for i in baseline if edges[i][0] in K)
        mate={v:(u,i) for i in M for x,y,_ in (edges[i],) for u,v in ((x,y),(y,x))}
        p=mate[a][0]
        H=K-{a}
        D={v for v in H if ordinary(H-{v}) is not None}
        parts=[frozenset(F) for F in nx.connected_components(graph.subgraph(D))]
        owner={v:j for j,F in enumerate(parts) for v in F}
        sink=owner[p]
        A={u for v in D for u in graph[v] if u in H and u not in D}
        C=H-A-D
        fixed=tuple(i for i in M if edges[i][0] in C)
        exposures={sink:p}
        agents={}
        for u in A:
            x,i=mate[u]
            j=owner[x]
            agents[j]=u
            exposures[j]=x
        ref=[]
        options=[]
        for j,F in enumerate(parts):
            e=exposures[j]
            interior=tuple(i for i in M if edges[i][0] in F and edges[i][1] in F)
            ref.append(interior if j==sink else interior+(mate[e][1],))
            entries={e:{gain(interior):interior}}
            for x in F-{e}:
                choices={}
                child=table(F-{e},x)
                for y in (set(graph[e]) & F)-{x}:
                    for i in ids[frozenset((e,y))]:
                        for k,w in child.get(y,{}).items():
                            choices.setdefault(plus(k,edges[i][2]),(i,)+w)
                entries[x]=choices
            options.append(entries)
        arcs=defaultdict(list)
        for j,u in agents.items():
            for x in (set(graph[u]) & D):
                k=owner[x]
                if k==j:
                    continue
                for i in ids[frozenset((u,x))]:
                    for h,w in options[k][x].items():
                        arcs[j].append((k,minus(plus(edges[i][2],h),gain(ref[j])),(i,)+w))
        out={}
        for start,F in enumerate(parts):
            pred={(start,zero):None}
            todo=deque([(start,zero)])
            while todo:
                j,g=todo.popleft()
                stats['macro_states']+=1
                for k,h,w in arcs[j]:
                    state=(k,plus(g,h))
                    if state not in pred:
                        pred[state]=((j,g),w)
                        todo.append(state)
            paths=[]
            for (end,g) in pred:
                if end!=sink:
                    continue
                state=(end,g)
                walk=[]
                while pred[state] is not None:
                    prev,w=pred[state]
                    walk.append((state[0],w))
                    state=prev
                sites=[start]
                chain=[]
                for k,w in reversed(walk):
                    if k in sites:
                        idx=sites.index(k)
                        del sites[idx+1:]
                        del chain[idx:]
                    else:
                        sites.append(k)
                        chain.append(w)
                kept=fixed+tuple(i for j,block in enumerate(ref) if j not in sites for i in block)
                paths.append(kept+tuple(i for block in chain for i in block))
            for x in F:
                found={}
                for w in paths:
                    for local in options[start][x].values():
                        trace=w+local
                        found.setdefault(gain(trace),trace)
                out[x]=found
        return out
    try:
        found=table(vertices,holes[0]).get(holes[1],{})
    except Cap:
        return 'UNKNOWN',None,stats
    if target not in found:
        return 'UNSAT',None,stats
    witness=found[target]
    if sorted(v for i in witness for v in edges[i][:2])!=sorted(vertices-set(holes)) or gain(witness)!=target:
        raise ArithmeticError('invalid original two-hole witness')
    return 'SAT',witness,stats
