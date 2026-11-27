"""Bipartite perfect matching at a prescribed GF(3) residue via neutral SCC routes."""
from collections import defaultdict, deque
from itertools import combinations, product

import networkx as nx


def solve(n, edges, base_ids, target, *, portal_cap=None, portals=None):
    """Use supplied base edge IDs; an explicit neutral deletion set forces routing."""
    edges = [(u,v,tuple(g)) for u,v,g in edges]
    base = tuple(base_ids)
    target = tuple(target)
    if n<0 or len(target)!=1 or target[0] not in range(3) or any(
        u==v or not (0<=u<n and 0<=v<n) or len(g)!=1 or g[0] not in range(3)
        for u,v,g in edges):
        raise ValueError('invalid ternary matching input')
    if any(i<0 or i>=len(edges) for i in base) or sorted(v for i in base for v in edges[i][:2])!=list(range(n)):
        raise ValueError('invalid baseline')
    if portal_cap is not None and portal_cap<0:
        raise ValueError('invalid cap')
    host = nx.Graph()
    host.add_nodes_from(range(n))
    host.add_edges_from((u,v) for u,v,g in edges)
    sides = nx.bipartite.color(host)
    owner = {v:i for i in base for v in edges[i][:2]}
    delta = (target[0]-sum(edges[i][2][0] for i in base))%3
    stats = dict(subsets=0,incidences=0,states=0,flow_calls=0)
    arcs = {}
    seen = set()
    adj = defaultdict(list)
    incoming = defaultdict(list)
    graph = nx.DiGraph()
    graph.add_nodes_from(base)
    for i,(a,b,g) in enumerate(edges):
        if i in graph:
            continue
        if sides[a]:
            a,b=b,a
        u,v=owner[a],owner[b]
        arc=(u,v,(g[0]-edges[u][2][0])%3)
        if arc in seen:
            continue
        seen.add(arc)
        arcs[i]=arc
        adj[u].append(i)
        incoming[v].append(i)
        graph.add_edge(u,v)

    def success(trace):
        trace=tuple(trace)
        ids=tuple(sorted(set(base).difference(arcs[i][0] for i in trace).union(trace)))
        if sorted(v for i in ids for v in edges[i][:2])!=list(range(n)) or sum(edges[i][2][0] for i in ids)%3!=target[0]:
            raise ArithmeticError('matching replay failed')
        return 'SAT',ids,stats

    def cycle(allowed):
        best=None
        for start in sorted(allowed):
            pred={(start,0):None}
            queue=deque([(start,0)])
            while queue:
                u,g=queue.popleft()
                if u==start and g:
                    path=[]
                    state=(u,g)
                    while pred[state] is not None:
                        state,i=pred[state]
                        path.append(i)
                    if best is None or len(path)<len(best):
                        best=path[::-1]
                    break
                for i in adj[u]:
                    _,v,t=arcs[i]
                    state=(v,(g+t)%3)
                    if v in allowed and state not in pred:
                        pred[state]=((u,g),i)
                        queue.append(state)
        return best

    def components(X):
        sub=graph.subgraph(set(base)-X)
        parts=list(nx.strongly_connected_components(sub))
        condensation=nx.condensation(sub,parts)
        ordered=[parts[j] for j in nx.topological_sort(condensation)]
        pots={}
        for part in ordered:
            root=min(part)
            pots[root]=0
            todo=[root]
            while todo:
                u=todo.pop()
                for i in adj[u]:
                    _,v,g=arcs[i]
                    if v not in part:
                        continue
                    t=(pots[u]+g)%3
                    if v in pots:
                        if pots[v]!=t:
                            return None
                    else:
                        pots[v]=t
                        todo.append(v)
        return ordered,pots

    universe=set(base)
    if portals is None:
        if not delta:
            return success(())
        first=cycle(universe)
        if first is None:
            return 'UNSAT',None,stats
        def gain(trace):
            return sum(arcs[i][2] for i in trace)%3
        if gain(first)==delta:
            return success(first)
        X={arcs[i][0] for i in first}
        other=cycle(universe-X)
        if other:
            return success(other if gain(other)==delta else first+other)
        limit=min(len(X),portal_cap) if portal_cap is not None else len(X)
        data=None
        for k in range(limit+1):
            for candidate in combinations(base,k):
                stats['subsets']+=1
                data=components(set(candidate))
                if data is not None:
                    X=set(candidate)
                    break
            if data is not None:
                break
        if data is None:
            return 'UNKNOWN',None,stats
    else:
        X=set(portals)
        if not X<=universe:
            raise ValueError('invalid portals')
        data=components(X)
        if data is None:
            raise ValueError('nonneutral exterior')
        if portal_cap is not None and len(X)>portal_cap:
            return 'UNKNOWN',None,stats
    ordered,pots=data
    stats['portals']=tuple(sorted(X))
    if not delta:
        return success(())

    def route(part,src,dst):
        # Shared terminals are necessarily zero-length paths by vertex capacity.
        overlap=src & dst
        src,dst=src-overlap,dst-overlap
        if not src:
            return ()
        stats['flow_calls']+=1
        net=nx.DiGraph()
        source,sink='source','sink'
        internal={}
        available=part-overlap
        for u in available:
            net.add_edge((u,0),(u,1),capacity=1)
            if u in src:
                net.add_edge(source,(u,0),capacity=1)
            if u in dst:
                net.add_edge((u,1),sink,capacity=1)
            for i in adj[u]:
                _,v,_=arcs[i]
                if v in available and u!=v:
                    net.add_edge((u,1),(v,0),capacity=1)
                    internal[u,v]=i
        val,flow=nx.maximum_flow(net,source,sink)
        if val<len(src):
            return None
        succ={u:(v,i) for (u,v),i in internal.items() if flow[(u,1)].get((v,0))}
        trace=[]
        for u in src:
            while u not in dst:
                u,i=succ[u]
                trace.append(i)
        return tuple(trace)

    def finish(chosen):
        src=[arcs[i][1] for i in chosen if arcs[i][1] not in X]
        dst=[arcs[i][0] for i in chosen if arcs[i][0] not in X]
        if len(set(src))!=len(src) or len(set(dst))!=len(dst):
            return None
        states={(frozenset(src),sum(arcs[i][2] for i in chosen)%3):tuple(chosen)}
        for part in ordered:
            exits=[i for u in part for i in adj[u] if arcs[i][1] not in part|X]
            local_sinks=part.intersection(dst)
            nxt={}
            for (pending,g),trace in states.items():
                stats['states']+=1
                arrivals=part & pending
                outside=pending-part
                count=len(arrivals)-len(local_sinks)
                if count<0:
                    continue
                for cross in combinations(exits,count):
                    tails=local_sinks|{arcs[i][0] for i in cross}
                    heads=outside|{arcs[i][1] for i in cross}
                    if len(tails)!=len(arrivals) or len(heads)!=len(outside)+count:
                        continue
                    gain=(g+sum(pots[v] for v in tails)-sum(pots[v] for v in arrivals)
                          +sum(arcs[i][2] for i in cross))%3
                    key=(frozenset(heads),gain)
                    if key in nxt:
                        continue
                    paths=route(part,arrivals,tails)
                    if paths is not None:
                        nxt[key]=trace+paths+cross
            states=nxt
            if not states:
                return None
        return states.get((frozenset(),delta))

    options=[(None,)+tuple(product(incoming[u],adj[u])) for u in sorted(X)]
    for config in product(*options):
        stats['incidences']+=1
        chosen={i for pair in config if pair is not None for i in pair}
        if any(({i for i in chosen if arcs[i][1]==u},{i for i in chosen if arcs[i][0]==u})
               != (({pair[0]},{pair[1]}) if pair is not None else (set(),set()))
               for u,pair in zip(sorted(X),config)):
            continue
        trace=finish(chosen)
        if trace is not None:
            return success(trace)
    return 'UNSAT',None,stats


def solve_unbased(n, edges, target, *, portal_cap=None):
    """Compute a base perfect matching and run the deterministic residue search."""
    edges = [(u,v,tuple(g)) for u,v,g in edges]
    target = tuple(target)
    if n<0 or len(target)!=1 or target[0] not in range(3) or any(
        u==v or not (0<=u<n and 0<=v<n) or len(g)!=1 or g[0] not in range(3)
        for u,v,g in edges):
        raise ValueError('invalid ternary matching input')
    if portal_cap is not None and portal_cap<0:
        raise ValueError('invalid cap')
    graph = nx.Graph()
    graph.add_nodes_from(range(n))
    graph.add_edges_from((u,v) for u,v,g in edges)
    colors = nx.bipartite.color(graph)
    left = [u for u in graph if colors[u]==0]
    pairs = nx.bipartite.maximum_matching(graph,top_nodes=left)
    if len(pairs)!=n:
        return 'UNSAT',None,{'baseline':False}
    by_pair = {frozenset((u,v)):i for i,(u,v,g) in enumerate(edges)}
    base = [by_pair[frozenset((u,pairs[u]))] for u in left]
    return solve(n,edges,base,target,portal_cap=portal_cap)
