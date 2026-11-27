"""Deterministic recursive GF(3)^b matching search using scalar-neutral portals."""
from collections import defaultdict, deque
from itertools import combinations, product
from math import log, sqrt

import networkx as nx


def add(a,b):
    return tuple((x+y)%3 for x,y in zip(a,b))


def sub(a,b):
    return tuple((x-y)%3 for x,y in zip(a,b))


def dot(a,b):
    return sum(x*y for x,y in zip(a,b))%3


def shortest(adj, available, normal, threshold):
    best=None
    for root in sorted(available):
        start=(root,0)
        parents={start:None}
        queue=deque([(start,0)])
        while queue:
            (u,g),d=queue.popleft()
            if u==root and g:
                path=[]
                state=(u,g)
                while parents[state] is not None:
                    state,e=parents[state]
                    path.append(e)
                best=tuple(reversed(path))
                break
            if d>=threshold or (best is not None and d+1>=len(best)):
                continue
            for v,h,i in adj[u]:
                key=(v,(g+dot(normal,h))%3)
                if v in available and key not in parents:
                    parents[key]=((u,g),i)
                    queue.append((key,d+1))
    return best


def solve(n,edges,target,*,threshold=None,portal_cap=None):
    edges=tuple((u,v,tuple(g)) for u,v,g in edges)
    target=tuple(target)
    if n<0 or any(x not in (0,1,2) for x in target) or any(
        not (0<=u<n and 0<=v<n and u!=v and len(g)==len(target) and all(x in (0,1,2) for x in g))
        for u,v,g in edges):
        raise ValueError('invalid labelled graph')
    if threshold is not None and threshold<1 or portal_cap is not None and portal_cap<0:
        raise ValueError('invalid search parameter')
    stats=dict(calls=0,bases=0,portal_nodes=0,batches=0,max_portals=0,cap_hits=0)

    def visit(order,es,t):
        stats['calls']+=1
        graph=nx.Graph()
        graph.add_nodes_from(range(order))
        graph.add_edges_from((u,v) for u,v,g in es)
        color=nx.bipartite.color(graph)
        left=sorted(u for u in graph if not color[u])
        mate=nx.bipartite.maximum_matching(graph,top_nodes=left)
        if len(mate)!=order:
            return 'UNSAT',None
        lookup={frozenset((u,v)):i for i,(u,v,g) in enumerate(es)}
        base=[lookup[frozenset((u,mate[u]))] for u in left]
        b=len(t)
        zero=(0,)*b
        def gain(ids):
            z=zero
            for i in ids:
                z=add(z,es[i][2])
            return z
        delta=sub(t,gain(base))
        if delta==zero:
            return 'SAT',tuple(base)
        owner={u:j for j,i in enumerate(base) for u in es[i][:2]}
        sites=set(range(len(base)))
        adj=defaultdict(list)
        labels=defaultdict(dict)
        arc={}
        base_set=set(base)
        dig=nx.DiGraph()
        dig.add_nodes_from(sites)
        for i,(u,v,g) in enumerate(es):
            if i in base_set:
                continue
            if color[u]:
                u,v=v,u
            a,c=owner[u],owner[v]
            h=sub(g,es[base[a]][2])
            if h in labels[a,c]:
                continue
            labels[a,c][h]=i
            arc[i]=(a,c,h)
            adj[a].append((c,h,i))
            dig.add_edge(a,c)
        def restore(trace):
            ids=tuple(sorted((base_set-{base[arc[i][0]] for i in trace})|set(trace)))
            if gain(ids)!=t or sorted(v for i in ids for v in es[i][:2])!=list(range(order)):
                raise ArithmeticError('recursive witness failed replay')
            return 'SAT',ids
        m=len(base)
        log_factor=max(1,log(2*m)*log(log(4*m))) if m else 1
        # Number of bases in the character-sum bound, ceil(log2(4*b)).
        s=(4*b-1).bit_length()
        limit=threshold or max(1,int(sqrt(m*log_factor/(b*s))))
        all_normals=tuple(v for v in product(range(3),repeat=b) if any(v) and next(x for x in v if x)==1)
        remain=set(sites)
        cycles=[]
        span=[]
        for _ in range(b*s):
            normal=None
            for candidate in all_normals:
                if any(dot(candidate,v) for v in span):
                    continue
                normal=candidate
                path=shortest(adj,remain,candidate,limit)
                if path is not None:
                    break
            else:
                break
            h=zero
            for i in path:
                u,v,k=arc[i]
                remain.remove(u)
                h=add(h,k)
            cycles.append((h,path))
            span.append(h)
            if len(span)==b:
                span=[]
        if len(cycles)==b*s:
            stats['bases']+=1
            states={zero:()}
            for h,path in cycles:
                for prev,trace in tuple(states.items()):
                    states.setdefault(add(prev,h),trace+path)
            return restore(states[delta])
        if normal is None:
            raise ArithmeticError('missing annihilator')
        pivot=next(i for i,x in enumerate(normal) if x)
        def project(h):
            return h[:pivot]+h[pivot+1:]
        def unproject(a,p):
            full=list(p)
            full.insert(pivot,0)
            full[pivot]=(a-dot(full,normal))*normal[pivot]%3
            return tuple(full)
        def neutral(X):
            subgraph=dig.subgraph(sites-X)
            parts=list(nx.strongly_connected_components(subgraph))
            dag=nx.condensation(subgraph,parts)
            pots={}
            for part in parts:
                root=min(part)
                pots[root]=0
                todo=[root]
                while todo:
                    u=todo.pop()
                    for v,h,i in adj[u]:
                        if v not in part:
                            continue
                        k=(pots[u]+dot(h,normal))%3
                        if v in pots:
                            if pots[v]!=k:
                                return None
                        else:
                            pots[v]=k
                            todo.append(v)
            return [parts[i] for i in nx.topological_sort(dag)],pots
        fixed=sites-remain
        budget=m if portal_cap is None else min(m,portal_cap)
        data=None
        for count in range(budget-len(fixed)+1):
            for extra in combinations(sorted(remain),count):
                X=fixed|set(extra)
                data=neutral(X)
                if data is not None:
                    break
            if data is not None:
                break
        if data is None:
            stats['cap_hits']+=1
            return 'UNKNOWN',None
        parts,pot=data
        stats['portal_nodes']+=1
        stats['max_portals']=max(stats['max_portals'],len(X))
        def batch(pairs):
            stats['batches']+=1
            out={zero:()}
            for pair in sorted(pairs):
                nxt={}
                for h,trace in out.items():
                    for k,i in labels[pair].items():
                        nxt.setdefault(add(h,k),trace+(i,))
                out=nxt
            return out
        unknown=False
        cache={}
        def local(j,arr,dep):
            nonlocal unknown
            key=(j,frozenset(arr),frozenset(dep))
            if key in cache:
                return cache[key]
            part=parts[j]
            src=sorted(part-dep)
            dst=sorted(part-arr)
            aidx={u:k for k,u in enumerate(src)}
            cidx={u:k+len(src) for k,u in enumerate(dst)}
            opts=[]
            original=[]
            for u in src:
                if u in cidx:
                    opts.append((aidx[u],cidx[u],(0,)*(b-1)))
                    original.append(None)
                for v,h,i in adj[u]:
                    if v in cidx:
                        opts.append((aidx[u],cidx[v],project(h)))
                        original.append(i)
            scalar=(sum(pot[u] for u in dep)-sum(pot[u] for u in arr))%3
            out={}
            for p in product(range(3),repeat=b-1):
                flag,ids=visit(len(src)+len(dst),opts,p)
                if flag=='UNKNOWN':
                    unknown=True
                if flag=='SAT':
                    out[unproject(scalar,p)]=tuple(original[i] for i in ids if original[i] is not None)
            cache[key]=out
            return out
        xin=sorted(X)
        options=[(None,)+tuple(product(dig.predecessors(u),dig.successors(u))) for u in xin]
        for config in product(*options):
            boundary=set()
            for u,choice in zip(xin,config):
                if choice is not None:
                    v,w=choice
                    boundary.update(((v,u),(u,w)))
            if len({u for u,v in boundary})!=len(boundary) or len({v for u,v in boundary})!=len(boundary):
                continue
            if any((u in {a for a,c in boundary} or u in {c for a,c in boundary})!=(choice is not None)
                   for u,choice in zip(xin,config)):
                continue
            arrivals=frozenset(v for u,v in boundary if v not in X)
            sinks={u for u,v in boundary if u not in X}
            states={(arrivals,h):trace for h,trace in batch(boundary).items()}
            for j,part in enumerate(parts):
                cross=[(u,v) for u in part for v in dig.successors(u) if v not in part and v not in X]
                nxt={}
                for (pending,h),trace in states.items():
                    arr=pending & part
                    outside=pending-part
                    local_sinks=sinks & part
                    count=len(arr)-len(local_sinks)
                    if count<0:
                        continue
                    for pairs in combinations(cross,count):
                        dep=local_sinks|{u for u,v in pairs}
                        heads=outside|{v for u,v in pairs}
                        if len(dep)!=len(arr) or len(heads)!=len(outside)+count:
                            continue
                        opts=local(j,arr,dep)
                        for k,extension in batch(pairs).items():
                            for g,inside in opts.items():
                                nxt.setdefault((frozenset(heads),add(add(h,k),g)),trace+extension+inside)
                states=nxt
                if not states:
                    break
            witness=states.get((frozenset(),delta))
            if witness is not None:
                return restore(witness)
        return ('UNKNOWN' if unknown else 'UNSAT'),None
    status,witness=visit(n,edges,target)
    return status,witness,stats
