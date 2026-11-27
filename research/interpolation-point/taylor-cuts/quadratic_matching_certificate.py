"""Degree-two deterministic UNSAT certificates for F3-labelled perfect matching."""
from itertools import combinations, combinations_with_replacement


def _add(dest, source, scale=1):
    for key,value in source.items():
        total=(dest.get(key,0)+scale*value)%3
        if total:
            dest[key]=total
        else:
            dest.pop(key,None)


def _product(first,second):
    out={}
    for x,a in first.items():
        for y,b in second.items():
            key=tuple(sorted(set(x+y)))  # Boolean edge indicator squares equal themselves
            _add(out,{key:a*b})
    return out


def _rows(n,edges,target,extension_pairs=()):
    if type(n) is not int or n<0 or any(type(t) is not int or t not in (0,1,2) for t in target):
        raise ValueError("invalid dimensions or target")
    incident=[[] for _ in range(n)]
    outputs=[{} for _ in target]
    for i,(u,v,g) in enumerate(edges):
        if not (type(u) is int and type(v) is int and 0<=u<n and 0<=v<n and u!=v and len(g)==len(target)):
            raise ValueError("invalid edge")
        if any(type(t) is not int or t not in (0,1,2) for t in g):
            raise ValueError("invalid edge label")
        incident[u].append(i)
        incident[v].append(i)
        for j,t in enumerate(g):
            if t:
                outputs[j][(i,)]=t
    # All monomial keys have nonnegative indices. A negative singleton records target evaluation.
    for v,ids in enumerate(incident):
        row={():2,**{(i,):1 for i in ids}}
        yield ("vertex",v),row
        for i in range(len(edges)):
            yield ("multiple",v,i),_product(row,{(i,):1})
        for i,j in combinations(ids,2):
            yield ("conflict",v,i,j),{(i,j):1}
    if extension_pairs is not None:
        # Factoring out the two forced edges leaves an ordinary perfect-matching test.
        import networkx as nx
        graph=nx.Graph()
        graph.add_nodes_from(range(n))
        graph.add_edges_from((u,v) for u,v,g in edges)
        for i,j in extension_pairs:
            if not (0<=i<j<len(edges)):
                continue
            endpoints={*edges[i][:2],*edges[j][:2]}
            if len(endpoints)!=4:
                continue
            remaining=set(range(n))-endpoints
            match=nx.max_weight_matching(graph.subgraph(remaining),maxcardinality=True)
            if 2*len(match)!=len(remaining):
                yield ("incompatible",i,j),{(i,j):1}
    def augmented(polynomial,value):
        row=dict(polynomial)
        if value%3:
            row[(-1,)]=value%3
        return row
    yield ("constant",),augmented({():1},1)
    for i,linear in enumerate(outputs):
        yield ("output",i),augmented(linear,target[i])
    for i,j in combinations_with_replacement(range(len(target)),2):
        yield ("output_product",i,j),augmented(_product(outputs[i],outputs[j]),target[i]*target[j])


def certificate(n,edges,target,*,extension_conflicts=False):
    """Return an explicit proof dictionary, or None if the row test has no proof."""
    pivots={}
    # The auxiliary evaluation column sorts first; the polynomial constant must sort after it.
    def order(k):
        return (k!=(-1,), len(k), k)
    edges=list(edges)
    pairs=combinations(range(len(edges)),2) if extension_conflicts else None
    for name,row in _rows(n,edges,tuple(target),pairs):
        row=dict(row)
        proof={name:1}
        while row:
            p=max(row,key=order)
            v=row[p]
            if p not in pivots:
                if v==2:
                    row={k:(2*c)%3 for k,c in row.items()}
                    proof={k:(2*c)%3 for k,c in proof.items()}
                if p==(-1,):
                    return proof
                pivots[p]=(row,proof)
                break
            basis,trace=pivots[p]
            _add(row,basis,-v)
            _add(proof,trace,-v)
    return None


def verify(n,edges,target,proof):
    """Replay the proposed linear combination without redoing elimination."""
    if not isinstance(proof,dict) or any(type(a) is not int or a not in (1,2) for a in proof.values()):
        return False
    combined={}
    used=set()
    pairs=[name[1:] for name in proof if isinstance(name,tuple) and len(name)==3 and name[0]=="incompatible"
           and all(type(i) is int for i in name[1:])]
    for name,row in _rows(n,list(edges),tuple(target),pairs if pairs else None):
        if name in proof:
            used.add(name)
            _add(combined,row,proof[name])
    return used==set(proof) and combined=={(-1,):1}
