"""Partial multi-XOR decision on a supplied square perfect matching.

Options use choice_cover_one_xor.Option(resource,event,parity); parity is a
nonnegative integer label mask. Parallel options retain their identity.
"""
from functools import reduce
from operator import xor
from choice_cover_one_xor import odd_cycle


def residue(x, table):
    for pivot in sorted(table,reverse=True):
        if x >> pivot & 1:
            x ^= table[pivot][0]
    return x


def insert(x, witness, table):
    for pivot in sorted(table,reverse=True):
        if x >> pivot & 1:
            value, support=table[pivot]
            x ^= value
            witness ^= support
    if x:
        table[x.bit_length()-1]=(x,witness)


def reachable(start, graph):
    seen={start}
    stack=[start]
    while stack:
        for v in graph[stack.pop()]:
            if v not in seen:
                seen.add(v)
                stack.append(v)
    return seen


def exceptional_labels(part, table):
    """One component matching per attainable quotient gain."""
    vertices, edges, _ = part
    potentials={0:0}
    stack=[0]
    while stack:
        u=stack.pop()
        for v,g,_ in edges[u]:
            if v not in potentials:
                potentials[v]=potentials[u]^g
                stack.append(v)
    states={(0,0):()}
    for u,row in enumerate(edges):
        nxt={}
        for (mask,total),chosen in states.items():
            for v,g,opt in row:
                if mask>>v & 1:
                    continue
                value=residue(potentials[u]^g^potentials[v],table)
                key=(mask|(1<<v),total^value)
                if key not in nxt:
                    nxt[key]=chosen+((vertices[u],opt),)
        states=nxt
    return {val:chosen for (_,val),chosen in states.items()}


def peel(options, base, target, free=(), *, exact=False):
    """Return (status, chosen options, free mask, stalled row components).

    A free vector can be toggled independently of every matching option.
    UNKNOWN is returned only when the span obstruction fails and the peeled
    SCCs alone cannot realize the target. The base matching is required.
    """
    n=len(base)
    owner={opt.resource:i for i,opt in enumerate(base)}
    free=tuple(free)
    if (len(options)!=n or len(owner)!=n or target<0 or any(v<0 for v in free)
        or any(base[i] not in row or any(o.parity<0 or o.resource not in owner for o in row)
               for i,row in enumerate(options))):
        raise ValueError('Invalid base matching, option, or label')
    adj=[[(owner[o.resource],o.parity^base[i].parity,o) for o in row] for i,row in enumerate(options)]
    graph=[[v for v,_,_ in row] for row in adj]
    rev=[[] for _ in base]
    for u,row in enumerate(graph):
        for v in row:
            rev[v].append(u)
    remaining=set(range(n))
    parts=[]
    while remaining:
        root=min(remaining)
        vertices=sorted(reachable(root,graph)&reachable(root,rev))
        remaining.difference_update(vertices)
        local={v:i for i,v in enumerate(vertices)}
        edges=[[(local[v],g,o) for v,g,o in adj[u] if v in local] for u in vertices]
        potential={0:0}
        stack=[0]
        while stack:
            u=stack.pop()
            for v,g,_ in edges[u]:
                if v not in potential:
                    potential[v]=potential[u]^g
                    stack.append(v)
        space={}
        for u,row in enumerate(edges):
            for v,g,_ in row:
                insert(potential[u]^g^potential[v],0,space)
        parts.append((vertices,edges,[v for v,_ in space.values()]))
    needed=target^reduce(xor,(o.parity for o in base),0)
    table={}
    for i,v in enumerate(free):
        insert(v,1<<i,table)
    all_space=table.copy()
    for _,_,space in parts:
        for v in space:
            insert(v,0,all_space)
    if residue(needed,all_space):
        return 'UNSAT',None,None,[]
    cycles=[]
    while True:
        for i,(vertices,edges,space) in enumerate(parts):
            directions={residue(v,table) for v in space}-{0}
            if len(directions)>1:
                continue
            if directions:
                bit=next(iter(directions)).bit_length()-1
                marked=[[(v,(residue(g,table)>>bit)&1,o) for v,g,o in row] for row in edges]
                cycle=[(vertices[u],o) for u,o in odd_cycle(marked)]
                gain=reduce(xor,(o.parity^base[u].parity for u,o in cycle),0)
                assert residue(gain,table) in directions
                insert(gain,1<<(len(free)+len(cycles)),table)
                cycles.append(cycle)
            parts.pop(i)
            break
        else:
            break
    stalled=[p[0] for p in parts]
    exceptional=()
    quotient_target=residue(needed,table)
    if quotient_target:
        if not exact:
            return 'UNKNOWN',None,None,stalled
        totals={0:()}
        for part in parts:
            local=exceptional_labels(part,table)
            nxt={}
            for prefix,previous in totals.items():
                for value,selection in local.items():
                    if prefix^value not in nxt:
                        nxt[prefix^value]=previous+selection
            totals=nxt
        if quotient_target not in totals:
            return 'UNSAT',None,None,stalled
        exceptional=totals[quotient_target]
        for u,opt in exceptional:
            needed^=opt.parity^base[u].parity
    witness=0
    for pivot in sorted(table,reverse=True):
        if needed>>pivot & 1:
            v,tag=table[pivot]
            needed^=v
            witness^=tag
    chosen=list(base)
    for u,opt in exceptional:
        chosen[u]=opt
    for i,cycle in enumerate(cycles,start=len(free)):
        if witness>>i & 1:
            for u,o in cycle:
                chosen[u]=o
    return 'SAT',chosen,witness&((1<<len(free))-1),stalled
