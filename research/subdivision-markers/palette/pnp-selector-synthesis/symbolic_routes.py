"""Physical paired-space basis by bounded-cycle fill and quartic indexed-route sampling."""
from collections import deque
from functools import reduce
from itertools import combinations
from operator import xor

from frontier import basis
from gain_lift_holes import long_hole
from wedge_path import insert, wedge


def activation_chart(vertices, edges):
    """Return component labels and offsets in every simultaneous endpoint solution."""
    neighbors = [[] for _ in range(vertices)]
    for u,v,tag in edges:
        neighbors[u].append((v,tag))
        neighbors[v].append((u,tag))
    components = [-1]*vertices
    offsets = [0]*vertices
    count = 0
    for start in range(vertices):
        if components[start] >= 0:
            continue
        components[start] = count
        pending = [start]
        while pending:
            u = pending.pop()
            for v,tag in neighbors[u]:
                value = offsets[u] ^ tag
                if components[v] < 0:
                    components[v] = count
                    offsets[v] = value
                    pending.append(v)
                elif offsets[v] != value:
                    return None
        count += 1
    return components,offsets


def symbolic_pairs(vertices, physical, bound=4):
    """Use original graph when certified, otherwise saturate its full-link components."""
    physical = list(physical)
    edges = physical.copy()
    routes = [None]*len(physical)
    representatives = {}
    complete = [set() for _ in range(vertices)]
    if long_hole(vertices,edges,bound) is not None:
        for i,(u,v,tag) in enumerate(edges):
            if u != v:
                representatives.setdefault(tuple(sorted((u,v))),{}).setdefault(tag,i)
        for (u,v),tags in representatives.items():
            if len(tags)==4:
                complete[u].add(v)
                complete[v].add(u)
        for start in range(vertices):
            queue = deque([start])
            previous = {start:None}
            while queue:
                target = queue.popleft()
                for v in sorted(complete[target]-previous.keys()):
                    previous[v]=target
                    queue.append(v)
                if target <= start:
                    continue
                tags = representatives.get((start,target),{})
                if len(tags)==4:
                    continue
                v=target
                path=[]
                while v != start:
                    u=previous[v]
                    path.append((u,v,representatives[tuple(sorted((u,v)))]))
                    v=u
                for tag in range(4):
                    if tag not in tags:
                        edges.append((start,target,tag))
                        routes.append(path)
        if long_hole(vertices,edges,bound) is not None:
            return None

    keys=[(1<<u)^(1<<v) for u,v,_ in edges]
    cycles=[]
    for k in range(1,min(len(edges),bound)+1):
        for sites in combinations(range(len(edges)),k):
            columns=[keys[i] for i in sites]
            if reduce(xor,columns,0)==0 and len(basis(columns))==k-1:
                if activation_chart(vertices,(edges[i] for i in sites)) is not None:
                    cycles.append(sites)

    def realize(sites,colors):
        mask=0
        for i in sites:
            if routes[i] is None:
                mask ^= 1<<i
            else:
                for u,v,tags in routes[i]:
                    mask ^= 1<<tags[colors[u]^colors[v]]
        return mask

    pivots={}
    for first,second in combinations(cycles,2):
        chart=activation_chart(vertices,(edges[i] for i in first+second))
        if chart is None:
            continue
        component,offset=chart
        relevant=set()
        for i in first+second:
            if routes[i]:
                for u,v,_ in routes[i]:
                    if component[u]!=component[v]:
                        relevant.update((component[u],component[v]))
        bits=[(c,bit) for c in sorted(relevant) for bit in (1,2)]
        for weight in range(min(4,len(bits))+1):
            for selected in combinations(bits,weight):
                colors=offset.copy()
                for c,bit in selected:
                    for v in range(vertices):
                        if component[v]==c:
                            colors[v]^=bit
                a,b=realize(first,colors),realize(second,colors)
                insert(pivots,wedge(a,b),(a,b))
    return tuple(row[1] for row in pivots.values())
