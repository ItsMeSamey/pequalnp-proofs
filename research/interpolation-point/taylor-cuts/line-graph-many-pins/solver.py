"""Induced-even prescribed vertices in the line graph of a supplied simple root."""
from itertools import combinations

def extend(edges, allowed, forced, odd):
    demand = set(allowed) if odd else set()
    adj = {v: [] for v in allowed}
    for i,(v,w) in enumerate(edges):
        if v not in adj or w not in adj: continue
        if i in forced:
            demand.symmetric_difference_update((v,w))
        else:
            adj[v].append((w,i)); adj[w].append((v,i))
    chosen, seen = set(forced), set()
    for root in allowed:
        if root in seen: continue
        order, parent = [root], {}
        seen.add(root)
        for v in order:
            for w,i in adj[v]:
                if w not in seen:
                    seen.add(w); parent[w]=(v,i); order.append(w)
        for v in reversed(order[1:]):
            if v in demand:
                w,i=parent[v]; chosen.add(i); demand.symmetric_difference_update((v,w))
        if root in demand: return None
    return chosen

def solve(n, edges, pins):
    vertices, pins = set(range(n)), tuple(pins)
    for count in range(len(pins)+1):
        for chosen in combinations(pins,count):
            odd_pins=set(chosen); even_pins=set(pins)-odd_pins
            fixed={v for i in odd_pins for v in edges[i]}
            even_ends={v for i in even_pins for v in edges[i]}
            if fixed & even_ends: continue
            odd_degree=set()
            for i in odd_pins: odd_degree.symmetric_difference_update(edges[i])
            limit=len(fixed-odd_degree)
            candidates=vertices-fixed-even_ends
            for width in range(min(limit,len(candidates))+1):
                for extra in combinations(candidates,width):
                    support=fixed.union(extra)
                    odd=extend(edges,support,odd_pins,True)
                    if odd is None: continue
                    even=extend(edges,vertices-support,even_pins,False)
                    if even is not None: return odd|even
    return None
