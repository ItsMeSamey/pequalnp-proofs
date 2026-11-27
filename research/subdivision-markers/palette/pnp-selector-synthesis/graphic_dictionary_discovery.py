"""Recognize bounded-hole gain lifts and recover an indexed basis of compatible wedges."""
from itertools import combinations, product
from functools import reduce
from operator import xor

from gain_lift_holes import long_hole
from route_union import uncovered_count
from signature_bounds import consistent
from recognizer import bit_indices
from wedge_path import wedge, insert
from frontier import basis


def certified_pairs(vertices, physical, virtual, bound):
    """Virtual entries are (tagged edge, tuple of physical-index subsets). None means unrecognized."""
    return _basis_from_routes(vertices, physical, virtual, bound, verify=True)


def _basis_from_routes(vertices, physical, virtual, bound, verify):
    physical = list(physical)
    virtual = [(edge, tuple(tuple(r) for r in routes)) for edge, routes in virtual]
    augmented = physical + [edge for edge, _ in virtual]
    if long_hole(vertices, augmented, bound) is not None:
        return None
    lists = [(1 << i,) for i in range(len(physical))]
    for edge, routes in virtual:
        if verify and uncovered_count(vertices, edge, physical, routes):
            return None
        lists.append(tuple(sum(1 << i for i in route) for route in routes))
    columns = [((1 << u) ^ (1 << v), tag) for u,v,tag in augmented]
    words = set()
    for length in range(1, min(len(augmented),bound)+1):
        for indices in combinations(range(len(augmented)),length):
            keys = [columns[i][0] for i in indices]
            if reduce(xor, keys, 0) or len(basis(keys)) != length-1:
                continue
            if not consistent(columns, indices):
                continue
            for selected in product(*(lists[i] for i in indices)):
                word = reduce(xor, selected, 0)
                if word and consistent(columns, bit_indices(word)):
                    words.add(word)
    pivots = {}
    for u,v in combinations(sorted(words),2):
        if consistent(columns,bit_indices(u|v)):
            insert(pivots, wedge(u,v), (u,v))
    return tuple(entry[1] for entry in pivots.values())


def discover_pairs(vertices, physical, bound, radius):
    """Try the original and a saturated short full-link fill. Radius controls output size."""
    from collections import deque
    if radius < 0:
        raise ValueError("negative search radius")
    physical = list(physical)
    answer = certified_pairs(vertices, physical, [], bound)
    if answer is not None:
        return answer
    representatives = {}
    for i,(u,v,b) in enumerate(physical):
        if u != v:
            representatives.setdefault(tuple(sorted((u,v))), {}).setdefault(b,i)
    adj = [set() for _ in range(vertices)]
    for (u,v), tags in representatives.items():
        if len(tags)==4:
            adj[u].add(v)
            adj[v].add(u)
    virtual = []
    for u in range(vertices):
        queue = deque([(u,())])
        visited = {u}
        while queue:
            v, links = queue.popleft()
            if len(links) >= 2 and u < v:
                present = representatives.get((u,v),{})
                for b in range(4):
                    if b in present:
                        continue
                    routes = []
                    for internal in product(range(4),repeat=len(links)-1):
                        colors = (0,*internal,b)
                        routes.append(tuple(tags[c ^ d] for tags,c,d in zip(links,colors,colors[1:])))
                    virtual.append(((u,v,b),routes))
            if len(links) == radius:
                continue
            for w in sorted(adj[v]-visited):
                visited.add(w)
                tags = representatives[tuple(sorted((v,w)))]
                queue.append((w,(*links,tags)))
    return _basis_from_routes(vertices,physical,virtual,bound,verify=False)
