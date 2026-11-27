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
    physical = list(physical)
    virtual = [(edge, tuple(tuple(r) for r in routes)) for edge, routes in virtual]
    augmented = physical + [edge for edge, _ in virtual]
    if long_hole(vertices, augmented, bound) is not None:
        return None
    lists = [(1 << i,) for i in range(len(physical))]
    for edge, routes in virtual:
        if uncovered_count(vertices, edge, physical, routes):
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
