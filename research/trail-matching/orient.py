"""Recognize whether reversing mask edges permits at most one start per bit.

The fixed-point criterion and tree dynamic program were proposed in this
research exchange. This file implements them; its oracle independently
enumerates edge orientations and computes loads directly from start masks.
"""
from collections import defaultdict
from itertools import product


def trees(masks):
    graph = defaultdict(list)
    for i,mask in enumerate(masks):
        other = mask ^ (1 << i)
        graph[mask].append((other,i))
        graph[other].append((mask,i))
    seen = set()
    result = []
    for root in graph:
        if root in seen:
            continue
        order = [root]
        seen.add(root)
        children = defaultdict(list)
        for vertex in order:
            for neighbor,i in graph[vertex]:
                if neighbor not in seen:
                    seen.add(neighbor)
                    order.append(neighbor)
                    children[vertex].append((neighbor,i))
        result.append((order,children))
    return result


def minimum_tree(tree, external):
    """Return (start count, bits of edges oriented from their 1 endpoint)."""
    order, children = tree
    root = order[0]
    for total in range(1,len(order)):
        table = {}
        for vertex in reversed(order):
            # A merged state counts child subtree starts and edges directed
            # from the vertex to its children. A witness encodes all directions.
            merged = {(0,0): 0}
            for child,i in children[vertex]:
                next_states = {}
                one_below = bool(child & (1 << i))
                for (starts,outgoing), witness in merged.items():
                    for outward in (0,1):
                        for substarts, subwitness in table[child,1-outward].items():
                            ones = substarts if one_below else total-substarts
                            combined = starts+substarts
                            if combined > total or ones+external[i] > 1:
                                continue
                            tail = vertex if outward else child
                            key = (combined,outgoing+outward)
                            next_states.setdefault(key,witness | subwitness | (tail & (1 << i)))
                merged = next_states
            has_parent = vertex != root
            degree = len(children[vertex]) + has_parent
            for parent_out in range(1 + int(has_parent)):
                possible = {}
                for (starts,outgoing), witness in merged.items():
                    local = max(0,2*(outgoing+parent_out)-degree)
                    if starts+local <= total:
                        possible.setdefault(starts+local,witness)
                table[vertex,parent_out] = possible
        if total in table[root,0]:
            return total,table[root,0][total]
    return None


def recognize(masks):
    """Return eligible oriented starting masks in pivot order, or None."""
    n = len(masks)
    if any(mask < 0 or mask >= 1 << n for mask in masks):
        raise ValueError("mask outside the pivot coordinate range")
    forest = trees(masks)
    totals = [0]*len(forest)
    while True:
        next_totals = []
        orientation = 0
        for k,tree in enumerate(forest):
            own_edges = [i for v in tree[0] for _,i in tree[1][v]]
            external = {i:sum(totals[j] for j,other in enumerate(forest)
                              if j != k and other[0][0] & (1 << i))
                        for i in own_edges}
            result = minimum_tree(tree,external)
            if result is None:
                return None
            total, directions = result
            next_totals.append(total)
            orientation |= directions
        if next_totals == totals:
            return tuple((mask & ~(1 << i)) | (orientation & (1 << i))
                         for i,mask in enumerate(masks))
        assert all(a <= b for a,b in zip(totals,next_totals))
        totals = next_totals


def orient_system(masks, offsets):
    """Return equivalent eligible masks and adjusted offset bitset, or None."""
    oriented = recognize(masks)
    if oriented is None:
        return None
    for old,new in zip(masks,oriented):
        offsets ^= old ^ new
    return oriented,offsets


def eligible(masks):
    balance = defaultdict(int)
    for i,m in enumerate(masks):
        balance[m] += 1
        balance[m ^ (1 << i)] -= 1
    return all(sum(max(0,b) for m,b in balance.items() if m & (1 << i)) <= 1
               for i in range(len(masks)))


def validate(n):
    # Clearing each self bit chooses one representative per family of 2^n
    # equivalent input orientations. The recognition input forest is identical.
    choices = [[m for m in range(1 << n) if not m & (1 << i)] for i in range(n)]
    accepted = tested = 0
    for canonical in product(*choices):
        valid = set()
        for signs in range(1 << n):
            candidate = tuple(m | (signs & (1 << i)) for i,m in enumerate(canonical))
            if eligible(candidate):
                valid.add(candidate)
        witness = recognize(canonical)
        assert (witness is not None) == bool(valid)
        if witness is not None:
            assert witness in valid
            accepted += 1
        tested += 1
    return tested, accepted


if __name__ == '__main__':
    for n in range(5):
        tested,accepted = validate(n)
        print(f"n={n}: {accepted}/{tested} unoriented forests eligible; {tested*(1 << n)} orientations compared.")
