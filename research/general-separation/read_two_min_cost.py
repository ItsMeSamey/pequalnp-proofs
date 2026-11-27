"""Minimum-cost finite-domain SAT with at most two distinct incident clauses per variable.

minimum_cost(costs, clauses, pins=None) returns None or (Fraction, tuple).
costs[i] maps original domain values to finite rational costs. A literal is
(i, iterable of satisfying values); signs can be encoded by complementation.
Unknown members of a literal's set are harmless. Pins restrict domains.
Separate calls use independent state. Requires networkx for general matching.
"""
from fractions import Fraction
from math import lcm


def minimum_cost(costs, clauses, *, pins=None):
    import networkx as nx

    domains = [{v: Fraction(c) for v, c in prices.items()} for prices in costs]
    def variable(i):
        if type(i) is not int or not 0 <= i < len(domains):
            raise ValueError("invalid variable index")
        return i

    for i, v in ({} if pins is None else pins).items():
        variable(i)
        domains[i] = {v: domains[i][v]} if v in domains[i] else {}

    occ = [{} for _ in domains]
    clause_count = 0
    for clause_id, clause in enumerate(clauses):
        clause_count += 1
        for i, allowed in clause:
            variable(i)
            if clause_id not in occ[i] and len(occ[i]) == 2:
                raise ValueError("variable occurs in more than two distinct clauses")
            occ[i].setdefault(clause_id, set()).update(allowed)
    if any(not domain for domain in domains):
        return None

    # An edge carries a nominated subset for one original variable.
    choices, edges = [], []
    slot = clause_count
    for i, domain in enumerate(domains):
        ends = tuple(occ[i])
        table = {}
        for v, price in domain.items():
            cover = sum(1 << j for j, u in enumerate(ends) if v in occ[i][u])
            for mask in range(1 << len(ends)):
                if cover & mask == mask and (mask not in table or price < table[mask][0]):
                    table[mask] = price, v
        choices.append(table)
        singles = [(u, 1 << j, table[1 << j][0]-table[0][0])
                   for j, u in enumerate(ends) if 1 << j in table]
        # Base singleton slot; no second slot if joint coverage is impossible.
        for u, mask, price in singles:
            edges.append((u, slot, price, i, mask))
        slot += 1
        if 3 not in table:
            continue
        pair = table[3][0]-table[0][0]
        delta = pair-sum(price for _, _, price in singles)
        if delta < 0:
            # Independent singleton slots. Move the second endpoint's first
            # slot to a fresh private vertex, then add the discounted pair.
            u, mask, price = singles[1]
            edges[-1] = (u, slot, price, i, mask)
            slot += 1
            edges.append((*ends, pair, i, 3))
        else:
            for u, mask, price in singles:
                edges.append((u, slot, price+delta, i, mask))
            slot += 1

    scale = 1
    for _, _, price, _, _ in edges:
        scale = lcm(scale, price.denominator)
    reward = 1 + sum(int(price*scale) for _, _, price, _, _ in edges)
    graph = nx.Graph()
    graph.add_nodes_from(range(clause_count))
    for u, v, price, owner, mask in edges:
        weight = reward*(1+int(v < clause_count))-int(price*scale)
        # Parallel direct edges have identical occupied clause vertices.
        old = graph.get_edge_data(u, v)
        if old is None or old["weight"] < weight:
            graph.add_edge(u, v, weight=weight, owner=owner, mask=mask)
    chosen = [0]*len(domains)
    covered = 0
    for u, v in nx.max_weight_matching(graph, weight="weight"):
        edge = graph[u][v]
        chosen[edge["owner"]] |= edge["mask"]
        covered += int(u < clause_count)+int(v < clause_count)
    if covered != clause_count:
        return None
    result = [table[mask] for table, mask in zip(choices, chosen)]
    return sum((price for price, _ in result), Fraction(0)), tuple(v for _, v in result)
