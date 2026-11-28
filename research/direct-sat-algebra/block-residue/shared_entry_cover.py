"""Pin a minimum vertex cover of the bad signed cones' canonical input pairs."""
from itertools import combinations, product

from corridor_nand import _hull, _net, _project, _replay, _rows, _sat
from distinct_cones import cone_groups
from signed_cone_nand import _materialize, _translated, normalize


def minimum_cover(edges):
    """Exact unweighted cover for distinct-endpoint pairs; no recursion depth cap."""
    edges = tuple(sorted({tuple(sorted(edge)) for edge in edges}))
    if any(len(edge) != 2 or edge[0] == edge[1] for edge in edges):
        raise ValueError("expected distinct-endpoint pairs")
    for budget in range(len(edges) + 1):
        stack = [()]
        while stack:
            chosen = stack.pop()
            selected = set(chosen)
            uncovered = next(((u,v) for u,v in edges
                              if u not in selected and v not in selected), None)
            if uncovered is None:
                return tuple(sorted(chosen))
            if len(chosen) < budget:
                u,v = uncovered
                stack.extend((chosen + (v,), chosen + (u,)))
    raise AssertionError("all pairs have a cover")


def solve(inputs, gates, *, clauses=(), pins=(), equalities=(), output=None):
    """Return (status, minimum cover of canonical wire IDs, normalized groups, raw)."""
    gates = _net(inputs, gates)
    if output is not None:
        if type(output) is not int or not 0 <= output < inputs + len(gates):
            raise ValueError("invalid designated original output")
        pins = tuple(pins) + ((output, 1),)
    original_rows = _rows(inputs + len(gates), clauses, pins, equalities)
    retained, aliases = normalize(inputs, gates)
    rows = _translated(original_rows, aliases)
    groups = cone_groups(inputs, tuple((a[0],b[0]) for a,b in retained))
    if groups is None:
        raise AssertionError("tied normalized operands")
    physical, expanded, blocks = _materialize(inputs, retained, groups)
    canon = {wire: base for base,wire in enumerate(expanded)}
    observed = {expanded[abs(l)-1] for row in rows for l in row}
    base_rows = [tuple((expanded[abs(l)-1]+1)*(1 if l>0 else -1) for l in row)
                 for row in rows]
    n = inputs + len(physical)
    readers = [set() for _ in range(n)]
    for owner, block in enumerate(blocks):
        for i in block:
            for v in physical[i]:
                readers[v].add(owner)
    factors = []
    bad_edges = []
    for owner, block in enumerate(blocks):
        outs = {inputs+i for i in block}
        entries = tuple(sorted({v for i in block for v in physical[i]} - outs))
        ports = tuple(sorted(v for v in outs.union(entries)
                             if v in observed or readers[v] - {owner}
                             or (v in entries and v >= inputs)))
        # Keep every entry choice until after fiber restriction. A private
        # entry need not be recoverable from its unconditioned projected word.
        all_ports = ports + tuple(v for v in entries if v not in ports)
        traces, _ = _project(inputs, physical, block, all_ports, entries)
        cases = [(word[:len(ports)],choice) for word,choice in traces.items()]
        words = list(dict.fromkeys(word for word,choice in cases))
        bad = any(tuple((a&b)|(a&c)|(b&c) for a,b,c in zip(x,y,z)) not in words
                  for x,y,z in combinations(words,3))
        if bad:
            if len(entries) != 2:
                raise AssertionError("nonbijunctive table on fewer than two inputs")
            bad_edges.append(tuple(canon[v] for v in entries))
        factors.append((ports,entries,cases,bad))
    cover = minimum_cover(bad_edges)
    cut = tuple(expanded[v] for v in cover)
    for bits in product((0,1), repeat=len(cut)):
        pinned = dict(zip(cut,bits))
        combined = base_rows + [((v+1)*(1 if bit else -1),) for v,bit in pinned.items()]
        choices = []
        for ports,entries,cases,bad in factors:
            table = {}
            for word,choice in cases:
                if all(v not in pinned or pinned[v]==b for v,b in zip(entries,choice)):
                    table.setdefault(word, choice)
            if not table or (bad and len(table)>2):
                raise AssertionError("invalid cover cofactor")
            combined.extend(_hull(ports,list(table)))
            choices.append((ports,entries,table))
        values = _sat(n,combined)
        if values is None:
            continue
        raw = values[:inputs]
        for ports,entries,table in choices:
            choice = table[tuple(values[v] for v in ports)]
            for v,bit in zip(entries,choice):
                if v<inputs:
                    raw[v]=bit
        wires = _replay(raw,physical)
        if any(wires[v]!=bit for v,bit in pinned.items()):
            raise AssertionError("global cover pin was lost")
        if any(not any(wires[abs(l)-1]==(l>0) for l in row) for row in combined):
            raise AssertionError("physical cofactor replay failed")
        original = _replay(raw,gates)
        if any(value != ((0 if base==-1 else wires[expanded[base]]) ^ flip)
               for value,(base,flip) in zip(original,aliases)):
            raise AssertionError("signed alias replay failed")
        if any(not any(original[abs(l)-1]==(l>0) for l in row) for row in original_rows):
            raise AssertionError("original exterior replay failed")
        return "sat", cover, groups, tuple(raw)
    return "unsat", cover, groups, None
