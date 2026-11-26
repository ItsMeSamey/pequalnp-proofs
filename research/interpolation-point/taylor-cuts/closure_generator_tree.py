"""Tree DP for conflict-free unions of 2-SAT closure generators."""
from collections import defaultdict
from affine_syndrome_trellis import echelon, contains


def bundle_factors(closures, labels):
    bundles = defaultdict(int)
    for i, label in enumerate(labels):
        if type(label) is not int or label < 0:
            raise ValueError("invalid label mask")
        if label:
            scope = sum(1 << j for j, c in enumerate(closures) if c >> i & 1)
            if scope:
                bundles[scope] ^= label
    return [(s, v) for s,v in sorted(bundles.items()) if v]


def solve_prepared(data, bags, edges):
    """Return (original-coordinate witness, selected generator mask, diagnostics)."""
    closures, labels = tuple(data['closures']), tuple(data['labels'])
    baseline, target = data['baseline'], data['target']
    n, g = len(labels), len(closures)
    if any(type(x) is not int or x < 0 or x.bit_length() > n for x in (baseline, *closures)):
        raise ValueError("invalid original-coordinate mask")
    if type(target) is not int or target < 0:
        raise ValueError("invalid target")
    factors = bundle_factors(closures, labels)
    conflicts = set()
    for a,b in data['conflicts']:
        if any(type(i) is not int or not 0 <= i < g for i in (a,b)) or a == b:
            raise ValueError("invalid conflict")
        conflicts.add((1 << a) | (1 << b))
    bags = [tuple(row) for row in bags]
    if not bags or any(len(set(row)) != len(row) or any(type(v) is not int or not 0 <= v < g for v in row) for row in bags):
        raise ValueError("invalid bags")
    masks = [sum(1 << i for i in row) for row in bags]
    adj = [[] for _ in bags]
    seen = set()
    for a,b in edges:
        if any(type(i) is not int or not 0 <= i < len(bags) for i in (a,b)) or a == b:
            raise ValueError("invalid bag edge")
        edge = tuple(sorted((a,b)))
        if edge in seen:
            raise ValueError("duplicate bag edge")
        seen.add(edge)
        adj[a].append(b)
        adj[b].append(a)
    parent = {0:-1}
    order = [0]
    for a in order:
        for b in adj[a]:
            if b not in parent:
                parent[b] = a
                order.append(b)
    if len(order) != len(bags) or len(seen) != len(bags)-1:
        raise ValueError("decomposition must be a tree")
    for i in range(g):
        count = sum((mask >> i) & 1 for mask in masks)
        links = sum(((masks[a] & masks[b]) >> i) & 1 for a,b in seen)
        if not count or links != count-1:
            raise ValueError("missing generator or disconnected occurrences")

    def owner(scope):
        for j in order:
            if not scope & ~masks[j]:
                return j
        raise ValueError("no bag covers required scope")

    local = [[] for _ in bags]
    forbidden = [[] for _ in bags]
    for i,(s,v) in enumerate(factors):
        local[owner(s)].append(i)
    for conflict in conflicts:
        forbidden[owner(conflict)].append(conflict)
    gains = [v for _,v in factors]
    whole = echelon(gains)
    stats = dict(max_bag_size=max(map(len,bags)), max_cut_rank=0, peak_per_word=0, bundles=len(gains))
    if not contains(whole, target):
        return None,None,stats

    def boundary(charged):
        inside = echelon(gains[i] for i in charged)
        outside = echelon(v for i,v in enumerate(gains) if i not in charged)
        width = len(inside) + len(outside) - len(whole)
        stats['max_cut_rank'] = max(width, stats['max_cut_rank'])
        return outside

    tables = {}
    for node in reversed(order):
        charged = set(local[node])
        outside = boundary(charged)
        live = {}
        for bits in range(1 << len(bags[node])):
            word = sum(((bits >> j) & 1) << v for j,v in enumerate(bags[node]))
            if any(word & f == f for f in forbidden[node]):
                continue
            value = 0
            for i in local[node]:
                scope,gain = factors[i]
                if word & scope:
                    value ^= gain
            if contains(outside,target ^ value):
                live[word,value] = word
        stats['peak_per_word'] = max(stats['peak_per_word'], int(bool(live)))
        for child in adj[node]:
            if parent.get(child) != node:
                continue
            child_set, child_table = tables.pop(child)
            charged.update(child_set)
            outside = boundary(charged)
            sep = masks[node] & masks[child]
            companion = defaultdict(list)
            for (word,value), trace in child_table.items():
                companion[word & sep].append((value,trace))
            nxt = {}
            per_word = defaultdict(int)
            for (word,left), trace in live.items():
                for right,other in companion.get(word & sep, ()):
                    value = left ^ right
                    if contains(outside,target ^ value) and (word,value) not in nxt:
                        nxt[word,value] = trace | other
                        per_word[word] += 1
            stats['peak_per_word'] = max(stats['peak_per_word'], max(per_word.values(),default=0))
            live = nxt
        tables[node] = charged,live
    for (_,value),chosen in tables[0][1].items():
        if value == target:
            toggle = 0
            for j,c in enumerate(closures):
                if chosen >> j & 1:
                    toggle |= c
            return baseline ^ toggle,chosen,stats
    return None,None,stats


def solve(n, clauses, parity, bags, edges):
    from two_sat_generator_interaction import prepare
    clauses, parity = tuple(tuple(c) for c in clauses), tuple(parity)
    data = prepare(n,clauses,parity)
    if data is None:
        return None,None,{}
    x,choice,stats = solve_prepared(data,bags,edges)
    if x is not None and (not all(any(bool(x >> (abs(l)-1) & 1) == (l>0) for l in c) for c in clauses)
                          or not all((x & m).bit_count()%2 == b for m,b in parity)):
        raise AssertionError("original witness replay failed")
    return x,choice,stats
