"""Exact bounded-ANF and quadratic residual counter for (truth table, a, b) DAGs."""
from itertools import combinations
from random import Random

def anf(q, gates, cap):
    nodes = [{1 << i} for i in range(q)]
    for table, a, b in gates:
        c, cb, ca, cab = ((table >> i) & 1 for i in range(4))
        ans = {0} if c else set()
        if ca ^ c:
            ans ^= nodes[a]
        if cb ^ c:
            ans ^= nodes[b]
        if c ^ ca ^ cb ^ cab:
            for u in nodes[a]:
                for v in nodes[b]:
                    ans.symmetric_difference_update((u | v,))
        if len(ans) > cap:
            return None
        nodes.append(ans)
    return nodes[-1], max(map(len, nodes))

def gauss(poly, free):
    """Signed sum of (-1)^poly over the free bit mask."""
    factor = 1
    while True:
        edge = next((s for s in sorted(poly) if s.bit_count() == 2), None)
        if edge is None:
            if any(s for s in poly):
                return 0
            return (-1 if 0 in poly else 1) * factor * (1 << free.bit_count())
        i = edge & -edge
        j = edge ^ i
        left = {s ^ i for s in poly if s & i and s != edge}
        right = {s ^ j for s in poly if s & j and s != edge}
        poly = {s for s in poly if not s & edge}
        for u in left:
            for v in right:
                poly.symmetric_difference_update((u | v,))
        free ^= edge
        factor *= 2

def count(q, gates, cap=1024):
    result = anf(q, gates, cap)
    if result is None:
        return None
    poly, peak = result
    high = sorted(s for s in poly if s.bit_count() > 2)
    cover = 0
    while True:
        residual = [s & ~cover for s in high if (s & ~cover).bit_count() > 2]
        if not residual:
            break
        i = max(range(q), key=lambda i: sum((s >> i) & 1 for s in residual))
        cover |= 1 << i
    free = (1 << q) - 1
    signed = 0
    if cover.bit_count() <= len(high):
        exponent = cover.bit_count()
        assignment = cover
        while True:
            reduced = set()
            for s in poly:
                if not s & cover & ~assignment:
                    reduced.symmetric_difference_update((s & ~cover,))
            signed += gauss(reduced, free ^ cover)
            if not assignment:
                break
            assignment = (assignment - 1) & cover
        mode = 'pinned'
    else:
        exponent = len(high)
        base = poly - set(high)
        for k in range(len(high) + 1):
            for subset in combinations(high, k):
                forced = 0
                for s in subset:
                    forced |= s
                reduced = set()
                for s in base:
                    reduced.symmetric_difference_update((s & ~forced,))
                signed += (-2)**k * gauss(reduced, free ^ forced)
        mode = 'expanded'
    return ((1 << q) - signed)//2, peak, len(high), mode, 1 << exponent

def corpus(q, kind):
    gates = []
    def gate(table, a, b):
        gates.append((table, a, b))
        return q + len(gates) - 1
    def product(items):
        u, *rest = items
        for v in rest:
            u = gate(8, u, v)
        return u
    terms = []
    for i in range(0, q-1, 2):
        b = i+1
        mask = product([(i+2)%q, (i+3)%q])
        terms.append(gate(6, gate(8, gate(6, i, mask), b), gate(8, mask, b)))
    if kind == 'star':
        terms.extend(product([0,i,i+1]) for i in range(2,q-1,2))
    if kind == 'wide':
        terms.append(product(list(range(q))))
    if kind == 'disjoint':
        terms.extend(product([i,i+1,i+2]) for i in range(0,q-2,3))
    u = terms[0]
    for v in terms[1:]:
        u = gate(6,u,v)
    return gates

def oracle(q,gates):
    allbits = (1 << (1 << q)) - 1
    nodes = [sum(1 << x for x in range(1 << q) if (x >> i) & 1) for i in range(q)]
    for table,a,b in gates:
        terms = [((nodes[a] if i&2 else ~nodes[a]) & (nodes[b] if i&1 else ~nodes[b])) for i in range(4) if table & (1<<i)]
        val = 0
        for t in terms:
            val |= t
        nodes.append(val & allbits)
    return nodes[-1].bit_count()

if __name__ == '__main__':
    rng = Random(31619)
    for _ in range(120):
        q = rng.randrange(2,9)
        gates = [(rng.randrange(16),rng.randrange(q+i),rng.randrange(q+i)) for i in range(3*q)]
        assert count(q,gates)[0] == oracle(q,gates)
    print('120 random gate-DAG truth-table checks passed')
    for q in [8,10,12]:
        for kind in ['clean','star','wide','disjoint']:
            gates = corpus(q,kind)
            ans = count(q,gates,32)
            truth = oracle(q,gates)
            assert ans[0] == truth
            print(q,kind,len(gates),truth,ans[1:])
