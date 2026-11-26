import json, sys
from functools import cache
from itertools import combinations

def reconstruct(data):
    library, raw, dirty = (data[k] for k in ['library', 'raw', 'dirty'])
    gates = []

    @cache
    def gate(op, a, b):
        if a == b:
            return a
        gates.append((op, a, b))
        return 23 + len(gates)
    uses = {m: [] for m in library}
    for m in library:
        if m.bit_count() >= 2:
            a, b = next(((a, b) for a, b in combinations(library, 2) if m not in (a, b) and a | b == m))
            uses[a].append(m)
            uses[b].append(m)

    @cache
    def forward(m):
        sources = [j for j, v in enumerate(raw if len(raw) == 24 else raw * 2) if m == v]
        sources += [v for i, z in enumerate(dirty) if m == z and (v := atom(i)) is not None]
        sources += [v for t in uses.get(m, []) if (v := forward(t)) is not None]
        if not sources:
            return None
        acc = sources[0]
        for v in sources[1:]:
            acc = gate('or', min(acc, v), max(acc, v))
        return acc

    @cache
    def atom(i):
        a, b = (forward(1 << 2 * i), forward(2 << 2 * i))
        if a is None or b is None:
            return None
        return gate('and', min(a, b), max(a, b))
    terms = [v for i in range(len(dirty), len(data['deps'])) if (v := atom(i)) is not None]
    out = terms[0]
    for v in terms[1:]:
        out = gate('or', min(v, out), max(v, out))
    errors = []
    for i in range(12):
        for j in range(12):
            bits = [k in (i, j + 12) for k in range(24)]
            for op, a, b in gates:
                bits.append(bits[a] & bits[b] if op == 'and' else bits[a] | bits[b])
            if bits[out] != (i != j):
                errors.append((i, j))
    return (gates, out, errors)
if __name__ == '__main__':
    g, out, errors = reconstruct(json.load(open(sys.argv[1])))
    print('gates', len(g), 'out', out, 'errors', errors)
    for e in g:
        print(*e)
