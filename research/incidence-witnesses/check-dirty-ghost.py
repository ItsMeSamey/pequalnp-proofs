"""Exhaustive full-cube check of three dirty marker forks and local bypasses."""
from functools import reduce
from operator import or_

n = 12
full = (1 << (1 << n)) - 1
rows = range(1 << n)
raw = [sum(1 << t for t in rows if (t >> i) & 1) for i in range(n)]
a, b, x, z = (list(range(i, i + 3)) for i in range(0, n, 3))
gates = []


def gate(op, l, r):
    gates.append((op, l, r))
    return n + len(gates) - 1


def nxt(i):
    return (i + 1) % 3


T = [gate('|', a[i], a[nxt(i)]) for i in range(3)]
G = [gate('&', x[i], gate('|', b[i], T[i])) for i in range(3)]
E = []
for i in range(3):
    j = nxt(i)
    H = gate('&', G[j], b[j])
    E.append(gate('&', gate('|', G[i], H), gate('|', G[j], a[i])))
terms = E + [gate('&', z[i], T[i]) for i in range(3)]
out = reduce(lambda l, r: gate('|', l, r), terms)


def run(*, force=(), bypass=None):
    wires = raw.copy()
    for j, (op, l, r) in enumerate(gates, n):
        if j in force:
            wire = full
        elif bypass and j == bypass[0]:
            wire = wires[bypass[1]]
        else:
            wire = wires[l] | wires[r] if op == '|' else wires[l] & wires[r]
        wires.append(wire)
    return wires[out]


goal = reduce(or_, ((raw[x[i]] & (raw[a[i]] | raw[b[i]])) |
                    (raw[z[i]] & (raw[a[i]] | raw[a[nxt(i)]])) for i in range(3)))
assert run() == goal
two_queries = sum(1 << t for t in rows if (t >> 6).bit_count() <= 2)
for j, (_, l, r) in enumerate(gates, n):
    for parent in (l, r):
        assert (run(bypass=(j, parent)) ^ goal) & two_queries
empty_queries = (1 << 64) - 1
for i in range(3):
    assert ((run(force=(G[i],)) ^ (raw[a[i]] | raw[b[i]])) & empty_queries) == 0
    assert run(force=(G[i], G[nxt(i)])) & 1
print(len(gates), 'gates; all full-cube rows, 58 sparse bypass checks, and 6 interventions passed')
