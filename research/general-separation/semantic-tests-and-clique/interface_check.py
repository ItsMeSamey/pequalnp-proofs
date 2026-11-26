"""Compare the signed-interface compiler to direct upward closure on small DAGs."""
from itertools import product
from random import Random

def subs(mask):
    part = mask
    while True:
        yield part
        if not part:
            return
        part = (part - 1) & mask

def run(n, gates):
    limit = 1 << n
    ones = (1 << limit) - 1
    x = [sum(1 << a for a in range(limit) if a & (1 << i)) for i in range(n)]
    truth = x + [ones ^ t for t in x]
    pos = [1 << i for i in range(n)] + [0] * n
    neg = [0] * n + [1 << i for i in range(n)]
    gamma = [0] * (2 * n)
    for gate, u, v in gates:
        pos.append(pos[u] | pos[v])
        neg.append(neg[u] | neg[v])
        truth.append((truth[u] & truth[v]) if gate == "AND" else (truth[u] | truth[v]))
        gamma.append(((pos[u] & neg[v]) | (neg[u] & pos[v])) if gate == "AND" else 0)
    boundary = [0] * len(pos)
    for index in range(len(gates) - 1, -1, -1):
        g = 2 * n + index
        _, u, v = gates[index]
        for child in (u, v):
            boundary[child] |= (boundary[g] | gamma[g]) & (pos[child] | neg[child])
    table = []
    for g in range(len(pos)):
        b = boundary[g]
        if g < n:
            row = {a: (x[g] if a == b else 0) for a in subs(b)}
        elif g < 2 * n:
            row = {a: (ones if not a else 0) for a in subs(b)}
        else:
            gate, u, v = gates[g - 2 * n]
            row = {a: 0 for a in subs(b)}
            for a in subs(boundary[u] | boundary[v]):
                left = table[u][a & boundary[u]]
                right = table[v][a & boundary[v]]
                row[a & b] |= left & right if gate == "AND" else left | right
        table.append(row)
    reference = sum(1 << a for a in range(limit) if any(truth[-1] & (1 << y) for y in subs(a)))
    assert table[-1][0] == reference
    return max(b.bit_count() for b in boundary)

if __name__ == "__main__":
    rng = Random(71520)
    counts = {}
    for n, steps in product(range(2, 6), (4, 12, 30)):
        for _ in range(100):
            gates = [(rng.choice(("AND", "OR")), rng.randrange(2*n+i), rng.randrange(2*n+i))
                     for i in range(steps)]
            width = run(n, gates)
            counts[width] = counts.get(width, 0) + 1
    print("upward closure agrees for 1200 shared DAGs; width histogram", sorted(counts.items()))
