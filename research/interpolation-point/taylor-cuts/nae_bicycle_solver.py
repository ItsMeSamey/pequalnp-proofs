"""Deterministic signed NAE search. Literal (variable, sign) means bit XOR sign."""
from itertools import product

def gate_ok(gate, assignment):
    return len({assignment[v] ^ s for v, s in gate}) >= 2

def solve(n, gates):
    original = [tuple(gate) for gate in gates]
    active = list(original)
    repairs = []
    while True:
        clean = []
        for gate in active:
            literals = set(gate)
            if any((v, s ^ 1) in literals for v, s in literals):
                continue
            if len(literals) <= 1:
                return None
            clean.append(tuple(sorted(literals)))
        active = clean
        adjacency = {}
        for i, gate in enumerate(active):
            for v, s in gate:
                adjacency.setdefault(v, []).append((i, s))
        leaf = next((v for v, incident in adjacency.items() if len(incident) == 1), None)
        if leaf is not None:
            i, _ = adjacency[leaf][0]
            repairs.append(('free', leaf, (active[i],)))
            active.pop(i)
            continue
        binary = next((i for i, gate in enumerate(active) if len(gate) == 2), None)
        if binary is not None:
            (u, s), (v, t) = active.pop(binary)
            delta = 1 ^ s ^ t
            repairs.append(('parity', v, (u, delta)))
            active = [tuple((u, sign ^ delta) if x == v else (x, sign) for x, sign in gate)
                      for gate in active]
            continue
        wire = next((v for v, incident in adjacency.items() if len(incident) == 2), None)
        if wire is not None:
            (i, s), (j, t) = adjacency[wire]
            left, right = active[i], active[j]
            repairs.append(('free', wire, (left, right)))
            flip = 1 ^ s ^ t
            joined = tuple((x, sign) for x, sign in left if x != wire) + tuple(
                (x, sign ^ flip) for x, sign in right if x != wire)
            active = [gate for k, gate in enumerate(active) if k not in (i,j)]
            active.append(joined)
            continue
        break
    variables = sorted(adjacency)
    for values in product(range(2), repeat=len(variables)):
        assignment = [0]*n
        for v, value in zip(variables, values):
            assignment[v] = value
        if not all(gate_ok(gate, assignment) for gate in active):
            continue
        for mode, v, payload in reversed(repairs):
            if mode == 'parity':
                u, delta = payload
                assignment[v] = assignment[u] ^ delta
            else:
                for value in (0, 1):
                    assignment[v] = value
                    if all(gate_ok(gate, assignment) for gate in payload):
                        break
                else:
                    raise AssertionError('invalid inverse reduction')
        assert all(gate_ok(gate, assignment) for gate in original)
        return assignment
    return None

if __name__ == '__main__':
    import random
    rng = random.Random(199928)
    checks = 0
    for trial in range(2500):
        n = rng.randint(1, 7)
        gates = [
            [(rng.randrange(n), rng.randrange(2)) for _ in range(rng.randint(0 if trial%5==0 else 2, 6))]
            for _ in range(rng.randint(0, 10))
        ]
        expected = any(all(gate_ok(gate, a) for gate in gates) for a in product(range(2), repeat=n))
        found = solve(n, gates)
        assert (found is not None) == expected, (n, gates, found, expected)
        checks += 1
    print(checks, 'random signed NAE instances checked against exhaustive primal SAT')
