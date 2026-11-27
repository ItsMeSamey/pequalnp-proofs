"""Check restricted one-flip sensitivity and exhaust the unrestricted native masks."""
from itertools import product


def build(n, clauses):
    ring0, ring1 = [0], [1]  # distinct wire marks
    variable = [(2+3*i, 3+3*i, 4+3*i) for i in range(n)]
    next_label = 2+3*n
    chunks = [[] for _ in range(n)]
    probes = []
    for clause in clauses:
        first, second = [], []
        for i in clause:
            x, y = next_label, next_label+1
            next_label += 2
            chunks[i].extend((x, y))
            first.append(x)
            second.append(y)
        probes.extend((tuple(first), (second[0], second[2], second[1])))
    for (u,v,w), chunk in zip(variable, chunks):
        ring0.extend([u, *chunk, v])
        ring1.append(w)
    p = list(range(next_label))
    for ring in (ring0, ring1):
        for j, v in enumerate(ring):
            p[v] = ring[(j+1) % len(ring)]
    return p, variable, probes


def toggle(p, gate, reverse=False):
    a, b, c = gate
    if reverse:
        b, c = c, b
    p[a], p[b], p[c] = p[b], p[c], p[a]


def join(p):
    x = p[0]
    while x > 1:
        x = p[x]
    return x == 1


def check(n, clauses):
    base, var, probes = build(n, clauses)
    best = satisfying = unrestricted = 0
    all_on_yes = 0
    for assignment in product((0, 1), repeat=n):
        p = base.copy()
        for bit, gate in zip(assignment, var):
            if bit:
                toggle(p, gate)
        assert not join(p)
        score = 0
        for j, clause in enumerate(clauses):
            cnt = 0
            for gate in probes[2*j:2*j+2]:
                toggle(p, gate)
                cnt += join(p)
                toggle(p, gate, True)
            assert cnt == (len({assignment[i] for i in clause}) > 1)
            score += cnt
        best = max(best, score)
        satisfying += score == len(clauses)
        # Enumerate all simultaneous probe subsets in Gray-code order.
        gray = 0
        for step in range(1, 1 << len(probes)):
            i = (step & -step).bit_length()-1
            gray ^= 1 << i
            toggle(p, probes[i], not ((gray >> i) & 1))
            result = join(p)
            unrestricted += result
            if gray == (1 << len(probes))-1:
                all_on_yes += result
    return best, satisfying, unrestricted, all_on_yes


if __name__ == "__main__":
    fano = [(0,1,2), (0,3,4), (0,5,6), (1,3,5), (1,4,6), (2,3,6), (2,4,5)]
    for name, n, clauses in [
        ("one clause", 3, [(0,1,2)]), ("Fano minus one line", 7, fano[:-1]), ("Fano", 7, fano)
    ]:
        result = check(n, clauses)
        print(name, result, flush=True)
        assert (result[1] > 0) == (name != "Fano")
        assert result[2] > 0
