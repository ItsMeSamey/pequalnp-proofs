from itertools import combinations, product
from math import comb
from random import Random

from compiler import Chart, compile_charts, form_value, retain


def accepts(clauses, x):
    return all(any(form_value(f, x) for f in clause) for clause in clauses)


def contains(chart, x):
    return not any(form_value(f, x) for f in chart.equations)


def check_instance(p, guards, terminal):
    charts = compile_charts(p, guards, terminal)
    k = len(terminal)
    assert len(charts) <= sum(comb(p, i) for i in range(min(p, k) + 1))
    assert all(len(c.equations) <= k for c in charts)
    for x in range(1 << p):
        def valid(y):
            a = x | (y << p)
            return accepts(terminal, a) and all(
                not (y >> j & 1) or accepts([g], a) for j, g in enumerate(guards))
        covering = [c for c in charts if contains(c, x)]
        assert bool(covering) == any(valid(y) for y in range(1 << len(guards)))
        for c in covering:
            y = sum(form_value(f, x) << j for j, f in enumerate(c.witness))
            assert len(c.witness) == len(guards) and valid(y)


def graph_check(n):
    edges = list(combinations(range(n), 2))
    for mask in range(1 << len(edges)):
        pairs = [e for j, e in enumerate(edges) if (mask >> j) & 1]
        colors = [(2 << (2*v), 4 << (2*v)) for v in range(n)]
        charts = [Chart((a ^ 1, b ^ 1)) for a, b in colors]
        charts += [Chart(tuple(a ^ b for a, b in zip(colors[v], colors[w]))) for v, w in pairs]
        charts = retain(charts)
        for x in range(1 << (2*n)):
            labels = [(x >> (2*v)) & 3 for v in range(n)]
            proper = 3 not in labels and all(labels[v] != labels[w] for v, w in pairs)
            assert proper == (not any(contains(c, x) for c in charts))


if __name__ == '__main__':
    # Exhaust all guard/terminal subsets of affine forms on one observed and one hidden bit.
    clauses = [tuple(i for i in range(8) if (mask >> i) & 1) for mask in range(256)]
    for guard, terminal in product(clauses, repeat=2):
        check_instance(1, [guard], [terminal])
    rng = Random(734)
    for _ in range(800):
        p, h, k = (rng.randrange(5) for _ in range(3))
        def clause(n):
            return tuple(rng.randrange(1 << (n+1)) for _ in range(rng.randrange(5)))
        check_instance(p, [clause(p+j+1) for j in range(h)], [clause(p+h) for _ in range(k)])
    for n in range(1, 5):
        graph_check(n)
    print("Checked 65,536 one-bit instances, 800 larger instances and 75 labeled graphs.")
