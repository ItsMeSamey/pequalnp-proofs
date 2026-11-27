"""Exact ordered Boolean circuit history-cover compiler. Bit 0 is the affine constant."""
from dataclasses import dataclass


def cuts(n, gates, out):
    for i in range(len(gates) + 1):
        mask = (1 << i) - 1
        rows = [r for gate in gates[i:] for r in gate] + [out]
        yield [(r >> (n + 1)) & mask for r in rows]


def conflicts(n, gates, out):
    edges = set()
    for i, rows in enumerate(cuts(n, gates, out)):
        columns = [sum(((r >> j) & 1) << k for k, r in enumerate(rows)) for j in range(i)]
        for j, u in enumerate(columns):
            if u:
                edges.update((h, j) for h in range(j) if columns[h] and columns[h] != u)
    return edges


def search_cover(edges, t, stats=None):
    if stats is not None:
        stats['nodes'] = stats.get('nodes', 0) + 1
    if not edges:
        return set()
    if t <= 0:
        return None
    for vertex in min(edges):
        found = search_cover({e for e in edges if vertex not in e}, t - 1, stats)
        if found is not None:
            return found | {vertex}
    return None


def direct(n, gates, out, x):
    word = 1 | x << 1
    for i, (a, b, c) in enumerate(gates):
        bit = (parity(a & word) & parity(b & word)) ^ parity(c & word)
        word |= bit << (n + 1 + i)
    return parity(out & word)


def parity(word):
    return word.bit_count() & 1


def value(poly, word):
    return sum(all(parity(f & word) for f in term) for term in poly) & 1


@dataclass
class System:
    n: int
    definitions: list
    final: list

    def evaluate(self, x):
        word = 1 | x << 1
        for bit, poly in self.definitions:
            word |= value(poly, word) * bit
        return value(self.final, word)

    def count_witness(self, counter=None):
        # Backend contract: exact joint count with given raw prefix bits pinned.
        if counter is None:
            accepted = [x for x in range(1 << self.n) if self.evaluate(x)]
            return len(accepted), next(iter(accepted), None)
        total = counter(self, 0, 0)
        if not total:
            return 0, None
        pins = assignment = 0
        for i in range(self.n):
            pins |= 1 << i
            if not counter(self, pins, assignment):
                assignment |= 1 << i
        assert self.evaluate(assignment)
        return total, assignment


def compile_system(n, gates, out, S):
    selected = sorted(S)
    m = len(gates)
    if any(i < 0 or i >= m for i in selected):
        raise ValueError('invalid gate ID')
    for i, gate in enumerate(gates):
        if len(gate) != 3 or any(r < 0 or r >> (n + i + 1) for r in gate):
            raise ValueError('invalid operand or gate order')
    if out < 0 or out >> (n + m + 1):
        raise ValueError('invalid output')
    named = {j: 1 << (n + 1 + k) for k, j in enumerate(selected)}
    deleted = sum(1 << j for j in selected)
    history = []
    for rows in cuts(n, gates, out):
        basis = {row & ~deleted for row in rows} - {0}
        if len(basis) > 1:
            raise ValueError('uncovered cut')
        history.append(next(iter(basis), 0))
    raw = (1 << (n + 1)) - 1

    def split(r, i):
        old = r >> (n + 1)
        base = r & raw
        for j, bit in named.items():
            if old >> j & 1:
                base ^= bit
        residual = old & ~deleted
        assert residual == 0 or residual == history[i]
        return base, int(bool(residual))

    definitions = []
    state = []
    for i, (a, b, c) in enumerate(gates):
        u, f = split(a, i)
        v, g = split(b, i)
        w, h = split(c, i)
        coefficient = (u if g else 0) ^ (v if f else 0) ^ (f & g) ^ h
        constant = [(u, v), (w,)]
        old = history[i + 1] & ((1 << i) - 1)
        assert old == 0 or old == history[i]
        if i in named:
            checkpoint = named[i] << len(named)
            definitions.append((checkpoint, state))
            definitions.append((named[i], constant + [(coefficient, checkpoint)]))
            state = [(checkpoint,)] if old else []
        elif history[i + 1] >> i & 1:
            scale = coefficient ^ int(bool(old))
            state = [term + (scale,) for term in state] + constant if scale else constant
        elif not old:
            state = []
    base, active = split(out, m)
    return System(n, definitions, [(base,)] + (state if active else []))
