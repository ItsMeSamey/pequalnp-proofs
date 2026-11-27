"""Compare greedy arbitrary gate pairs with the exact fixed-order interval optimum."""

from itertools import combinations

from corridor_nand import _net, _project, _rows, corridor_witness
from interval_optimizer import minimum_partition


class _Costs:
    def __init__(self, inputs, gates, observed):
        self.inputs = inputs
        self.gates = _net(inputs, gates)
        n = inputs + len(self.gates)
        self.observed = set(observed)
        if any(type(v) is not int or not 0 <= v < n for v in self.observed):
            raise ValueError("invalid observed wire")
        self.reader_count = [0] * n
        for gate in self.gates:
            for v in set(gate):
                self.reader_count[v] += 1

    def score(self, group):
        outputs = {self.inputs + i for i in group}
        local_readers = {}
        for i in group:
            for v in set(self.gates[i]):
                local_readers[v] = local_readers.get(v, 0) + 1
        entries = sorted(local_readers.keys() - outputs)
        if len(entries) > 2:
            return None
        ports = sorted(v for v in outputs.union(entries)
                       if v in self.observed
                       or self.reader_count[v] > local_readers.get(v, 0)
                       or (v in entries and v >= self.inputs))
        _, bad = _project(self.inputs, self.gates, group, ports, entries)
        return int(bad)

    def verify(self, groups, expected):
        covered = sorted(i for group in groups for i in group)
        if covered != list(range(len(self.gates))):
            raise AssertionError("partition does not cover each gate once")
        costs = [self.score(group) for group in groups]
        if None in costs or sum(costs) != expected:
            raise AssertionError("physical projection cost disagrees with partition score")


def _greedy(costs, seed):
    size = len(seed)
    original = [costs.score(group) for group in seed]
    if None in original:
        raise ValueError("inadmissible seed block")
    gains = {1: [], 2: []}
    for i, j in combinations(range(size), 2):
        merged = tuple(sorted(seed[i] + seed[j]))
        score = costs.score(merged)
        if score is not None:
            gain = original[i] + original[j] - score
            if gain > 0:
                gains[gain].append((i, j))
    occupied = set()
    groups = []
    total = sum(original)
    for gain in (2, 1):
        for i, j in gains[gain]:
            if i not in occupied and j not in occupied:
                occupied.update((i, j))
                groups.append(tuple(sorted(seed[i] + seed[j])))
                total -= gain
    groups.extend(seed[i] for i in range(size) if i not in occupied)
    return total, tuple(sorted(groups))


def _singletons(costs):
    return tuple((i,) for i in range(len(costs.gates)))


def _intervals(costs):
    score, ranges = minimum_partition(costs.inputs, costs.gates, costs.observed)
    seed = tuple(tuple(range(start, stop)) for start, stop in ranges)
    costs.verify(seed, score)
    return seed


def coarsened_interval_partition(inputs, gates, observed=()):
    """Gain at least half the best one-round pair-coarsening saving of the interval seed."""
    costs = _Costs(inputs, gates, observed)
    score, groups = _greedy(costs, _intervals(costs))
    costs.verify(groups, score)
    return score, groups


def greedy_pair_partition(inputs, gates, observed=()):
    """Return (bad, groups), gaining at least half the best pair-partition saving.

    Charge each optimal positive edge to the first greedy edge blocking it
    (possibly itself). That edge has at least the charged weight and its two
    endpoints can block at most two optimal matching edges. The singleton
    baseline minus matching weight is exactly the true projection cost.
    """
    costs = _Costs(inputs, gates, observed)
    score, groups = _greedy(costs, _singletons(costs))
    costs.verify(groups, score)
    return score, groups


def best_partition(inputs, gates, observed=()):
    """Pick the cheaper greedy coarsening of singleton and optimal interval seeds.

    Ties prefer the interval seed's coarsening. Both passes score every
    candidate union on original gate IDs. For g gates, their preprocessing
    uses polynomial time (a conservative O(g**3 log(g+2)) indexed bound)
    and O(g**2) storage, in addition to the interval optimizer.
    """
    costs = _Costs(inputs, gates, observed)
    pairs = _greedy(costs, _singletons(costs))
    intervals = _greedy(costs, _intervals(costs))
    score, groups = intervals if intervals[0] <= pairs[0] else pairs
    costs.verify(groups, score)
    return score, groups


def pair_interval_witness(inputs, gates, *, clauses=(), pins=(), equalities=()):
    """Solve the original gated CSP using the chosen physical gate partition."""
    gates = _net(inputs, gates)
    clauses = tuple(tuple(c) for c in clauses)
    pins = tuple(tuple(p) for p in pins)
    equalities = tuple(tuple(eq) for eq in equalities)
    rows = _rows(inputs + len(gates), clauses, pins, equalities)
    observed = {abs(l)-1 for row in rows for l in row}
    bad, groups = best_partition(inputs, gates, observed)
    status, raw = corridor_witness(inputs, gates, groups, clauses=clauses, pins=pins,
                                  equalities=equalities, max_bad=bad)
    if status not in ("sat", "unsat"):
        raise AssertionError("verified partition was skipped")
    return bad, groups, raw
