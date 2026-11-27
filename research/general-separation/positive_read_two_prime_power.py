"""Positive read-two CNF interpolation modulo 3**k."""
import argparse
import json
import sys
from operator import index


def _gauss(m, negative, pins):
    free = set(range(m)) - pins
    linear = free.copy()
    pairs = set()
    constant = 0
    for incident in negative:
        live = [i for i in incident if i in free]
        linear.symmetric_difference_update(live)
        if len(live) == 2:
            pairs.symmetric_difference_update([tuple(live)])
    pivots = 0
    while pairs:
        u, v = pairs.pop()
        a, b = u in linear, v in linear
        linear.discard(u)
        linear.discard(v)
        left, right, rest = set(), set(), set()
        for i, j in pairs:
            if u in (i, j):
                left.add(j if i == u else i)
            elif v in (i, j):
                right.add(j if i == v else i)
            else:
                rest.add((i, j))
        pairs = rest
        constant ^= a and b
        if a:
            linear.symmetric_difference_update(right)
        if b:
            linear.symmetric_difference_update(left)
        for i in left:
            for j in right:
                if i == j:
                    linear.symmetric_difference_update([i])
                else:
                    pairs.symmetric_difference_update([(min(i,j), max(i,j))])
        pivots += 1
    if linear:
        return 0
    magnitude = 1 << (len(free) - pivots)
    return -magnitude if constant else magnitude


def _subsets(costs, k):
    """Iterative DFS of admissible subsets."""
    chosen = []
    stack = [(0, 0)]
    yield ()
    while stack:
        j, total = stack[-1]
        if j == len(costs):
            stack.pop()
            if chosen:
                chosen.pop()
            continue
        stack[-1] = (j + 1, total)
        cost = total + costs[j]
        if cost < k:
            chosen.append(j)
            yield tuple(chosen)
            stack.append((j + 1, cost))


def _contractions(costs, k):
    counts = {0: 1}
    for cost in costs:
        updated = counts.copy()
        for total, count in counts.items():
            if total + cost < k:
                new = total + cost
                updated[new] = updated.get(new, 0) + 2 * count
        counts = updated
    return sum(counts.values())


def evaluate(n, clauses, point, k, *, max_contractions=None):
    n, k = index(n), index(k)
    if n < 0 or k < 1 or len(point) != n:
        raise ValueError("require n >= 0, k >= 1 and exactly n coordinates")
    if max_contractions is not None:
        max_contractions = index(max_contractions)
        if max_contractions < 0:
            raise ValueError("negative contraction budget")
    modulus = 3 ** k
    point = [index(x) % modulus for x in point]
    reads = [0] * n
    active = []
    empty = False
    for clause in clauses:
        live = set()
        satisfied = False
        for entry in clause:
            i = index(entry)
            if not 0 <= i < n:
                raise ValueError("variable index out of range")
            reads[i] += 1
            if reads[i] > 2:
                raise ValueError("more than two raw occurrences")
            if point[i] == 1:
                satisfied = True
            elif point[i] != 0:
                live.add(i)
        if not satisfied:
            if not live:
                empty = True
            active.append(live)
    if empty or not active:
        return dict(status="exact", value=int(not empty), contractions=0)

    occurrences = [[] for _ in point]
    for c, clause in enumerate(active):
        for i in clause:
            occurrences[i].append(c)
    grouped = {}
    for i, incident in enumerate(occurrences):
        if incident:
            key = tuple(incident)
            grouped[key] = grouped.get(key, 1) * (1 - point[i]) % modulus
    zero = set()
    negative = set()
    defects, costs, deltas = [], [], []
    for key, weight in grouped.items():
        base = (0, 1, -1)[weight % 3]
        if base == 0:
            zero.add(key)
        elif base == -1:
            negative.add(key)
        delta = (weight - base) % modulus
        if delta:
            defects.append(key)
            deltas.append(delta)
            valuation = 0
            while delta % 3 == 0:
                delta //= 3
                valuation += 1
            costs.append(valuation)
    required = _contractions(costs, k)
    if max_contractions is not None and max_contractions < required:
        return dict(status="unknown", reason="contraction_budget",
                    required=required, available=max_contractions)
    answer = 0
    for subset in _subsets(costs, k):
        selected = [defects[i] for i in subset]
        keep_zero = zero.difference(selected)
        pinned = {v for key in keep_zero for v in key}
        signs = negative.difference(selected)
        coefficient = 1
        for i in subset:
            coefficient = coefficient * deltas[i] % modulus
        for mask in range(1 << len(selected)):
            fixed = pinned.copy()
            for j, key in enumerate(selected):
                if (mask >> j) & 1:
                    fixed.update(key)
            term = _gauss(len(active), signs, fixed)
            if mask.bit_count() & 1:
                term = -term
            answer = (answer + coefficient * term) % modulus
    return dict(status="exact", value=answer, contractions=required)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--max-contractions", type=int)
    if hasattr(sys, "set_int_max_str_digits"):
        sys.set_int_max_str_digits(0)
    options = parser.parse_args()
    try:
        request = json.load(sys.stdin)
        if not isinstance(request, dict) or set(request) != {"n", "k", "point", "clauses"}:
            raise ValueError("expected n, k, point and clauses")
        if not isinstance(request["point"], list) or not isinstance(request["clauses"], list):
            raise ValueError("expected point and clauses arrays")
        if any(not isinstance(c, list) for c in request["clauses"]):
            raise ValueError("expected each clause to be an array")
        result = evaluate(**request, max_contractions=options.max_contractions)
    except (TypeError, ValueError, OverflowError) as exc:
        print(json.dumps(dict(status="error", reason=str(exc))))
        return 2
    print(json.dumps(result))
    return 0


if __name__ == "__main__":
    sys.exit(main())
