"""Finite exhaustive comparison of successor tours and the switch/interlacement test.

Vertex labels are 0..n-1. A switch on a cycle tau maps output track i to
tau(i), followed by feedback sigma; the successor is sigma[tau[i]].
This checker enumerates switch settings, not delta-matroid parity algorithms.
"""
import itertools
import random
from collections import Counter


def cycles(perm):
    seen = set()
    parts = []
    for i in range(len(perm)):
        if i not in seen:
            part = []
            while i not in seen:
                seen.add(i)
                part.append(i)
                i = perm[i]
            parts.append(tuple(part))
    return parts


def all_tours(rows):
    result = set()
    for order in itertools.permutations(range(1, len(rows))):
        path = (0,) + order
        edges = list(zip(path, path[1:] + (0,)))
        if all(j in rows[i] for i, j in edges):
            result.add(tuple(j for i, j in sorted(edges)))
    return result


def reference_matching(rows):
    owner = {}
    def augment(i, seen):
        for j in rows[i]:
            if j in seen:
                continue
            seen.add(j)
            if j not in owner or augment(owner[j], seen):
                owner[j] = i
                return True
        return False
    if not all(augment(i, set()) for i in range(len(rows))):
        return None
    return tuple(j for j, i in sorted(owner.items(), key=lambda ji: ji[1]))


def relative_cycles(rows, sigma):
    inverse = {j: i for i, j in enumerate(sigma)}
    alternate = {i: inverse[j] for i, row in enumerate(rows)
                 for j in row if j != sigma[i]}
    done = set()
    parts = []
    for start in alternate:
        path = {}
        i = start
        while i in alternate and i not in done and i not in path:
            path[i] = len(path)
            i = alternate[i]
        if i in path:
            parts.append(tuple(path)[path[i]:])
        done.update(path)
    return parts, len(alternate) - sum(map(len, parts))


def multiply(sigma, parts):
    successor = list(sigma)
    for part in parts:
        for i, j in zip(part, part[1:] + part[:1]):
            successor[i] = sigma[j]
    return tuple(successor)


def network(sigma, parts):
    # Retain a forced unary node on every track, even on switchless circuits.
    n = len(sigma)
    tail = [(i, 0) for i in range(n)]
    edges = []
    groups = []
    switch_count = 0
    for part in parts:
        group = []
        for track in part[1:]:
            switch = n + switch_count
            group.append(switch_count)
            switch_count += 1
            for port, i in enumerate((part[0], track)):
                edges.append((tail[i], (switch, port)))
                tail[i] = (switch, port)
        groups.append(group)
    for i in range(n):
        edges.append((tail[i], (sigma[i], 0)))
    return edges, groups, switch_count


def euler_data(edges, n, switches):
    outgoing = [[] for _ in range(n + switches)]
    for i, ((v, _), _) in enumerate(edges):
        outgoing[v].append(i)
    baseline = 0
    interlace = [0] * switches
    components = 0
    for start in range(len(outgoing)):
        if not outgoing[start]:
            continue
        components += 1
        stack = [(start, None)]
        tour = []
        while stack:
            v, last = stack[-1]
            if outgoing[v]:
                e = outgoing[v].pop()
                stack.append((edges[e][1][0], e))
            else:
                stack.pop()
                if last is not None:
                    tour.append(last)
        tour.reverse()
        word = []
        for a, b in zip(tour, tour[1:] + tour[:1]):
            (v, incoming), (u, leaving) = edges[a][1], edges[b][0]
            assert v == u
            if v >= n:
                i = v - n
                word.append(i)
                if incoming != leaving:
                    baseline |= 1 << i
        for i in set(word):
            left = word.index(i)
            right = word.index(i, left + 1)
            for j in word[left+1:right]:
                interlace[i] ^= 1 << j
    return components, baseline, interlace


def rank(rows):
    pivots = {}
    for row in rows:
        while row:
            i = row.bit_length()
            if i not in pivots:
                pivots[i] = row
                break
            row ^= pivots[i]
    return len(pivots)


def verify(rows, stats):
    n = len(rows)
    stats['graphs'] += 1
    indegrees = [sum(j in row for row in rows) for j in range(n)]
    if any(d != 2 for d in indegrees):
        stats['non_two_indegrees'] += 1
    direct = all_tours(rows)
    covers = {p for p in itertools.product(*rows) if len(set(p)) == n}
    sigma = reference_matching(rows)
    if sigma is None:
        assert not covers and not direct
        stats['no_matching'] += 1
        return
    parts, tails = relative_cycles(rows, sigma)
    if tails:
        stats['graphs_with_alternate_tails'] += 1
    for m in set(map(len, parts)):
        stats[f'graphs_with_relative_{m}'] += 1
    long_parts = [p for p in parts if len(p) > 3]
    short = [p for p in parts if len(p) <= 3]
    derived_covers, observed_tours = set(), set()
    for picks in itertools.product((0, 1), repeat=len(long_parts)):
        base = multiply(sigma, [p for p, b in zip(long_parts, picks) if b])
        edges, groups, count = network(base, short)
        c, baseline, matrix = euler_data(edges, n, count)
        stats['networks'] += 1
        if c > 1:
            stats['disconnected_networks'] += 1
        if not count:
            stats['switchless_networks'] += 1
        if any(len(g) == 2 and ((baseline >> g[0]) ^ (baseline >> g[1])) & 1 for g in groups):
            stats['unequal_baseline_networks'] += 1
        for mask in range(1 << count):
            physical = list(range(n))
            for part, group in zip(short, groups):
                for track, i in zip(part[1:], group):
                    if mask & (1 << i):
                        physical = [track if v == part[0] else part[0] if v == track else v
                                    for v in physical]
            p = tuple(base[i] for i in physical)
            changed = mask ^ baseline
            nullity = changed.bit_count() - rank(
                row & changed for i, row in enumerate(matrix) if changed & (1 << i))
            predicted = c + nullity
            assert predicted == len(cycles(p)), (rows, base, mask, p)
            stats['physical_settings'] += 1
            if any(len({(mask >> i) & 1 for i in g}) != 1 for g in groups):
                continue
            active = [part for part, g in zip(short, groups) if mask & (1 << g[0])]
            assert p == multiply(base, active)
            assert p not in derived_covers
            derived_covers.add(p)
            stats['legal_settings'] += 1
            if predicted == 1:
                observed_tours.add(p)
    assert derived_covers == covers, (rows, parts, covers ^ derived_covers)
    assert observed_tours == direct, (rows, direct ^ observed_tours)
    stats['yes_graphs'] += bool(direct)
    stats['tours'] += len(direct)


def main():
    stats = Counter()
    for n in range(3, 5):
        choices = [list(itertools.combinations([j for j in range(n) if j != i], 2))
                   for i in range(n)]
        for rows in itertools.product(*choices):
            verify(rows, stats)
    print('exhaustive exactly-two loop-free through n=4', dict(sorted(stats.items())))
    rng = random.Random(80519)
    stats = Counter()
    for n in range(1, 9):
        for _ in range(40):
            rows = [tuple(rng.sample(range(n), rng.randrange(min(2, n) + 1))) for i in range(n)]
            verify(rows, stats)
        for _ in range(60):
            sigma = list(range(n))
            rng.shuffle(sigma)
            rows = [tuple(sorted({sigma[i], rng.randrange(n)})) for i in range(n)]
            verify(rows, stats)
        for _ in range(35):
            sigma, tau = list(range(n)), list(range(n))
            rng.shuffle(sigma)
            rng.shuffle(tau)
            verify([tuple(sorted({sigma[i], tau[i]})) for i in range(n)], stats)
    print('seed 80519 random maximum-outdegree-two through n=8', dict(sorted(stats.items())))
    assert stats['graphs_with_relative_3'] and stats['graphs_with_relative_4']
    assert stats['unequal_baseline_networks'] and stats['graphs_with_alternate_tails']


if __name__ == '__main__':
    main()
