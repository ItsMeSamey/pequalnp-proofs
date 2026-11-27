"""Exact finite-domain binary CSP evaluation on a supplied tree decomposition."""
from itertools import product


def _decomposition(domains, constraints, bags, tree_edges):
    bags = [tuple(bag) for bag in bags]
    bag_sets = [set(bag) for bag in bags]
    occurrences = {u: set() for u in domains}
    for i, bag in enumerate(bags):
        if len(bag) != len(bag_sets[i]):
            raise ValueError('duplicate vertex in bag')
        for u in bag:
            if u not in occurrences:
                raise ValueError('unknown vertex in bag')
            occurrences[u].add(i)
    if any(not ids for ids in occurrences.values()):
        raise ValueError('uncovered CSP vertex')
    neighbors = [[] for _ in bags]
    seen = set()
    for i, j in tree_edges:
        if any(type(k) is not int or not 0 <= k < len(bags) for k in (i, j)):
            raise ValueError('invalid bag index')
        edge = (min(i, j), max(i, j))
        if i == j or edge in seen:
            raise ValueError('invalid tree edge')
        seen.add(edge)
        neighbors[i].append(j)
        neighbors[j].append(i)
    if len(seen) != max(0, len(bags) - 1):
        raise ValueError('bag graph is not a tree')
    visited = set()
    todo = [0] if bags else []
    while todo:
        i = todo.pop()
        if i not in visited:
            visited.add(i)
            todo.extend(neighbors[i])
    if len(visited) != len(bags):
        raise ValueError('disconnected bag graph')
    internal_edges = dict.fromkeys(domains, 0)
    for i, j in seen:
        for u in bag_sets[i] & bag_sets[j]:
            internal_edges[u] += 1
    if any(internal_edges[u] + 1 != len(ids) for u, ids in occurrences.items()):
        raise ValueError('running intersection violation')
    assigned = [[] for _ in bags]
    positions = [{u: j for j, u in enumerate(bag)} for bag in bags]
    for u, v, relation in constraints:
        if u not in occurrences or v not in occurrences:
            raise ValueError('unknown constraint vertex')
        hosts = occurrences[u] & occurrences[v]
        if not hosts:
            raise ValueError('uncovered CSP edge')
        host = min(hosts)
        assigned[host].append((positions[host][u], positions[host][v], set(relation)))
    return bags, positions, occurrences, neighbors, assigned


def solve(domains, constraints, bags, tree_edges, output, *, state_cap=None, step_cap=None):
    """Return one full assignment per attainable Boolean output.

    states counts tried bag rows; steps also charges relation and child lookups.
    A cap interrupts before the next charge and yields unknown. The caller
    decodes and replays assignments against the original predictor.
    """
    for cap in (state_cap, step_cap):
        if cap is not None and (type(cap) is not int or cap < 0):
            raise ValueError('caps must be nonnegative integers')
    domains = {u: tuple(dict.fromkeys(values)) for u, values in domains.items()}
    bags, positions, occurrences, neighbors, assigned = _decomposition(
        domains, constraints, bags, tree_edges)
    if output not in domains or any(type(v) not in (bool, int) or v not in (0, 1)
                                    for v in domains[output]):
        raise ValueError('designated Boolean output variable required')
    root = min(occurrences[output])
    parent = {root: None}
    order = [root]
    children = [[] for _ in bags]
    child_keys = [[] for _ in bags]
    separators = [() for _ in bags]
    for i in order:
        for j in neighbors[i]:
            if j == parent[i]:
                continue
            parent[j] = i
            order.append(j)
            children[i].append(j)
            common = [u for u in bags[j] if u in positions[i]]
            separators[j] = tuple(positions[j][u] for u in common)
            child_keys[i].append(tuple(positions[i][u] for u in common))
    tables = [{} for _ in bags]
    states = steps = 0
    width = max(map(len, bags)) - 1

    def result(status, **fields):
        return dict(status=status, width=width, states=states, steps=steps,
                    witnesses={}, **fields)

    def exhausted():
        return result('unknown', reason='cap')

    for i in reversed(order):
        for row in product(*(domains[u] for u in bags[i])):
            if ((state_cap is not None and states >= state_cap) or
                    (step_cap is not None and steps >= step_cap)):
                return exhausted()
            states += 1
            steps += 1
            for a, b, relation in assigned[i]:
                if step_cap is not None and steps >= step_cap:
                    return exhausted()
                steps += 1
                if (row[a], row[b]) not in relation:
                    break
            else:
                for j, columns in zip(children[i], child_keys[i]):
                    if step_cap is not None and steps >= step_cap:
                        return exhausted()
                    steps += 1
                    if tuple(row[t] for t in columns) not in tables[j]:
                        break
                else:
                    key = (int(row[positions[i][output]]) if i == root else
                           tuple(row[t] for t in separators[i]))
                    tables[i].setdefault(key, row)
    bits = tables[root].keys()
    answer = result(('empty', 'constant', 'pair')[len(bits)])
    for bit in bits:
        witness = {}
        pending = [(root, bit)]
        while pending:
            i, key = pending.pop()
            row = tables[i][key]
            witness.update(zip(bags[i], row))
            for j, columns in zip(children[i], child_keys[i]):
                pending.append((j, tuple(row[t] for t in columns)))
        answer['witnesses'][bit] = witness
    if len(bits) == 1:
        answer['value'] = next(iter(bits))
    return answer
