"""Construct width-seven path bags for a supplied minimal two-pin all-odd support."""
import argparse
import json
import sys

from three_connected_odd_pair import indexed_graph


def validate(graph, bags):
    """Check coverage, consecutive appearances, bag size and every original edge."""
    first = [None] * len(graph)
    last = [None] * len(graph)
    for t, bag in enumerate(bags):
        if len(bag) > 8 or len(set(bag)) != len(bag):
            return False
        for v in bag:
            if type(v) is not int or not 0 <= v < len(graph):
                return False
            if first[v] is None:
                first[v] = t
            elif last[v] != t - 1:
                return False
            last[v] = t
    if any(t is None for t in first):
        return False
    return all(first[v] <= last[u] and first[u] <= last[v]
               for u, neighbors in enumerate(graph) for v in neighbors)


def exceptional(graph, active, pins):
    q, v = sorted(pins, key=lambda i: len(graph[i]))
    common = graph[q]
    other = graph[v] - common
    if len(active) != 10 or len(common) != 3 or len(graph[v]) != 7 or not common <= graph[v]:
        return None
    outside = active - common - other - {q, v}
    if len(outside) != 1:
        return None
    return [outside | other, other | common | {v}, common | {q, v}]


def construct(lists, pins):
    original = indexed_graph(lists)
    n = len(original)
    if (not isinstance(pins, (tuple, list)) or len(pins) != 2 or pins[0] == pins[1]
            or any(type(v) is not int or not 0 <= v < n for v in pins)):
        raise ValueError("two distinct original pin indices required")
    if any(len(r) not in (1, 3, 5) for r in original):
        raise ValueError("the supplied support must have degrees one, three or five")
    graph = [set(r) for r in original]
    active = set(range(n))
    p, q = pins
    history = []
    bags = None
    while len(active) > 8:
        if len(graph[p]) > 5 or len(graph[q]) > 5:
            bags = exceptional(graph, active, (p, q))
            break
        if len(graph[q]) == 1:
            p, q = q, p
        if len(graph[p]) != 1 or q in graph[p]:
            break
        u, = graph[p]
        toggles = []
        if len(graph[q]) == 1:
            v, = graph[q]
            if u == v or v not in graph[u]:
                break
            toggles.append((u, v))
            gone = (p, q)
            child = (u, v)
            bag = {p, q, u, v}
        else:
            common = graph[u] & graph[q]
            if u not in graph[q]:
                extra = graph[u] - common - {p}
                if graph[q] != common or len(common) != 3 or len(extra) != 1:
                    break
                v, = extra
                toggles.extend((v, j) for j in common)
            else:
                extra = graph[q] - common - {u}
                if graph[u] != common | {p, q}:
                    break
                if len(common) == 1:
                    v, = common
                elif len(common) == 3 and len(extra) == 1:
                    v, = extra
                    toggles.extend((v, j) for j in common)
                else:
                    break
                toggles.append((q, v))
            gone = (p, u)
            child = (q, v)
            bag = {p, u, q, v} | graph[q]
        for i, j in toggles:
            if j in graph[i]:
                graph[i].remove(j)
                graph[j].remove(i)
            else:
                graph[i].add(j)
                graph[j].add(i)
        for i in gone:
            for j in graph[i]:
                graph[j].remove(i)
            graph[i].clear()
            active.remove(i)
        history.append(bag)
        p, q = child
    if len(active) <= 8:
        bags = [active]
    if bags is not None:
        result = [sorted(s) for s in bags + history[::-1]]
        if validate(original, result):
            return dict(status="CERTIFIED", width=max(map(len, result))-1, bags=result)
    return dict(status="UNKNOWN", width=None, bags=None)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("input", nargs="?", type=argparse.FileType("r"), default=sys.stdin)
    args = parser.parse_args()
    try:
        data = json.load(args.input)
        print(json.dumps(construct(data["neighbors"], data["pins"])))
    except (ValueError, TypeError, KeyError) as error:
        parser.error(str(error))


if __name__ == "__main__":
    main()
