"""Connected-component atlas census of ten-edge hosts with a degree-four flag."""
from collections import Counter
import networkx as nx


def enumerate_hosts():
    # The center requires four edges; two remote pure-bearing components
    # require at least two more each. No component can exceed six edges.
    types = []
    for graph in nx.graph_atlas_g():
        edges = graph.number_of_edges()
        if not 1 <= edges <= 6 or not nx.is_connected(graph):
            continue
        degree = max(d for _, d in graph.degree())
        if degree <= 4:
            types.append((edges, degree, graph))
    types.sort(key=lambda item: item[:2])
    counts = Counter()

    def extend(selection, remaining, start):
        if remaining:
            for i in range(start, len(types)):
                edges = types[i][0]
                if edges > remaining:
                    break
                extend(selection + [types[i]], remaining - edges, i)
            return
        if sum(d >= 2 for _, _, g in selection for _,d in g.degree()) < 5 and all(all(d != 3 for _,d in g.degree()) for _,_,g in selection):
            return
        if not any(d == 4 for _, d, _ in selection):
            return
        if sum(d >= 2 for _, d, _ in selection) < 3:
            return
        for center, (_, degree, _) in enumerate(selection):
            if degree < 4:
                continue
            shapes = {(0, 0)}
            for j, (_, _, graph) in enumerate(selection):
                if j == center:
                    continue
                options = set()
                potential = [v for v, d in graph.degree() if d >= 2]
                for mask in range(1 << len(potential)):
                    kept = [v for i, v in enumerate(potential) if mask >> i & 1]
                    parts = list(nx.connected_components(graph.subgraph(kept)))
                    options.add((sum(len(comp) > 1 for comp in parts),
                                 sum(len(comp) == 1 for comp in parts)))
                shapes = {(a+c, b+d) for a,b in shapes for c,d in options}
            if not any(k+h-int(h>0) >= 2 for k,h in shapes):
                return
        counts[tuple(sorted((e for e, _, _ in selection), reverse=True))] += 1

    extend([], 10, 0)
    return counts


if __name__ == '__main__':
    for sizes, count in sorted(enumerate_hosts().items()):
        print(sizes, count)
