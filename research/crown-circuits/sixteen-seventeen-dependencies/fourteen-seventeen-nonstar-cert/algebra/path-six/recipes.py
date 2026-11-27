"""Generic OR cap three. Example: python -B recipes.py triangle-triangle."""
import sys
from itertools import combinations
import path

graphs = {
    "triangle-triangle": [(0,1),(1,2),(2,0),(3,4),(4,5),(5,3)],
    "paw-edge": [(0,1),(1,2),(2,0),(2,3),(4,5)],
    "path3-triangle": [(0,1),(1,2),(3,4),(4,5),(5,3)],
    "cycle4-edge": [(0,1),(1,2),(2,3),(3,0),(4,5)],
}

def check(name):
    graph = graphs[name]
    edges = [1<<a | 1<<b for a,b in graph]
    positive = sorted({a|b for a,b in combinations(edges,2)})
    path.edges = edges
    path.tests = edges + positive
    path.negative_bits = (1 << len(edges)) - 1
    path.required = ((1 << len(positive)) - 1) << len(edges)
    path.full = path.negative_bits | path.required
    base = path.initial_bank()
    if path.finish_with_at_most_one_or(base):
        return "at most one OR"
    count = 0
    for h in sorted(path.possible_new_ors(base)):
        one = path.extend(base,h)
        if path.finish_with_at_most_one_or(one):
            return "at most two ORs"
        for j in sorted(path.possible_new_ors(one)):
            count += 1
            if path.finish_with_at_most_one_or(path.extend(one,j)):
                return f"three ORs; helper signatures {h} and {j}"
    return f"no three-OR decoder after {count} ordered helper banks"

if __name__ == "__main__":
    print(sys.argv[1],check(sys.argv[1]))
