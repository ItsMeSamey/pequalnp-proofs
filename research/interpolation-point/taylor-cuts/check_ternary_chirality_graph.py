from itertools import product
from ternary_chirality_graph import compile_graph, decode, encode


def colour(graph):
    neighbours = [set() for _ in range(graph.order)]
    for u, v in graph.edges:
        neighbours[u].add(v)
        neighbours[v].add(u)
    values = [-1] * graph.order
    def extend():
        choices = []
        for v, a in enumerate(values):
            if a < 0:
                free = {0, 1, 2} - {values[w] for w in neighbours[v]}
                choices.append((len(free), -len(neighbours[v]), v, free))
        if not choices:
            return tuple(values)
        _, _, v, free = min(choices)
        for c in sorted(free):
            values[v] = c
            answer = extend()
            if answer is not None:
                return answer
        values[v] = -1
    return extend()


def check(n, rows):
    g = compile_graph(n, rows)
    good = [s for s in product((1, 2), repeat=n)
            if all(sum(a*b for a,b in zip(s,r))%3 == 0 for r in rows)]
    for s in good:
        assert decode(g, encode(g, s)) == s
    witness = colour(g)
    assert (witness is not None) == bool(good)
    if witness is not None:
        assert decode(g,witness) in good


if __name__ == "__main__":
    check(0,[()])
    for n in range(1,4):
        for row in product(range(3), repeat=n):
            check(n,[row])
    for a,b in product(product(range(3),repeat=2),repeat=2):
        check(2,[a,b])
    pencil = [(-1,-1,1,0),(-1,1,0,1)]
    check(4,pencil)
    for row in pencil:
        check(4,[row])
    # Puncture the four coordinate forms in turn, eliminating their free value.
    for row in [(1,1,-1), (1,1,1), (-1,1,1), (-1,-1,1)]:
        check(3,[row])
    print("128 graph systems passed including all four pencil punctures")
