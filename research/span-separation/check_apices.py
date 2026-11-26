"""Exercise parity-preserving recolorings and the rooted trace encoding."""
from itertools import product
from functools import reduce
from operator import xor
from random import Random


def components(vertices, graph):
    left = set(vertices)
    out = []
    while left:
        block = {left.pop()}
        stack = list(block)
        while stack:
            nxt = graph[stack.pop()] & left
            left -= nxt
            block |= nxt
            stack.extend(nxt)
        out.append(block)
    return out


def add_edge(graph, a, b):
    graph[a].add(b)
    graph[b].add(a)


def compact(rng, n=60, r=2):
    # The two apices keep respectively the red and blue base vertices connected.
    graph = [set() for _ in range(n + 2)]
    for i in range(n):
        if i:
            add_edge(graph, i, i-1)
        add_edge(graph, i, n + i % 2)
    add_edge(graph, n, n + 1)
    color = [i % 2 for i in range(n)] + [0, 1]
    labels = [rng.randrange(1 << r) for _ in graph]
    pins = set(rng.sample(range(n), 3))
    def values():
        return tuple(reduce(xor, (v for v,i in zip(labels,color) if i==j), 0) for j in (0,1))
    initial = values()
    steps = 0
    while True:
        islands = [b for i in (0,1) for b in
                   components((v for v in range(n) if color[v]==i), graph)]
        adj = {i: [j for j, other in enumerate(islands) if j!=i and
                   any(graph[v] & other for v in block)] for i,block in enumerate(islands)}
        free = [i for i, block in enumerate(islands) if not pins & block]
        if len(free) <= 8*r:
            break
        edges = [(i, adj[i][0]) for i in free]
        fixed = {}
        def score():
            return sum(1 << ((a in fixed) + (b in fixed)) for a,b in edges
                       if fixed.get(a,0)==0 and fixed.get(b,1)==1)
        for i in range(len(islands)):
            fixed[i]=0
            s0=score()
            fixed[i]=1
            if score()<s0:
                fixed[i]=0
        donors = [(a,b) for a,b in edges if not fixed[a] and fixed[b]]
        assert len(donors)>2*r
        basis = {}
        for j,(a,b) in enumerate(donors):
            delta = reduce(xor, (labels[v] for v in islands[a]), 0)
            val, witness = delta | (delta << r), 1 << j
            while val and val.bit_length() in basis:
                prev, opts=basis[val.bit_length()]
                val ^= prev
                witness ^= opts
            if val:
                basis[val.bit_length()] = val, witness
                continue
            for i,(src,dst) in enumerate(donors):
                if witness >> i & 1:
                    for v in islands[src]:
                        color[v] = color[next(iter(islands[dst]))]
            break
        else:
            raise AssertionError("dependent transfers expected")
        assert values() == initial and all(color[v]==v%2 for v in pins)
        assert all(len(components((v for v in range(n+2) if color[v]==j),graph))==1 for j in (0,1))
        steps += 1
    return steps


def check_root_tags(rng):
    n, s = rng.randrange(3,8), rng.randrange(2,4)
    graph = [set() for _ in range(n)]
    for i in range(1,n):
        add_edge(graph,i,rng.randrange(i))
    for i in range(n):
        for j in range(i):
            if rng.randrange(4)==0:
                add_edge(graph,i,j)
    labels=[rng.randrange(4) for _ in range(n)]
    labels[0] ^= reduce(xor,labels,0)
    target=[rng.randrange(4) for _ in range(s)]
    target[0]=reduce(xor,target[1:],0)
    pin,owner=rng.randrange(n),rng.randrange(s)
    tagged=labels.copy()
    for i in range(1,s):
        tagged[0] ^= 1 << (i+1)
        tagged[i] ^= 1 << (i+1)
    tagged[pin] ^= 1 << (s+1)
    tagged[owner] ^= 1 << (s+1)
    H={0}
    for i in range(1,s):
        x=target[i] ^ (1 << (i+1))
        H |= {y^x for y in H}
    original = encoded = False
    for coloring in product(range(s),repeat=n):
        parts=[[v for v in range(n) if coloring[v]==i] for i in range(s)]
        if not all(len(components(p,graph))==1 for p in parts):
            continue
        sums=[reduce(xor,(labels[v] for v in p),0) for p in parts]
        original |= list(coloring[:s])==list(range(s)) and coloring[pin]==owner and sums==target
        subspace={0}
        for p in parts:
            x=reduce(xor,(tagged[v] for v in p),0)
            subspace |= {y^x for y in subspace}
        encoded |= subspace==H
    assert original == encoded


if __name__=="__main__":
    rng=Random(89001)
    steps=sum(compact(rng) for _ in range(50))
    for _ in range(120):
        check_root_tags(rng)
    print(f"{steps} safe island reductions and 120 rooted partition-to-trace comparisons passed")
