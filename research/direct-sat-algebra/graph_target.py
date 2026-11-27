"""Reduce a target on a certified graph to ordinary three-colouring.

A quotient self-loop proves UNSAT. A bipartite quotient supplies a checked
ambient witness. Other quotients return UNKNOWN and may still be colourable.
"""
from dataclasses import dataclass
from itertools import combinations
from graph_derivation import Graph, recover
from quadratic_target import apply_basis, insert, reduce_vector, interpolate


@dataclass(frozen=True)
class Quotient:
    owner: tuple  # -1 denotes an inactive vertex
    size: int
    inequalities: tuple  # self-loops retained
    target: int
    edge_bits: int


def quotient(graph,target):
    rows = {}
    for j,(_,_,e) in enumerate(graph.edges):
        insert(e,1<<j,rows)
    remainder,goal = reduce_vector(graph.output_offset ^ target,rows)
    if target<0 or remainder:
        raise ValueError("target outside recovered output coordinates")
    n = len(graph.planes)
    active = set()
    zeros = [[] for _ in range(n)]
    ones = []
    for j,(u,v,_) in enumerate(graph.edges):
        if goal>>j&1:
            active.update((u,v))
            ones.append((u,v))
        else:
            zeros[u].append(v)
            zeros[v].append(u)
    owner = [-1]*n
    size = 0
    for u in sorted(active):
        if owner[u]>=0:
            continue
        owner[u] = size
        stack = [u]
        while stack:
            for v in zeros[stack.pop()]:
                if v in active and owner[v]<0:
                    owner[v]=size
                    stack.append(v)
        size += 1
    edges = tuple(sorted({tuple(sorted((owner[u],owner[v]))) for u,v in ones}))
    return Quotient(tuple(owner),size,edges,target,goal)


def lift(graph,q,colours):
    """Lift any supplied proper three-colouring (integer codes 1, 2, 3)."""
    if (len(colours)!=q.size or any(v not in (1,2,3) for v in colours)
            or any(colours[u]==colours[v] for u,v in q.inequalities)):
        raise ValueError("invalid quotient colouring")
    codes = [colours[k] if k>=0 else 0 for k in q.owner]
    witness = graph.shift
    for code,plane in zip(codes,graph.planes):
        witness ^= apply_basis(plane,code)
    out = graph.output_offset
    for u,v,e in graph.edges:
        if codes[u] and codes[v] and codes[u]!=codes[v]:
            out ^= e
    if out!=q.target:
        raise ArithmeticError("lifted colouring fails target")
    return witness


def probe(graph,target):
    """Return (status, packed ambient witness or None, quotient)."""
    q = quotient(graph,target)
    adj = [[] for _ in range(q.size)]
    for u,v in q.inequalities:
        if u==v:
            return "UNSAT",None,q
        adj[u].append(v)
        adj[v].append(u)
    colours = [0]*q.size
    for i in range(q.size):
        if colours[i]:
            continue
        colours[i] = 1
        stack = [i]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if colours[v]==colours[u]:
                    return "UNKNOWN",None,q
                if not colours[v]:
                    colours[v] = 3-colours[u]
                    stack.append(v)
    return "SAT",lift(graph,q,colours),q


def self_test():
    from itertools import product
    from random import Random
    rng = Random(678)
    def raw(edges,x):
        codes = [(x>>(2*i))&3 for i in range(x.bit_length()//2+1)]
        out = 0
        for j,(u,v) in enumerate(edges):
            a = codes[u] if u<len(codes) else 0
            b = codes[v] if v<len(codes) else 0
            out |= int(bool(a and b and a!=b))<<j
        return out
    checks = 0
    statuses = set()
    for n in range(5):
        possible = list(combinations(range(n),2))
        for subset in range(1<<len(possible)):
            edges = [e for j,e in enumerate(possible) if subset>>j&1]
            graph = Graph(tuple((1<<(2*i),2<<(2*i)) for i in range(n)),
                          tuple((u,v,1<<j) for j,(u,v) in enumerate(edges)),0,0)
            image = {raw(edges,x) for x in range(1<<(2*n))}
            for target in range(1<<len(edges)):
                st,w,q = probe(graph,target)
                statuses.add(st)
                colouring = next((c for c in product((1,2,3),repeat=q.size)
                                  if all(c[u]!=c[v] for u,v in q.inequalities)),None)
                assert (colouring is not None)==(target in image)
                if colouring is not None:
                    assert raw(edges,lift(graph,q,colouring))==target
                assert st!="UNSAT" or target not in image
                assert st!="SAT" or raw(edges,w)==target
                checks += 1
    assert statuses=={"UNKNOWN","SAT","UNSAT"}
    from quadratic_centroid import independent
    def random_basis(d):
        basis=()
        while len(basis)<d:
            basis=independent((*basis,rng.randrange(1,1<<d)))
        return basis
    edges=[(i,(i+1)%5) for i in range(5)]
    ib,ob=random_basis(10),random_basis(5)
    def hidden(x):
        return apply_basis(ob,raw(edges,apply_basis(ib,x^553))) ^ 19
    graph=recover(10,5,*interpolate(hidden,10))
    target=apply_basis(ob,0b00101)^19
    status,w,_=probe(graph,target)
    assert status=="SAT" and hidden(w)==target
    print(f"{checks} graph/target pairs and dense translated mixed target passed")


if __name__=="__main__":
    self_test()
