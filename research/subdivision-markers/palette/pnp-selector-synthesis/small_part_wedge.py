"""Unrestricted deterministic cut-pair generation with a physical scalar oracle."""
from itertools import combinations
from five_terminal_dual import component_lifts
from planar_moment_certificate import CertifiedDual


def generators(n,edges,first_space):
    edges=tuple(tuple(e) for e in edges);dual=CertifiedDual(n,edges)
    adj=[{v for v,_ in neighbors if v!=u} for u,neighbors in enumerate(dual.graph)]
    def components(vertices):
        unseen=set(vertices)
        while unseen:
            root=min(unseen);unseen.remove(root);part=[root]
            for u in part:
                for v in adj[u]&unseen:unseen.remove(v);part.append(v)
            yield part
    def neutral(vertices):
        acc=0
        for v in vertices:acc^=dual.charge[v]
        return not acc
    for size in range(1,n//3+1):
        for selected in combinations(range(n),size):
            if not neutral(selected) or len(next(components(selected)))!=size:continue
            parts=list(components(set(range(n))-set(selected)))
            if any(not neutral(part) for part in parts):continue
            A=sum(1<<v for v in selected);a=dual.cut(A)
            for part in parts:
                sites=set(part);es=[(u,v) for u,v,_ in edges if u in sites and v in sites]
                for y in component_lifts(part,es,dual.charge,first_space):
                    b=dual.cut(y)
                    if not dual.compatible(A,y):raise AssertionError("invalid original pair")
                    if a and b and a!=b:yield a,b
