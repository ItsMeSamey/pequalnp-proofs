"""Independent incremental short-path forest generation and exact SA5 replay."""
from ast import literal_eval
from fractions import Fraction
from functools import cache
from itertools import combinations, permutations, product
from pathlib import Path


def distances(adj, v):
    levels={v:0}
    work=[v]
    for u in work:
        for w in adj[u]:
            if w not in levels:
                levels[w]=levels[u]+1
                work.append(w)
    return levels


def tree_key(adj, marked):
    def rooted(v,parent):
        return (int(v in marked), tuple(sorted(rooted(w,v) for w in adj[v] if w!=parent)))
    return min(rooted(v,-1) for v in range(len(adj)))


@cache
def orbit_maps(n,edges):
    best=None
    choices=[]
    for p in permutations(range(n)):
        val=tuple(sorted((min(p[i],p[j]),max(p[i],p[j]),d) for i,j,d in edges))
        if best is None or val<best:
            best,choices=val,[]
        if val==best:
            choices.append(p)
    return best,choices


def enumerate_types():
    types=[{()}, {()}]
    previous=[(((),), frozenset({0}))]
    for n in range(2,6):
        new={}
        for adj,marked in previous:
            ds=[distances(adj,i) for i in marked]
            for v in range(len(adj)):
                near=min(d[v] for d in ds)
                for extra in range(4-near):
                    if not extra and v in marked:
                        continue
                    graph=[list(row) for row in adj]
                    last=v
                    for _ in range(extra):
                        graph[last].append(len(graph))
                        graph.append([last])
                        last=len(graph)-1
                    marks=marked|{last}
                    k=tree_key(graph,marks)
                    if k not in new:
                        new[k]=(tuple(map(tuple,graph)),marks)
        previous=list(new.values())
        found=set()
        for adj,marked in previous:
            slots=sorted(marked)
            rows=[distances(adj,v) for v in slots]
            trunc=tuple((i,j,rows[i][slots[j]]) for i,j in combinations(range(n),2) if rows[i][slots[j]]<=3)
            found.add(orbit_maps(n,trunc)[0])
        for j in range(1,n):
            for a in types[j]:
                for b in types[n-j]:
                    found.add(orbit_maps(n,a+tuple((j+u,j+v,d) for u,v,d in b))[0])
        types.append(found)
    return types


def replay(path):
    weights={}
    for line in path.read_text().splitlines():
        key,number=line.rsplit(" ",1)
        key=literal_eval(key)
        assert key not in weights
        weights[key]=Fraction(number)
    assert min(weights.values())>=0 and weights[0,(),()]==1
    typ=enumerate_types()
    assert {(n,g) for n,gs in enumerate(typ) for g in gs}=={(n,g) for n,g,p in weights}
    touched=set()
    @cache
    def lookup(n,edges,parts):
        best,choices=orbit_maps(n,edges)
        key=(n,best,min(tuple(sorted(tuple(sorted(p[i] for i in part)) for part in parts)) for p in choices))
        touched.add(key)
        return weights[key]
    def word(n,edges,cols):
        if any(d==1 and cols[i]==cols[j] for i,j,d in edges):
            return 0
        parts=tuple(sorted(tuple(i for i,v in enumerate(cols) if v==c) for c in set(cols)))
        return lookup(n,edges,parts)
    checks=0
    for n,gs in enumerate(typ):
        for g in gs:
            for v in range(n):
                rest=tuple((i-(i>v),j-(j>v),d) for i,j,d in g if v not in (i,j))
                for c in product(range(3),repeat=n-1):
                    expected=word(n-1,rest,c)
                    actual=sum(word(n,g,c[:v]+(t,)+c[v:]) for t in range(3))
                    assert actual==expected
                    checks+=1
    assert touched==set(weights)
    print([len(gs) for gs in typ],len(weights),"orbit weights and",checks,"exact marginals passed")


if __name__=="__main__":
    replay(Path(__file__).with_name("colour-sa5-r3-orbits.txt"))
