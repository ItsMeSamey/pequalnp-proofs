"""End-to-end decision peeling on clique bags glued along graphical triangles."""
from collections import Counter
from itertools import combinations, product
from pathlib import Path
from random import Random
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'kernel'))
from kernel import Basis, certificate


def vertex(i):
    return 0 if i == 0 else 1 << (i-1)


def parity(x):
    return x.bit_count() & 1


def canon(rows):
    """A forbidden flat: None is empty, () forbids the entire space."""
    basis = {}
    for m, b in rows:
        while m and (p := m.bit_length()-1) in basis:
            v,c = basis[p]
            m,b = m^v,b^c
        if m:
            basis[m.bit_length()-1] = m,b
        elif b:
            return None
    return tuple(basis.values())


def budget(flats, observed):
    basis = Basis()
    for r in observed:
        basis.add(r)
    pairs = []
    for f in flats:
        normals = [basis.reduce(m)[0] for m,_ in f]
        if len(normals) == 1:
            normals *= 2
        pairs.append(normals)
    selected,_ = certificate(pairs)
    return len(flats)-len(selected)


def accepts(flats, w):
    return all(any(parity(m&w) != c for m,c in f) for f in flats)


def local(bag, flats, tests=()):
    for values in product(range(2), repeat=len(bag)-1):
        w = sum(vertex(i)*v for i,v in zip(sorted(bag-{0}),values))
        if all(parity(w&m)==c for m,c in tests) and accepts(flats,w):
            return True
    return False


def gluing_graph(bags, parents):
    graph = [set() for _ in bags]
    for j,p in enumerate(parents,1):
        assert len(bags[j] & bags[p]) == 3
        graph[p].add(j)
        graph[j].add(p)
    return graph


def peel(bags, parents, constraints, pins, log, rng):
    # All bags contain anchor 0. Fixing a real coordinate contracts its anchor edge.
    masks = sum(vertex(i) for i in pins)
    values = sum(vertex(i)*b for i,b in pins.items())
    files = []
    for rows in constraints:
        kept = []
        for f in rows:
            restricted = canon([(m & ~masks,c ^ parity(m&values)) for m,c in f])
            if restricted == ():
                return False
            if restricted is not None:
                kept.append(restricted)
        files.append(kept)
    graph = gluing_graph(bags, parents)
    active = set(range(len(bags)))
    total = budget([f for part in files for f in part], ())
    assert total <= 1
    while len(active)>1:
        i = rng.choice(sorted(j for j in active if len(graph[j]) == 1))
        j, = graph[i]
        joint = sorted((bags[i] & bags[j])-{0}-pins.keys())
        K = [vertex(v) for v in joint]
        k = len(K)
        d = budget(files[i],K)
        def test(eqs):
            assert budget(files[i],[m for m,_ in eqs]) <= 1
            return local(bags[i],files[i],eqs)
        out = []
        if d <= 1:
            F = {bs for bs in product(range(2),repeat=k) if test(tuple(zip(K,bs)))}
            log['exact'] += 1
            if not F:
                return False
            if len(F) == 1 and k:
                bs, = F
                out = [((m,1^b),) for m,b in zip(K,bs)]
            elif k==2 and len(F)==2:
                a,b = K
                for direction,m in ((1,a),(2,b),(3,a^b)):
                    choices = {parity(direction & (x|(y<<1))) for x,y in F}
                    if len(choices)==1:
                        out = [((m,1^choices.pop()),)]
                        break
                assert out
            elif k==2 and len(F)==3:
                excluded, = set(product(range(2),repeat=2))-F
                out = [tuple(zip(K,excluded))]
        elif d == k+1:
            log['outside-full'] += 1
            return test(())
        else:
            assert k==2 and d==2
            if not test(()):
                return False
            a,b = K
            fixed = []
            for m in (a,b,a^b):
                if budget(files[i],[m]) <= 1:
                    ok0,ok1 = (test(((m,c),)) for c in (0,1))
                    assert ok0 or ok1
                    if ok0 != ok1:
                        fixed.append((m,int(ok1)))
            if fixed:
                # If all three are fixed, any two of the distinct rows suffice.
                out = [((m,1^c),) for m,c in fixed[:2]]
                log['exact-fixed'] += 1
            else:
                log['relaxed'] += 1
        files[i] = []
        files[j].extend(out)
        active.remove(i)
        graph[j].remove(i)
        updated = budget([f for part in files for f in part], ())
        assert updated <= total
        total = updated
    last, = active
    log['final'] += 1
    return local(bags[last],files[last])


def graph_boundaries(rng, count):
    bags = [{0,1,2,3,4}]
    parents = []
    for i in range(1,count):
        p = rng.randrange(i)
        a,b = rng.sample(sorted(bags[p]-{0}),2)
        bags.append({0,a,b,4+i})
        parents.append(p)
    return bags,parents


def brute(bags,files,pins):
    highest = max(max(b) for b in bags)
    for w in range(1 << highest):
        if all(parity(w&vertex(i))==b for i,b in pins.items()) and all(accepts(rows,w) for rows in files):
            return w
    return None


def random_flat(bag,rng):
    if rng.randrange(3):
        a,b,c=rng.sample(sorted(bag),3)
        return ((vertex(a)^vertex(b),rng.randrange(2)),(vertex(a)^vertex(c),rng.randrange(2)))
    a,b=rng.sample(sorted(bag),2)
    return ((vertex(a)^vertex(b),rng.randrange(2)),)


def run():
    rng=Random(292101)
    log=Counter()
    # Child-private coordinates genuinely enter two of the three constraints.
    bags=[{0,1,2,3,4},{0,1,2,5},{0,3,4,6}]
    parents=[0,0]
    def three(a,b,y):
        A,B,Y=map(vertex,(a,b,y))
        return [((A,0),(Y,0)),((B,0),(Y,1)),((A,0),(B,0))]
    files=[[((vertex(1),1),)],three(1,2,5),three(3,4,6)]
    assert brute(bags,files,{}) is not None and not all(accepts(rows,0) for rows in files)
    # Fix an order peeling both satellites into the central clique.
    class SatellitesFirst:
        def choice(self,items):
            return max(items)
    fixed=Counter()
    assert peel(bags,parents,files,{},fixed,SatellitesFirst())
    assert fixed['relaxed']==2 and fixed['final']==1
    for turn in range(400):
        bags,parents=graph_boundaries(rng,rng.randrange(3,7))
        while True:
            files=[[random_flat(b,rng) for _ in range(rng.randrange(4))] for b in bags]
            if budget([f for row in files for f in row],())<=1:
                break
        expected=brute(bags,files,{}) is not None
        for _ in range(2):
            assert peel(bags,parents,files,{},log,rng)==expected
    # Native guarded pivots and a single original marker pin. For each surviving
    # clause its pivot is unique. Trying additional zero pivots preserves δ<=1.
    recovered=0
    for trial in range(250):
        bags,parents=graph_boundaries(rng,rng.randrange(3,7))
        highest=max(max(b) for b in bags)
        files=[[] for _ in bags]
        for v in range(1,highest+1):
            i=rng.choice([i for i,b in enumerate(bags) if v in b])
            u=rng.choice(sorted(bags[i]-{v}))
            f=canon(((vertex(v),1),(vertex(u),rng.randrange(2))))
            if f is not None:
                files[i].append(f)
        marker=rng.randrange(1,highest+1)
        pins={marker:rng.randrange(2)}
        expected=brute(bags,files,pins)
        ok=peel(bags,parents,files,pins,log,rng)
        assert ok == (expected is not None)
        if not ok:
            continue
        for v in range(1,highest+1):
            if v not in pins and peel(bags,parents,files,{**pins,v:0},log,rng):
                pins[v]=0
        witness=sum(vertex(v)*pins.get(v,1) for v in range(1,highest+1))
        assert all(accepts(row,witness) for row in files)
        recovered+=1
    print("Two successive non-full relaxed deletions:",dict(fixed))
    print("400 general instances, two independently chosen peeling orders each; 250 native marker instances;",recovered,"native witnesses")
    print("Observed transitions:",dict(log))

if __name__ == '__main__':
    run()
