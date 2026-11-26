from itertools import product
from random import Random
from fibers import solve
from decode import decode

rng = Random(4205)
def check(d, edges, must):
    status, w = solve(d, edges)
    brute = any(all((row[u], row[v]) in rel for u,v,rel in edges)
                for row in product(*d.values()))
    assert (not must and status == 'unsupported') or (status == 'sat') == brute and status != 'unsupported'
    if w is not None:
        assert all((w[u],w[v]) in rel for u,v,rel in edges)
    return status

counts = {}
for _ in range(1000):
    d = dict.fromkeys(range(3), range(3))
    edges = [(u,v,{pair for pair in product(range(3),repeat=2) if rng.randrange(2)})
             for u,v in [(0,1),(1,2),(2,0)]]
    s = check(d,edges,False)
    counts[s] = counts.get(s,0)+1
print('random',counts)
counts = {}
for _ in range(100):
    labels = []
    for u in range(3):
        label = [0,0,1,1,2,2,3,3]
        rng.shuffle(label)
        labels.append(label)
    d = dict.fromkeys(range(3), range(8))
    edges = []
    cnf = []
    for u,v in [(0,1),(1,2),(2,0)]:
        p = rng.sample(range(4),4)
        rel = set()
        for a,b in product(range(8),repeat=2):
            if p[labels[u][a]] == labels[v][b]:
                rel.add((a,b))
            else:
                cnf.append([(-1 if (val>>j)&1 else 1)*(1+3*vert+j)
                            for vert,val in [(u,a),(v,b)] for j in range(3)])
        edges.append((u,v,rel))
    s = check(d,edges,True)
    c,w = decode(cnf,range(1,10))
    assert s == c
    if w:
        assert all(any(bool(w[abs(l)]) == (l>0) for l in clause) for clause in cnf)
    counts[s] = counts.get(s,0)+1
print('scrambled fibers, explicit and CNF',counts)
