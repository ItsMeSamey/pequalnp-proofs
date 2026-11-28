"""Independent exhaustive relaxed and physical orientation oracles."""
from itertools import combinations, product
from random import Random
from joint_choice import solve


def check(types,links=(),units=(),extra=(),caps=False):
    n = 2*len(types)+1
    guard = n-1
    gates, ports, tables = [], [], []
    def add(a,b):
        gates.append((a,b))
        return n+len(gates)-1
    for i,kind in enumerate(types):
        x,p = 2*i,2*i+1
        o = add(x,p)
        if kind == 3:
            e = add(o,p)
            t = add(e,add(p,p))
            ports.append((o,e,t))
            rows = [(int(not (a and b)),int(not ((not (a and b)) and b)),b)
                    for a,b in product(range(2),repeat=2)]
        else:
            ports.append((x,p,o))
            rows = [(a,b,int(not (a and b))) for a,b in product(range(2),repeat=2)]
        tables.append(list(dict.fromkeys(rows)))
    ids = [v for vs in ports for v in vs]
    clauses = [(v+1,guard+1) for v in ids]+[(guard+1,)]
    clauses.extend(tuple((ids[abs(l)-1]+1)*(1 if l>0 else -1) for l in row) for row in extra)
    eqs = [(ids[i],ids[j],d) for i,j,d in links]
    pins = [(ids[i],b) for i,b in units]
    def exterior(w):
        return (all(any(w[abs(l)-1] == (l>0) for l in row) for row in clauses)
                and all(w[a]^w[b] == d for a,b,d in eqs)
                and all(w[a] == b for a,b in pins))
    def hull(word, table):
        return all(any((a[i],a[j]) == (word[i],word[j]) for a in table)
                   for i,j in combinations(range(3),2))
    domains = [[w for w in product(range(2),repeat=3) if hull(w,t)] for t in tables]
    relaxed = []
    for assign in product(*domains):
        w = dict(zip(ids,(b for triple in assign for b in triple)))
        w[guard] = 1
        if exterior(w):
            relaxed.append(assign)
    def extend(constraints,assign):
        return all(assign[i] in (tables[i][:2] if s==0 else tables[i][2:])
                   for i,s in constraints)
    candidates, real = [], []
    for sides in product(range(2),repeat=len(types)):
        ix = list(enumerate(sides))
        if all(any(extend(sub,a) for a in relaxed)
               for k in range(min(2,len(ix))+1) for sub in combinations(ix,k)):
            candidates.append(sides)
        if any(extend(ix,a) for a in relaxed):
            real.append(sides)
    def direct(raw):
        w = list(raw)
        for a,b in gates:
            w.append(int(not (w[a] and w[b])))
        return exterior(w)
    feasible = any(direct(raw) for raw in product(range(2),repeat=n))
    assert feasible == bool(real)
    opts = dict(clauses=clauses,equalities=eqs,pins=pins)
    state,stats,raw = solve(n,gates,**opts)
    assert stats['bad'] == len(types)
    learned = stats['selector_clauses']
    def passed(s):
        return all(any(s[abs(l)-1] == (l>0) for l in row) for row in learned)
    assert [s for s in product(range(2),repeat=len(types)) if passed(s)] == candidates
    tested = candidates.index(real[0])+1 if real else len(candidates)
    assert stats['tested'] == tested
    assert state == ('sat' if feasible else 'unsat')
    assert (len(raw)==n and direct(raw)) if feasible else raw is None
    if caps:
        for limit in sorted({0,max(0,tested-1),tested}):
            result, bounded, answer = solve(n,gates,max_models=limit,**opts)
            assert result == ('skip' if limit < tested else state)
            assert bounded['tested'] == min(limit,tested)
            assert direct(answer) if result == 'sat' else answer is None
        if types:
            assert solve(n,gates,max_bad=len(types)-1,**opts)[0] == 'skip'


def main():
    check((),caps=True)
    check((3,),units=[(0,1),(1,1),(2,1)],caps=True)
    check((3,),units=[(0,0),(1,0)],caps=True)
    check((3,),units=[(2,1)],caps=True)
    check((3,3),links=[(i,i+3,1) for i in range(3)],caps=True)
    check((3,3),links=[(0,3,0),(3,0,0),(0,3,0)],caps=True)
    check((3,4,3),links=[(1,3,1),(4,7,0),(4,7,0)],extra=[(-3,8),(5,-7)],caps=True)
    check((4,),extra=[()],caps=True)
    rng = Random(11992)
    for _ in range(30):
        types = tuple(rng.choice((3,4)) for _ in range(rng.randrange(1,4)))
        k = 3*len(types)
        eqs = [(*rng.sample(range(k),2),rng.randrange(2)) for _ in range(3)]
        pins = [(rng.randrange(k),rng.randrange(2)) for _ in range(rng.randrange(3))]
        check(types,eqs,pins)
    print('38 original NAND charts, relaxed unary/pair projection, full orientations and caps')


if __name__ == '__main__':
    main()
