"""Check GF(2) pivot-list subcubes for signed long-clause satisfaction."""
from itertools import combinations,product
from math import comb
from random import Random


def columns(n,clauses):
    return [[sum(1<<j for j,(m,b) in enumerate(clauses)
                 if m>>i&1 and (b>>i&1)!=v)
             for v in (0,1)] for i in range(n)]


def extend(span,v):
    return span | {w^v for w in span}


def partition(n,clauses):
    cols = columns(n,clauses)
    total_span = {0}
    for pair in cols:
        for v in pair:
            total_span = extend(total_span,v)
    k = len(total_span).bit_length()-1
    seen = {}
    lists = kept = 0
    accepted_counts = [0]*3
    cores = [lambda x:True,lambda x:False,lambda x:x%3==1]
    for size in range(min(n,k)+1):
        for piv in combinations(range(n),size):
            for values in product((0,1),repeat=size):
                lists += 1
                chosen = dict(zip(piv,values))
                span = {0}
                allowed = []
                for i,pair in enumerate(cols):
                    if i in chosen:
                        v = chosen[i]
                        if pair[v] in span:
                            break
                        span = extend(span,pair[v])
                        allowed.append([v])
                    else:
                        options = [v for v in (0,1) if pair[v] in span]
                        if not options:
                            break
                        allowed.append(options)
                else:
                    kept += 1
                    # Which rows are nonzero somewhere in this subspace?
                    support = sum(1<<j for j in range(len(clauses))
                                  if any(w>>j&1 for w in span))
                    opts = list(product(*allowed))
                    for assignment in opts:
                        x = sum(v<<i for i,v in enumerate(assignment))
                        assert x not in seen
                        seen[x] = support
                    if support == (1<<len(clauses))-1:
                        for t,core in enumerate(cores):
                            accepted_counts[t] += sum(core(sum(v<<i for i,v in enumerate(a))) for a in opts)
    assert lists == sum(comb(n,j)*2**j for j in range(min(n,k)+1))
    assert len(seen)==2**n and kept<=min(lists,2**n)
    ok = []
    for x in range(2**n):
        truth = sum(1<<j for j,(m,b) in enumerate(clauses) if x&m!=b)
        assert truth==seen[x]
        if truth==(1<<len(clauses))-1:
            ok.append(x)
    assert accepted_counts == [sum(core(x) for x in ok) for core in cores]
    return kept, lists


if __name__=='__main__':
    cases = cubes = candidates = 0
    for n,cap in ((0,1),(1,3),(2,9),(3,3),(5,None)):
        universe = [(m,b) for m,b in product(range(2**n),repeat=2) if b&m==b]
        if cap is None:
            rng = Random(7634)
            families = [rng.choices(universe,k=rng.randrange(16)) for _ in range(150)]
        else:
            families = (seq for k in range(cap+1) for seq in combinations(universe,k))
        for family in families:
            retained, examined = partition(n,family)
            cubes += retained
            candidates += examined
            cases += 1
    print(cases,'CNFs;',candidates,'candidate lists;',cubes,'nonempty partition cells')
