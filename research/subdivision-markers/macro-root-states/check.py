"""Direct truth tables, cut-rank identity and large clique-sum controls."""
from itertools import combinations
from random import Random
from macro import small_port, spectrum
from solve import augment, canonical, functional, image, intersection


def brute(cols, gains, cogains):
    n = len(cols)
    cuts = {sum(((v & phi).bit_count() % 2) << i for i,v in enumerate(cols))
            for phi in range(1 << max((v.bit_length() for v in cols), default=0))}
    cycles = [c for c in range(1 << n) if not image(cols,c)]
    scores = {image(gains,c) ^ image(cogains,d) for c in cycles for d in cuts if not c & d}
    return scores, cycles, cuts


def verify_local(rng):
    count = 0
    for _ in range(100):
        cols = tuple(rng.randrange(32) for _ in range(rng.randrange(1,10)))
        basis = canonical(cols)
        d = min(len(basis),rng.randrange(3))
        port = canonical(rng.sample(basis,d))
        table = small_port(list(enumerate(cols)),port)
        oracle = {f:set() for f in range(1<<d)}
        for mask in range(1<<len(cols)):
            u = image(cols,mask)
            selected = tuple(v for i,v in enumerate(cols) if mask >> i & 1)
            for f in oracle:
                if u in {image(port,j) for j in range(1<<d)} and functional(port+selected,f) is not None:
                    oracle[f].add(u)
        for f, targets in oracle.items():
            assert set(table[f]) == targets
            for u, mask in table[f].items():
                selected = tuple(v for i,v in enumerate(cols) if mask >> i & 1)
                assert image(cols, mask) == u and functional(port+selected,f) is not None
        count += 1
    return count


def verify_cuts(rng):
    comparisons = 0
    macro_runs = 0
    for z in range(150):
        n = rng.randrange(2,9)
        cols = [rng.randrange(1<<rng.randrange(1,5)) for _ in range(n)]
        t = 1 + z % 3
        gains = [rng.randrange(1<<t) for _ in cols]
        cogains = [rng.randrange(1<<t) for _ in cols]
        spectrum0, cycles, cuts = brute(cols,gains,cogains)
        ordinary, roots = augment(cols,gains,cogains,t)
        for A in (rng.randrange(1<<n),(1<<(n//2))-1):
            inside = [i for i in range(n) if A>>i & 1]
            out = [i for i in range(n) if not A>>i & 1]
            rank = lambda group: len(canonical(group))
            native = rank(cols[i] for i in inside)+rank(cols[i] for i in out)-rank(cols)
            primal_rank = rank(image(gains,c) for c in cycles if not c & ~A)
            dual_rank = rank(image(cogains,d) for d in cuts if not d & ~A)
            U = intersection(canonical(ordinary[i] for i in inside),canonical(roots+tuple(ordinary[i] for i in out)))
            assert len(U) == native+primal_rank+dual_rank
            comparisons += 1
        # Coalesce adjacent pairs when allowable. Singletons always qualify.
        blocks = []
        i = 0
        while i < n:
            candidate = list(range(i,min(n,i+2)))
            outside = roots + tuple(v for j,v in enumerate(ordinary) if j not in candidate)
            if len(intersection(canonical(ordinary[j] for j in candidate),canonical(outside))) > 2:
                candidate = [i]
            blocks.append(candidate)
            i += len(candidate)
        def tree(lo, hi):
            if hi == lo+1:
                return lo
            mid = (lo+hi)//2
            return tree(lo,mid),tree(mid,hi)
        found,_ = spectrum(cols,gains,cogains,t,blocks,tree(0,len(blocks)))
        assert set(found) == spectrum0
        assert all(c in cycles and d in cuts and not c & d for c,d in found.values())
        macro_runs += 1
    return comparisons,macro_runs


def cliques(m, same):
    edges = list(combinations(range(m),2))
    cols = tuple((1<<a)|(1<<b) for a,b in edges)
    n = len(cols)
    pin = edges.index((0,1))
    cut = edges.index((0,3))
    gain = [int(i==pin) for i in range(n)]
    cogain = [2*int(i==cut) for i in range(n)]
    second = [8*int(i==(pin if same else cut)) for i in range(n)]
    base = cols+tuple(v<<m for v in cols)
    found,w = spectrum(base,gain+[v<<2 for v in gain],cogain+second,4,
                       [range(n), range(n,2*n)], (0,1))
    assert w == 4
    assert set(found) == (set(range(12)) if same else set(range(16)))
    return len(found)


if __name__ == "__main__":
    rng=Random(46152)
    print("local truth tables",verify_local(rng))
    print("cut-rank identities and whole-graph spectra",verify_cuts(rng))
    print("clique controls (m, full, one incompatible pin)",[(m,cliques(m,False),cliques(m,True)) for m in (5,10,18)])
