"""Direct finite checks for the semantic converse. Standard library only."""
from itertools import product


def table(f):
    return sum(int(f(s)) << s for s in range(256))


def splice():
    full = (1 << 256)-1
    b, a, r, t = [table(lambda s,i=i: (s >> i) & 1) for i in range(4)]
    literals = {table(lambda s,i=i: (s >> i) & 1) ^ polarity
                for i in range(8) for polarity in (0,full)}
    first, second = r ^ (a & b), t ^ (b & r)
    def forecast(history, query):
        mask = full
        for q,y in history:
            mask &= q if y else full ^ q
        margin = 2*(mask & query).bit_count()-mask.bit_count()
        if history == [(first,1),(second,1)] and query == full ^ t:
            return 1
        return int(margin > 0 or (margin == 0 and query in literals))
    def simulate(gates,output):
        history = []
        decoded = []
        physical = full
        for wire, parents in gates:
            u,v = parents(decoded)
            query = wire ^ (u & v)
            d = 1 ^ forecast(history,query)
            history.append((query,d))
            physical &= query if d else full ^ query
            decoded.append(wire ^ (full if d == 0 else 0))
            assert (physical & decoded[-1]) == (physical & (full ^ (u & v)))
        out = output(decoded)
        assert (physical & out) == (physical & b & (full ^ a))
        return forecast(history,out),history
    f1,h1 = simulate([(r,lambda g:(b,full ^ a))],lambda g:full ^ g[0])
    f2,h2 = simulate([(r,lambda g:(a,b)),(t,lambda g:(b,g[0]))],lambda g:full ^ g[1])
    assert h1[0] != h2[0] and h2 == [(first,1),(second,1)]
    survivors = first & second
    assert [(survivors & q).bit_count() for q in (t,full ^ t)] == [48,16]
    assert 2+1+((48).bit_length()-1) == 8
    assert [forecast([],0), f1,f2,forecast([],b)] == [0,0,1,1]
    predictions = {-1: forecast([],0), 1:f1, 2:f2, 3:forecast([],b)}
    lo,hi = -1,3
    while hi-lo > 1:
        mid = (lo+hi)//2
        if predictions[mid]:
            hi = mid
        else:
            lo = mid
    assert (lo,hi) == (1,2) and not (hi & 1)


def bisect_formulas():
    # A DNF with one minterm per selected word gives every function through n=3.
    for n in range(4):
        size = 1 << n
        for mask in range(1 << size):
            terms = [tuple((x >> i) & 1 for i in range(n))
                     for x in range(size) if mask >> x & 1]
            def formula(x):
                return any(all(((x >> i)&1) == v for i,v in enumerate(term))
                           for term in terms)
            pool = list(range(size))
            errors = 0
            while True:
                def forecast(j):
                    return int(2*sum(formula(x) and x <= j for x in pool) > len(pool))
                if not forecast(size-1):
                    errors += 1
                    pool = [x for x in pool if formula(x)]
                    if errors == n+1:
                        assert not pool and mask == 0
                        break
                    assert errors <= n
                    continue
                lo,hi = -1,size-1
                while hi-lo > 1:
                    mid = (lo+hi)//2
                    if forecast(mid):
                        hi = mid
                    else:
                        lo = mid
                assert formula(hi) and hi == lo+1
                break


def segmented_count(n,anchor,queries):
    size = 1 << n
    cuts = sorted({0,size} | {t+1 for thresholds,_,_ in queries for t in thresholds})
    total = 0
    for lo,hi in zip(cuts,cuts[1:]):
        for b in range(2):
            forms = []
            for thresholds,selector,label in queries:
                mask,offset = selector(b,tuple(lo <= t for t in thresholds))
                forms.append((mask,offset ^ label))
            left = lo
            while left < hi:
                span = 1
                while left%(2*span) == 0 and left+2*span <= hi:
                    span *= 2
                equations = forms + [(1 << i,(left >> i)&1)
                                     for i in range(span.bit_length()-1,n)]
                basis = {}
                for row,rhs in equations:
                    while row and row.bit_length() in basis:
                        pivot,bit = basis[row.bit_length()]
                        row,rhs = row ^ pivot,rhs ^ bit
                    if row:
                        basis[row.bit_length()] = row,rhs
                    elif rhs:
                        break
                else:
                    total += 1 << (n-len(basis))
                    if b and left <= anchor < left+span:
                        total -= all((anchor & m).bit_count()%2 == y for m,y in forms)
                left += span
    return total


def blind():
    n,anchor = 3,3
    masks = [((0,4),lambda b,c: ((5 if c[0] else 3)^b,int(c[1]))),
             ((2,6),lambda b,c: (6 if b else 2,int(c[0]) ^ int(c[1]))),
             ((),lambda b,c:(0,b))]
    for labels in product((0,1),repeat=3):
        for end in range(4):
            qs = [(ts,f,l) for (ts,f),l in zip(masks[:end],labels)]
            native = 0
            for x,b in product(range(8),range(2)):
                if (x,b) == (anchor,1):
                    continue
                for ts,f,l in qs:
                    m,o = f(b,tuple(x <= t for t in ts))
                    if (((x&m).bit_count()%2)^o) != l:
                        break
                else:
                    native += 1
            assert segmented_count(n,anchor,qs) == native


if __name__ == '__main__':
    splice()
    bisect_formulas()
    blind()
    print('Canonical splice, explicit formulas and segmented affine counts agree.')
