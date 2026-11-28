"""Independent physical theta and square matching oracle."""
from fractions import Fraction
from itertools import combinations
from read_two_ring_nonzero import compile_nonzero
import ring_image_gram_demands as backend


def rank(rows):
    pivots={}
    for row in rows:
        v=list(map(Fraction,row))
        for j in sorted(pivots):
            c=v[j]
            v=[x-c*y for x,y in zip(v,pivots[j])]
        if any(v):
            j=next(i for i,x in enumerate(v) if x)
            pivots[j]=[x/v[j] for x in v]
    return len(pivots)


def fixture():
    edges=[]
    for i in range(4):
        edges.extend([(0,2+2*i),(2+2*i,3+2*i),(3+2*i,1)])
    edges.extend([(10,11),(11,12),(12,13),(13,10)])
    stars=[tuple(i for i,e in enumerate(edges,1) if v in e) for v in range(14)]
    rows=stars+[(-a,-b) for s in stars for a,b in combinations(s,2)]
    demands=[tuple(1+3*k for k in range(4) if k not in pair)+(13,)
             for pair in combinations(range(4),2)]
    def search(free,chosen):
        if not free:
            yield frozenset(chosen)
            return
        v=min(free)
        for i,e in enumerate(edges,1):
            if v in e and set(e)<=free:
                yield from search(free-set(e),chosen+[i])
    words=list(search(set(range(14)),[]))
    assert len(words)==8
    misses=[[int(not w.intersection(d)) for w in words] for d in demands]
    assert rank(misses)==4
    chosen=[]
    for row in misses:
        if rank(chosen+[row])>len(chosen):
            chosen.append(row)
    for deleted in [(),(1,),(2,),(13,),(1,4),(13,14)]:
        indices=[i for i,w in enumerate(words) if not w.intersection(deleted)]
        restricted=[[a[i] for i in indices] for a in misses]
        gram=[[sum(x*y for x,y in zip(a,b)) for b in restricted] for a in restricted]
        assert rank(gram)==rank(restricted)
        for i in indices:
            assert any(r[i] for r in chosen)==any(r[i] for r in misses)
    possible={w for w in words if all(w.intersection(d) for d in demands)}
    assert len(possible)==4
    parity={0,(1<<len(words))-1}
    for edge in range(1,len(edges)+1):
        column=sum((edge in w)<<i for i,w in enumerate(words))
        parity |= {p^column for p in parity}
    assert all(sum(x<<i for i,x in enumerate(a)) not in parity for a in misses)
    return edges,rows,demands,possible


def controls():
    # A finite original matching oracle for a square: misses may be constant,
    # zero, or repeated. Deleting any subset preserves the selected zero set.
    words=[{1,3},{2,4}]
    class Counter:
        def count(self,*,deleted):
            return sum(not w.intersection(deleted) for w in words)
    for demands in ([],[{1,2}],[set(),{1,2}],[{1},{3},{2},{4},{1,2}]):
        for blocked in (set(),{1},{1,2}):
            basis=backend._gram_basis(Counter(),blocked,demands)
            live=[w for w in words if not blocked&w]
            misses=[[int(not w&d) for w in live] for d in demands]
            assert len(basis)==rank(misses)
            for w in live:
                assert all(w&demands[i] for i in basis)==all(w&d for d in demands)


def main():
    controls()
    edges,rows,demands,possible=fixture()
    source=rows+demands
    raw=compile_nonzero(len(edges),source)
    args=tuple(raw[k] for k in ('n','clauses','point','k'))
    r=backend.decide(*args)
    assert (r['status'],r['count'],r['nonaffine_count'],r['affine_count'],r['gram_rank'])==(
        'nonzero',4,6,0,4)
    assert frozenset(i for i,b in enumerate(r['assignment'],1) if b) in possible
    assert r['value']==4*pow(-15,raw['expanded_edges'],3**raw['k'])%3**raw['k']
    gram,spent=r['gram_determinants'],r['determinants']
    assert 0<gram<spent
    for cap in (gram-1,spent-1):
        fail=backend.decide_source(len(edges),source,max_determinants=cap)
        assert fail['status']=='unknown' and fail['required']==cap+1 and fail['determinants']==cap
        assert ('gram_rank' in fail)==(cap>=gram)
    print('Physical theta+C4: 8 perfect matchings, 6 nonaffine misses, Gram rank 4, 4 models.')


if __name__=='__main__':
    main()
