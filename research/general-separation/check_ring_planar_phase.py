"""Original physical image controls with independent matching enumeration."""
from itertools import combinations, product
from read_two_ring_nonzero import compile_nonzero
from ring_image_planar_demands import decide


def source(edges):
    vertices={v for e in edges for v in e}
    stars=[tuple(i for i,e in enumerate(edges,1) if v in e) for v in sorted(vertices)]
    conflicts=[(-i,-j) for star in stars for i,j in combinations(star,2)]
    return stars,conflicts


def matchings(edges):
    def walk(free,chosen):
        if not free:
            yield frozenset(chosen)
            return
        v=min(free)
        for i,e in enumerate(edges,1):
            if v in e and set(e)<=free:
                yield from walk(free-set(e),chosen+[i])
    return set(walk({v for e in edges for v in e},[]))


def verify(edges,extra,expected,cap=False):
    stars,conflicts=source(edges)
    raw=compile_nonzero(len(edges),stars+conflicts+extra)
    data=[raw[key] for key in ('n','clauses','point','k')]
    good={m for m in matchings(edges) if all(m.intersection(row) for row in extra)}
    assert len(good)==expected
    if cap:
        refusal=decide(*data,max_determinants=0)
        assert refusal['reason']=='determinant_budget' and refusal['required']>0
        result=decide(*data,max_determinants=refusal['required'])
    else:
        result=decide(*data)
    assert result['count']==expected and result['status']==('nonzero' if good else 'zero')
    assert result['value']==pow(-15,raw['expanded_edges'],3**raw['k'])*expected%3**raw['k']
    if good:
        assert frozenset(i for i,b in enumerate(result['assignment'],1) if b) in good
    return data,good


def phase(n,clauses):
    deg=[sum(abs(l)==i for c in clauses for l in c) for i in range(1,n+1)]
    edges=[]
    offset=[]
    start=0
    for d in deg:
        size=4*max(1,d)
        offset.append(len(edges)+1)
        edges.extend((start+j,start+(j+1)%size) for j in range(size))
        start+=size
    starts=[s-1 for s in offset]
    edges.extend((v+1,w) for v,w in zip(starts,starts[1:]))
    use=[0]*n
    extra=[]
    for c in clauses:
        marks=[]
        for l in c:
            i=abs(l)-1
            marks.append(offset[i]+4*use[i]+int(l<0))
            use[i]+=1
        extra.append(tuple(marks))
    models={bits for bits in product((0,1),repeat=n)
            if all(any(bits[abs(l)-1]==(l>0) for l in c) for c in clauses)}
    lifted={tuple(int(j in m) for j in offset) for m in matchings(edges)
            if all(m.intersection(row) for row in extra)}
    assert lifted==models
    return verify(edges,extra,len(models))


if __name__=='__main__':
    from ring_image_cycle_phases import decide as cycle_decide
    square=[(0,1),(1,2),(2,3),(3,0)]
    verify(square,[(1,4),(4,1)],2,True)
    verify(square+[(4,5)],[],2)
    domino=[(0,1),(1,2),(3,4),(4,5),(0,3),(1,4),(2,5),(0,6),(6,7)]
    verify(domino,[],3)
    for n,cs in [(2,[]),(2,[(1,-2)]),(1,[()]),(3,[(1,-2,3)])]:
        data,good=phase(n,cs)
        result=cycle_decide(*data)
        if n==3:
            assert result['status']=='unknown' and result['reason']=='wide_phase_clause'
        else:
            assert result['status']==('nonzero' if good else 'zero')
            if good:
                assert frozenset(i for i,b in enumerate(result['assignment'],1) if b) in good
    stars,neg=source(square)
    raw=compile_nonzero(4,stars[1:]+neg)
    assert decide(*(raw[k] for k in ('n','clauses','point','k')))['reason']=='missing_star'
    print('Original planar counts 2/3/4/0, phase lifts and width-three refusal passed.')
