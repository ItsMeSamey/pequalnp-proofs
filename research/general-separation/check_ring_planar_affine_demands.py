"""Independent enumeration on actual edge coordinates."""
from itertools import combinations
from read_two_ring_nonzero import compile_nonzero
import ring_image_affine_demands as backend
from planar_character_oracle import CharacterOracle
import networkx as nx


def cycle(size,start):
    return [(start+i,start+(i+1)%size) for i in range(size)]


def oracle(edges,demands):
    stars={v:[] for e in edges for v in e}
    for i,(u,v) in enumerate(edges,1):
        stars[u].append(i)
        stars[v].append(i)
    masks=[sum(1<<(i-1) for i in s) for s in stars.values()]
    matchings=[w for w in range(1<<len(edges)) if all((s&w).bit_count()==1 for s in masks)]
    dm=[sum(1<<(i-1) for i in set(d)) for d in demands]
    labels=[tuple(int(bool(d&w)) for w in matchings) for d in dm]
    acceptable=[w for j,w in enumerate(matchings) if all(f[j] for f in labels)]
    affine=set()
    for coefficient in range(1<<len(edges)):
        word=tuple((w&coefficient).bit_count()%2 for w in matchings)
        affine.add(word)
        affine.add(tuple(1-x for x in word))
    rows=[tuple(s) for s in stars.values()]
    rows += [(-i,-j) for s in stars.values() for i,j in combinations(s,2)]
    rows.extend(demands)
    return rows,matchings,labels,affine,acceptable


def all_readouts():
    from pm_demand_affine import classify
    from planar_character_oracle import _signed_det
    assert _signed_det([[0,1],[1,0]])==-1
    assert classify(1,1,[(0,0)],[0,0])==classify(1,1,[(0,0)],[0])
    for demand in ([0,False],[0,0.0]):
        try:
            classify(1,1,[(0,0)],demand)
        except ValueError:
            continue
        raise AssertionError(demand)
    edges=cycle(4,0)+cycle(4,4)
    _,words,_,affine,_=oracle(edges,[])
    # Assign vertices to shore-local positions independently of the producer.
    pairs=[
           ((u if u%2==0 else v)//2,(v if u%2==0 else u)//2) for u,v in edges]
    root=nx.Graph()
    for i,(u,v) in enumerate(edges,1):
        root.add_edge(u,v,variable=i)
    char=CharacterOracle(root)
    for d in range(1<<len(edges)):
        ids=[i for i in range(len(edges)) if d>>i&1]
        truth=tuple(int(bool(w&d)) for w in words)
        r=classify(4,4,pairs,ids)
        assert r['base'] in words and all(r['base']^delta in words for delta in r['directions'])
        assert (r['status']=='affine')==(truth in affine)
        if r['status']=='affine':
            assert tuple(r['constant']^((w&r['mask']).bit_count()%2) for w in words)==truth
        if d<16:
            neg=[i+1 for i in ids]
            for pin,deleted in [((),()),((1,),()),((1,2),()),((1,),(7,))]:
                allowed=[w for w in words if all(w>>(i-1)&1 for i in pin)
                         and all(not(w>>(i-1)&1) for i in deleted)]
                expected=sum((-1)**((w&d).bit_count()%2) for w in allowed)
                assert char.count(negative=neg,pinned=pin,deleted=deleted)==expected
                assert char.count(negative=set(neg)^{1,4},pinned=pin,deleted=deleted)==-expected


def physical(edges,demands):
    rows,words,labels,affine,expected=oracle(edges,demands)
    raw=compile_nonzero(len(edges),rows)
    fields=tuple(raw[key] for key in ('n','clauses','point','k'))
    ans=backend.decide(*fields)
    assert ans['count']==len(expected)
    minimal=[f for d,f in zip(demands,labels)
             if not any(set(other)<set(d) for other in demands)]
    assert len(minimal)<len(demands)
    assert ans['affine_count']==sum(f in affine for f in minimal)
    assert ans['nonaffine_count']==sum(f not in affine for f in minimal)
    assert ans['affine_rank']<ans['affine_count']
    witness=sum(bit<<i for i,bit in enumerate(ans['assignment']))
    assert witness in expected and ans['value']==pow(-15,raw['expanded_edges'],3**raw['k'])*len(expected)%3**raw['k']
    spent=ans['determinants']
    assert spent>1
    for budget in (0,spent-1):
        r=backend.decide(*fields,max_determinants=budget)
        assert r['status']=='unknown' and r['reason']=='determinant_budget'
        assert r['available']==budget and r['required']>budget
    assert backend.decide(*fields,max_determinants=spent)['count']==len(expected)


if __name__=='__main__':
    all_readouts()
    physical(cycle(6,0)+cycle(4,6),[(1,3),(3,5),(2,7),(1,3,7)])
    print('All 256 physical readouts, signed gauges, affine rank saving and residual passed.')
