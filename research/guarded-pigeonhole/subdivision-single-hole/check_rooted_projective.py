from itertools import combinations
from time import monotonic
import networkx as nx
from rooted_projective import close,replay,table,start,insert,deductions


def flower(k):
    g=nx.Graph()
    for i in range(k):
        for j in (1,2,3):g.add_edge((i,0),(i,j))
        g.add_edge((i,1),((i+1)%k,1))
        for j in (2,3):g.add_edge((i,j),((i+1)%k,j if i+1<k else 5-j))
    return g


def data(g):
    edges=sorted(tuple(sorted(e)) for e in g.edges)
    ids={e:i for i,e in enumerate(edges)}
    P=[0]*len(edges)
    cycles=nx.cycle_basis(g)
    for k,c in enumerate(cycles):
        for a,b in zip(c,c[1:]+c[:1]):P[ids[tuple(sorted((a,b)))]]|=1<<k
    p=sorted(set(P))
    root=next((a,b) for a,b in combinations(p,2) if a^b in p)
    return len(cycles),p,root


def test(g,limit=None):
    d,p,root=data(g)
    t=monotonic()
    state,log,r,pts,k,passes=close(d,p,root,seconds=limit)
    assert replay(d,p,root,log)
    print(len(g),d,k,state,'affine_dimension',2*d-r,'points',pts,'records',len(log),'passes',passes,'seconds',round(monotonic()-t,2),flush=True)
    if state=='UNSAT':
        assert log[-1][1] is None
    return state,log,d,p,root


if __name__=='__main__':
    st,log,d,p,rt=test(nx.petersen_graph())
    assert st=='UNSAT' and not replay(d,p,rt,[(log[-1][0],None)])
    st,log,d,p,rt=test(nx.cubical_graph())
    assert st=='STABLE'
    pts,sys=start(d,p,rt)
    for B,(eq,ps) in log:
        for v,b in eq:assert insert(sys,v,b)
        pts.update(ps)
    maps=[f for f in range(1<<(2*d)) if all((v&f).bit_count()%2==b for v,b in sys.values())]
    def legal(f):
        return all((f&v).bit_count()%2 or ((f>>d)&v).bit_count()%2 for v in p)
    _,initial=start(d,p,rt)
    true={f for f in range(1<<(2*d)) if legal(f) and all((f&v).bit_count()%2==b for v,b in initial.values())}
    assert len(true)==4 and true=={f for f in maps if legal(f)}
    print("Cube affine survivors",len(maps),"true rooted assignments",len(true),flush=True)
    test(flower(5),90)
    from random import Random
    from rooted_projective import basis,span,replay_unsat
    rng=Random(902)
    for _ in range(200):
        d=rng.randrange(2,6)
        f0=rng.getrandbits(2*d)
        system={}
        for j in range(rng.randrange(2*d+1)):
            v=rng.getrandbits(2*d)
            assert insert(system,v,(v&f0).bit_count()%2)
        B=basis(rng.getrandbits(d) for j in range(rng.randrange(5)))
        vals=span(B)
        pts={v for v in vals if rng.randrange(3)==0}
        legal,possible,_,forms=table(B,d,pts,system)
        brute=set()
        good=set()
        for f in range(1<<(2*d)):
            if any((f&v).bit_count()%2!=b for v,b in system.values()):continue
            m=sum(((v&f).bit_count()%2)<<i for i,v in enumerate(forms))
            brute.add(m)
            if all((f&v).bit_count()%2 or ((f>>d)&v).bit_count()%2 for v in pts):good.add(m)
        assert possible==sum(1<<v for v in brute) and legal==sum(1<<v for v in good)
    assert not replay_unsat(d,p,rt,[])
    print('200 projected Gaussian tables matched brute force.')


def flower_color_count(k):
    """Exact labeled edge color count by the three track edges across each cut."""
    from itertools import product
    states=list(product((1,2,3),repeat=3))
    next_states={a:[b for b in states if {x^y for x,y in zip(a,b)}=={1,2,3}] for a in states}
    total=0
    for start in states:
        weights={start:1}
        for _ in range(k):
            new={}
            for a,n in weights.items():
                for b in next_states[a]:new[b]=new.get(b,0)+n
            weights=new
        total+=weights.get((start[0],start[2],start[1]),0)
    return total


if __name__=='__main__':
    assert all(flower_color_count(k)==0 for k in (5,7,9))
    assert flower_color_count(4)>0
    print('Independent twisted track count gives zero at J5, J7, J9.')
