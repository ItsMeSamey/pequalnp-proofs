from itertools import combinations,product
from labelled_affine_orbit import prepare,solve
from labelled_switching_generators import dot


def hub(words,matrices):
    b=len(words[0])
    z=len(words)
    n=z+1
    zero=(0,)*b
    es=[(u,v,words[u] if v==z else zero) for u,v in combinations(range(n),2)]
    lookup={(u,v):i for i,(u,v,g) in enumerate(es)}
    actions=[]
    for A in matrices:
        perm=tuple(words.index(tuple(dot(row,g) for row in A)) for g in words)+(z,)
        emap=tuple(lookup[tuple(sorted((perm[u],perm[v])))] for u,v,g in es)
        actions.append((A,zero,perm,emap,(zero,)*n))
    return n,es,actions


def hub_match(n,es,t,*,avoiding=False):
    # Independent polynomial oracle on this hub: interiors remain zero under projection.
    z=n-1
    assert all(not any(g) for u,v,g in es if v!=z)
    ids={(u,v):i for i,(u,v,g) in enumerate(es)}
    for i,(u,v,g) in enumerate(es):
        if v==z and ((g!=t) if avoiding else (g==t)):
            rest=sorted(set(range(z))-{u})
            return 'SAT',(i,)+tuple(ids[a,c] for a,c in zip(rest[::2],rest[1::2])),{}
    return 'UNSAT',None,{}


if __name__=='__main__':
    all3=list(product(range(3),repeat=3))
    words=[g for g in all3 if g!=(0,0,0) and g[1:]!=(1,0)]
    n,es,acts=hub(words,[((1,1,0),(0,1,0),(0,0,1))])
    for t in all3:
        s,w,stats=solve(n,es,t,acts,backend=hub_match)
        assert s==('SAT' if t in words else 'UNSAT')
        if t[1:] == (1,0):
            assert stats['orbit']==3 and stats['flat_rank']==1
    words=list(product(range(3),repeat=2))
    n,es,acts=hub(words,[((1,1),(0,1)),((0,1),(1,0)),((2,0),(0,1))])
    q=prepare(n,es,2,acts)
    for t in words:
        s,w,stats=solve(n,es,t,acts,backend=hub_match)
        assert s=='SAT'
        if any(t):
            assert stats['orbit']==8 and stats['flat_rank']==1
    n,es,acts=hub([(0,),(1,),(2,)],[((2,),)])
    for t in ((1,),(2,)):
        s,w,stats=solve(n,es,t,acts,avoid=lambda n,e,g:hub_match(n,e,g,avoiding=True))
        assert s=='SAT' and stats['mode']=='avoid'
    A,t,perm,emap,p=acts[0]
    try:
        prepare(n,es,1,[(A,t,emap)])
    except ValueError:
        pass
    else:
        raise AssertionError('implicit semantic promise accepted')
    q=prepare(n,es,1,[(A,t,emap)],semantic_certificate=lambda *args:True)
    assert len(q.orbit((1,)))==2
    print('27 K24 targets, 9 nonflat-orbit controls, scalar reflection and explicit semantic callback passed')
