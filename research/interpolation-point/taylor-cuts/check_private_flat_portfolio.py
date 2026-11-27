from itertools import combinations,product
from random import Random
from private_flat_portfolio import solve
from clause_rank_drop_hybrid import count as source_flat

def valid(x,cs,rows):
    return all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in cs) and all((x&m).bit_count()%2==b for m,b in rows)

def check(n,cs,rows,**caps):
    count=sum(valid(x,cs,rows) for x in range(1<<n))
    out=solve(n,cs,rows,**caps)
    if out['status']!='UNKNOWN':
        assert out['count']==count
        assert valid(out['witness'],cs,rows) if count else out['witness'] is None
    return out

def safe(n,src):
    cs=[];z=n
    for c in src:
        markers=list(range(z+1,z+1+len(c)));z+=len(c)
        cs.extend([markers,*[(-i,-j) for i,j in combinations(markers,2)],*[(-m,l) for m,l in zip(markers,c)]])
    src_count=sum(valid(x,src,[]) for x in range(1<<n))
    certs=sum(valid(x,cs,[]) for x in range(1<<z))
    ans=solve(z,cs,[],flat_cap=6,soft_terms_cap=8,source_flat_cap=6)
    assert ans['count']==certs
    return src_count,certs,ans['stage']

if __name__=='__main__':
    rng=Random(80713); seen=set()
    for _ in range(180):
        n=rng.randrange(1,7)
        cs=[tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randrange(1,5))) for j in range(rng.randrange(11))]
        rows=[(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(3))]
        for caps in (dict(peel_rank_cap=0,flat_cap=0,soft_terms_cap=1),dict(peel_rank_cap=0,flat_cap=2,soft_terms_cap=4,source_flat_cap=n)):
            o=check(n,cs,rows,**caps);seen.add(o['stage'])
            if 'source_flat_cap' in caps:assert o['status']!='UNKNOWN'
    # Shared rank-two obstruction with one genuinely soft private projection.
    cs=[(i,j) for i in (1,2) for j in range(3,7)]+[(1,7),(8,9),(10,11)]
    o=check(11,cs,[],flat_cap=2,soft_terms_cap=2)
    assert o['stage']=='private-flat' and o['count']==324 and o['metrics']['soft_terms']==2
    assert source_flat(11,cs,cap=2,group_equal=True)[0] is None
    assert solve(11,cs,[],flat_cap=2,soft_terms_cap=1)['status']=='UNKNOWN'
    fallback=solve(11,cs,[],flat_cap=0,soft_terms_cap=1,source_flat_cap=6)
    assert fallback['stage']=='source-flat' and fallback['count']==324
    # XOR-tie the first hub to a new complemented bit, and use it as a private guard.
    tied=check(12,cs+[(-12,7)],[(1|(1<<11),1)],flat_cap=2,soft_terms_cap=2)
    assert tied['count']==324 and tied['stage']=='private-flat'
    # All four hub patterns forbidden: still certificates for an UNSAT decision.
    neg=check(11,cs+[[a,b] for a in (1,-1) for b in (2,-2)],[],flat_cap=2,soft_terms_cap=2)
    assert neg['status']=='UNSAT'
    controls=[safe(1,[(1,1,1),(-1,-1,-1)]),safe(2,[(1,2,1),(-1,2,-1)])]
    assert [x[:2] for x in controls]==[(0,0),(2,6)]
    print('180 random CNF+XORs at two budgets;',seen,'mixed',o,'tied',tied['count'],'safe source/certificates',controls)
