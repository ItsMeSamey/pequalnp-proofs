"""04-only original assignment enumeration for signed conflict bicliques."""
from itertools import combinations, product
from random import Random
from unittest.mock import patch
from biclique_period import biclique_period_witness
from biclique_physical import UnsupportedConflict, biclique_block_witness, biclique_comparison_witness


def shell_ok(bits, edges):
    yes=[(bits[x]^bits[y])==d for x,y,d in edges]
    return all(yes[i] or yes[i+1] for i in range(0,len(yes),2))


def raw_ok(bits, pins):
    return all((bits[a]^bits[b])==d for a,b,d in pins) and all(
        bits[i:i+2]!=bits[i+2:i+4] for i in range(0,len(bits),4))


def copies(edges):
    seen={}; pins=[]
    for e,(a,b,d) in enumerate(edges):
        j=4*(e//2)+e%2
        for v,i,offset in ((a,j,0),(b,j+2,1^d)):
            first,old=seen.setdefault(v,(i,offset))
            if i!=first:pins.append((first,i,old^offset))
    return pins


def comparison(n,edges,required=False):
    words={w for w in product((0,1),repeat=n) if shell_ok(w,edges)}
    try: result=biclique_comparison_witness(n,edges)
    except UnsupportedConflict:
        assert not required
        return 'skip'
    assert (result is not None)==bool(words)
    if result is not None:assert tuple(result) in words
    pins=copies(edges)
    bits=biclique_block_witness(len(edges)//2,pins)
    assert (bits is not None)==bool(words)
    if bits is not None:assert len(bits)==2*len(edges) and raw_ok(bits,pins)
    if len(edges)<=4:
        assert any(raw_ok(w,pins) for w in product((0,1),repeat=2*len(edges)))==bool(words)
    return 'sat' if words else 'unsat'


def projected(columns,components):
    def syndrome(w):
        s=0
        for b,c in zip(w,columns):
            if b:s^=c
        return s
    def legal(w):
        return all(not(any(w[i] for i in A) and any(w[i] for i in B)) for A,B in components)
    possible={syndrome(w) for w in product((0,1),repeat=len(columns)) if legal(w)}
    for target in range(8):
        w=biclique_period_witness(columns,target,components)
        assert (w is not None)==(target in possible)
        if w is not None:assert len(w)==len(columns) and legal(w) and syndrome(w)==target


def collective():
    columns=[1,2,1,4,1,1,2,2,2,2,4,4]
    groups=[((i,i+1),(i+2,i+3)) for i in (0,4,8)]
    def no_branch(*args,repeat):
        assert repeat==0
        return product(*args,repeat=repeat)
    with patch('biclique_period.product',no_branch):
        projected(columns,groups)
    physical=[None]*12; n=0
    for c in (1,2,4):
        ids=[i for i,v in enumerate(columns) if v==c]
        for k,i in enumerate(ids):
            physical[i]=(n+k,n+(k+1)%len(ids),int(i in (0,6,10)))
        n+=len(ids)
    edges=[physical[i] for A,B in groups for a in A for b in B for i in (a,b)]
    assert comparison(n,edges,True)=='sat'


def triangles(clauses):
    sites=[]
    for j,clause in enumerate(clauses):
        a,b=2*j+1,2*j+2
        sites.extend(zip(clause,[(0,a,1),(a,b,0),(b,0,0)]))
    edges=[e for (p,u),(q,v) in combinations(sites,2) if p==-q for e in (u,v)]
    return comparison(2*len(clauses)+1,edges,True)


def main():
    collective()
    taut=[(1,-1,1),(-1,1,-1)]
    assert triangles([(1,1,1),*taut])=='sat'
    assert triangles([(1,1,1),(-1,-1,-1),*taut])=='unsat'
    assert comparison(1,[(0,0,1)]*2,True)=='unsat'
    assert comparison(2,[(0,1,0),(0,1,1)],True)=='sat'
    f=[(0,j,0) for j in range(1,5)]
    assert comparison(5,[f[0],f[1],f[1],f[2],f[2],f[3]])=='skip'
    assert biclique_block_witness(1,[(0,1,0),(0,1,1)]) is None
    rng=Random(44232)
    for _ in range(80):
        m=rng.randrange(8); cols=[rng.randrange(8) for _ in range(m)]
        split=rng.randrange(m+1)
        projected(cols,[(tuple(range(split)),tuple(range(split,m)))])
        n=rng.randrange(1,6)
        comparison(n,[(rng.randrange(n),rng.randrange(n),rng.randrange(2))
                      for _ in range(2*rng.randrange(1,4))])
        k=rng.randrange(1,3)
        pins=[(rng.randrange(4*k),rng.randrange(4*k),rng.randrange(2))
              for _ in range(rng.randrange(10))]
        truth=any(raw_ok(w,pins) for w in product((0,1),repeat=4*k))
        try: w=biclique_block_witness(k,pins)
        except UnsupportedConflict: continue
        assert (w is not None)==truth
        if w is not None:assert raw_ok(w,pins)
    print('80 flag/vertex/pin batches; collective, triangle SAT/NO, induced P4 skip')


if __name__=='__main__':main()
