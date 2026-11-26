"""Check affine charts and score-exception compression in the raw binary host."""
from itertools import product
from random import Random
from baseline import canonical, image, solve, family

def assess(cols,tags,U,colors):
    z=tuple(c for c,v in zip(cols,colors) if not v)
    if len(canonical(z))!=len(z):
        return None
    f=sum(bool(v&1)<<i for i,v in enumerate(colors))
    g=sum(bool(v&2)<<i for i,v in enumerate(colors))
    a=solve(U,image(cols,f))
    b=solve(U,image(cols,g))
    if a is None or b is None:
        return None
    score=image([x for x,y in tags],f)^image([y for x,y in tags],g)
    L=frozenset(i for i in range(1<<len(U)) if solve(z,image(U,i)) is not None)
    return (a,b),score,L

def check():
    rng=Random(4541)
    counts={}
    states=0
    for trial in range(150):
        d=rng.randrange(2,5)
        cols=tuple(rng.randrange(1<<d) for _ in range(rng.randrange(1,7)))
        tags=tuple((rng.randrange(8),rng.randrange(8)) for _ in cols)
        p=rng.randrange(1,1<<d)
        U=(p,) if trial%3 else (p,rng.choice([v for v in range(1,1<<d) if v!=p]))
        chart=family(cols,tags,U)
        if chart is None:
            continue
        kind,records=chart
        counts[kind,len(U)]=counts.get((kind,len(U)),0)+1
        observed={}
        for colors in product(range(4),repeat=len(cols)):
            actual=assess(cols,tags,U,colors)
            if actual:
                ab,score,L=actual
                observed.setdefault(ab,set()).add((score,L))
        assert set(observed)==set(records)
        for ab,(colors,score) in records.items():
            actual=assess(cols,tags,U,colors)
            assert actual[:2]==(ab,score)
            assert all(actual[2]<=L for _,L in observed[ab])
            states+=len(observed[ab])
        base,offset=records[0,0]
        for (a,b),(colors,score) in records.items():
            delta=tuple((1<<i,0) for i in range(len(U)) if a>>i&1)
            delta+=tuple((0,1<<i) for i in range(len(U)) if b>>i&1)
            checkcolors=list(base)
            checkscore=offset
            for h in delta:
                other,othertag=records[h]
                checkcolors=[v^u^c for v,u,c in zip(checkcolors,other,base)]
                checkscore^=othertag^offset
            assert tuple(checkcolors)==colors and checkscore==score
    for trial in range(200):
        k=trial%6
        deltas=[rng.randrange(1<<k) for _ in range(40)]
        target=image(deltas,(1<<len(deltas))-1)
        selected=solve(deltas,target)
        assert selected.bit_count()<=k and image(deltas,selected)==target
    # A real triangle spanning a two-dimensional port, duplicated virtually,
    # always has strictly nonzero witnesses for all 16 imbalance pairs.
    cols=(1,2,3)
    U=(1,2)
    possible=set()
    for c in product((1,2,3),repeat=3):
        possible.add(assess(cols,((0,0),)*3,U,c)[0])
    assert len(possible)==16
    assert family(cols,((0,0),)*3,U) is None
    print('charts',counts,'statuses',states,'40-child score checks',200,'triangle',len(possible))

if __name__=='__main__':
    check()
