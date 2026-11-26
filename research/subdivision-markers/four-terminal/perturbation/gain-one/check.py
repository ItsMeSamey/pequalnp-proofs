"""Monomial-level audit of the score-one tree and unicycle sieve."""
from itertools import combinations
from random import Random


def submasks(m):
    s=m
    while s:
        yield s
        s=(s-1)&m


def tables(n,edges):
    m=len(edges)
    boundary=[0]*(1<<m)
    for s in range(1,len(boundary)):
        e=s&-s
        a,b=edges[e.bit_length()-1]
        boundary[s]=boundary[s^e]^(1<<a)^(1<<b)
    trees=[]
    for t in range(1<<m):
        if t.bit_count()==n-1 and all(boundary[s] for s in submasks(t)):
            joins={boundary[s]:s for s in [0,*submasks(t)]}
            trees.append((t,joins))
    return boundary,trees


def check(boundary,trees,u,g,r):
    # Full circuit truth table by submask tests in the perturbed matrix.
    ker=[(v ^ (u if (s&g).bit_count()%2 else 0))==0 for s,v in enumerate(boundary)]
    good={s for s in range(1,len(ker)) if ker[s] and (g&s).bit_count()%2 and r&s==r and
          all(not ker[t] for t in submasks(s) if t!=s)}
    qualifying_trees=set()
    contributions={}
    for t,j in trees:
        c=j[u]
        if r&c==r and (g&c).bit_count()%2:
            qualifying_trees.add(t)
        for e in submasks(g&~t):
            if e.bit_count()!=1:
                continue
            f=j[u^boundary[e]]
            if (r&~e)&f!=(r&~e) or (g&f).bit_count()%2:
                continue
            k=t|e
            contributions.setdefault(k,[]).append(f|e)
    surviving={k for k,c in contributions.items() if len(c)%2}
    assert bool(qualifying_trees or surviving)==bool(good)
    for t,j in trees:
        if t in qualifying_trees:
            assert j[u] in good
    cancellations=0
    for k,choices in contributions.items():
        cycle=next(q for q in submasks(k) if not boundary[q])
        for c in set(choices):
            if cycle&c==cycle:
                assert choices.count(c)==(cycle&g).bit_count()
                if choices.count(c)%2:
                    assert c in good
                else:
                    cancellations+=1
            else:
                assert c in good
        if k in surviving:
            assert any(c in good for c in choices)
    # If forest sieve is empty, every genuine cyclic witness can be extended
    # to a surviving monomial, so this also checks individual completeness.
    if not qualifying_trees:
        assert all(any(c in contributions[k] for k in surviving) for c in good)
    return bool(qualifying_trees),bool(surviving),cancellations


if __name__=='__main__':
    rng=Random(473)
    results=[0,0,0]
    n=4
    edges=list(combinations(range(n),2))
    boundary,trees=tables(n,edges)
    cases=0
    for u in range(1,1<<n):
        if u.bit_count()%2:
            continue
        for g in range(1<<len(edges)):
            for r in range(1<<len(edges)):
                if r.bit_count()>3:
                    continue
                out=check(boundary,trees,u,g,r)
                results=[a+b for a,b in zip(results,out)]
                cases+=1
    for _ in range(250):
        n=rng.randrange(2,8)
        edges=[(i,rng.randrange(i)) for i in range(1,n)]
        edges.extend((rng.randrange(n),rng.randrange(n)) for _ in range(rng.randrange(5)))
        boundary,trees=tables(n,edges)
        u=rng.randrange(1,1<<(n-1))<<1
        u|=u.bit_count()%2
        g=rng.randrange(1<<len(edges))
        r=rng.randrange(1<<len(edges))
        out=check(boundary,trees,u,g,r)
        results=[a+b for a,b in zip(results,out)]
        cases+=1
    print(cases,"instances; tree-positive, unicycle-positive, cancelled cyclic candidates:",results)
