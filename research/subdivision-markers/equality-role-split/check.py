"""Cross-check two algorithms against direct enumeration of interpolating bases."""
from itertools import combinations, permutations
from random import Random
from pathlib import Path
import sys
sys.path.append(str(Path(__file__).resolve().parents[1] / 'unseeded-root-states'))
from solve import xor, canonical, solve, image, eliminate


def direct(cols, labels, pins):
    r=len(canonical(cols))
    for base in combinations(range(len(cols)),r):
        T=[cols[e] for e in base]
        if len(canonical(T))!=r:
            continue
        os=[labels[e] for e in base]
        sol=[solve(T,p) for p in pins]
        if all(s is not None and image(os,s)==0 for s in sol):
            return True
    return False


def run():
    rng=Random(511)
    targets=full=full_yes=0
    for rep in range(190):
        n=rng.randrange(2,5)
        # Two permutation layers, thinning some roles gives paths as well as cycles.
        a=list(range(n)); b=a.copy(); rng.shuffle(a);rng.shuffle(b)
        edges=[(i,j) for i,row in enumerate(zip(a,b)) for j in sorted(set(row)) if rng.randrange(5)]
        role=[(1<<u)|(1<<(n+v)) for u,v in edges]
        gains=[rng.randrange(1<<(rep%5)) for e in edges]
        labels=[0 if rep%3==0 else rng.randrange(4) for e in edges]
        cols=[b^(g<<(2*n)) for b,g in zip(role,gains)]
        # In degree up to two these fundamental cycles have disjoint supports and exhaust all role cycles.
        _,cycles=eliminate(role)
        assert all(not (u&v) for u,v in combinations(cycles,2))
        G=[image(gains,C) for C in cycles]
        O=[image(labels,C) for C in cycles]
        r=len(canonical(G))
        def tables(pins):
            refs=[solve(cols,p) for p in pins]
            if None in refs:return False
            initial=image(labels,refs[0])|(image(labels,refs[1])<<2)
            for J in combinations(range(len(cycles)),r):
                B=[G[j] for j in J]
                if len(canonical(B))!=r:continue
                states={initial}
                for i,C in enumerate(cycles):
                    if i in J:continue
                    coeff=solve(B,G[i])
                    Q=O[i]^image([O[j] for j in J],coeff)
                    options={((Q if refs[0]>>e&1 else 0)|((Q if refs[1]>>e&1 else 0)<<2))
                             for e in range(len(cols)) if C>>e&1}
                    states={s^v for s in states for v in options}
                if 0 in states:return True
            return False
        for _ in range(4):
            pins=[image(cols,rng.randrange(1<<len(cols))) for _ in range(2)]
            if len(canonical(pins))<2:continue
            assert tables(pins)==direct(cols,labels,pins)
            targets+=1
        p=(1<<(2*n))-1
        m0=solve(role,p)
        if m0 is None:continue
        d0=image(gains,m0); o0=image(labels,m0)
        for trial in range(5):
            d1,d2=[rng.randrange(1<<(rep%5)) for _ in range(2)]
            if trial==0 and any(G):
                d1,d2=d0,d0^next(g for g in G if g)
            if d1==d2:continue
            pins=(p|(d1<<(2*n)),p|(d2<<(2*n)))
            lx=solve([a|(b<<5) for a,b in zip(G,O)],(d1^d0)|(o0<<5)) is not None
            iz=False
            for z in range(1<<len(cycles)):
                gs=[g for i,g in enumerate(G) if z>>i&1]
                if len(canonical(gs))==len(gs) and image(G,z)==d1^d2 and image(O,z)==0:
                    iz=True;break
            predicted=lx and iz
            assert predicted==direct(cols,labels,pins)==tables(pins)
            full+=1;full_yes+=int(predicted)
    arcs=[(0,1),(1,2),(2,0),(3,4),(4,5),(5,3),(0,3),(4,0)]
    role=[(1<<u)|(1<<(6+v)) for u,v in arcs]
    assert direct(role,[0]*len(arcs),[(1<<12)-1,role[0]])
    for perm in permutations(range(1,6)):
        path=(0,)+perm+(0,)
        assert not all(e in arcs for e in zip(path,path[1:]))
    print('arbitrary-pin comparisons',targets,'two-cover comparisons',full,'YES',full_yes,'articulation control passes')
    assert full_yes
run()
