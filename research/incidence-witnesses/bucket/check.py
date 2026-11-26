from itertools import combinations,product
from fractions import Fraction
from random import Random

def plane(q):
    reps=[p for p in product(range(q),repeat=3) if any(p) and next(v for v in p if v)==1]
    rows=[{j for j,l in enumerate(reps) if not sum(x*y for x,y in zip(p,l))%q} for p in reps]
    cols=[{i for i,r in enumerate(rows) if j in r} for j in range(len(reps))]
    return rows,cols

def only(s):
    assert len(s)==1
    return next(iter(s))

def check(q):
    P,L=plane(q); n=len(P); k=q//2
    c=(1,3); a=(0,4)
    join=lambda x,y:only(P[x]&P[y])
    meet=lambda l,j:only(L[l]&L[j])
    pointcode={p:tuple(join(p,i) for i in c) for p in range(n) if p not in c}
    linecode={l:tuple(meet(l,i) for i in a) for l in range(n) if l not in a}
    flags=[(p,l) for p in range(n) for l in P[p]]
    generic=[(p,l) for p,l in flags if p not in L[join(*c)]|L[a[0]]|L[a[1]]
             and l not in P[c[0]]|P[c[1]]|P[meet(*a)]]
    assert generic
    rng=Random(q); events=0
    for p,l in rng.sample(generic,min(25,len(generic))):
        for o,ell in flags:
            if o in L[l]|L[pointcode[p][0]]|L[pointcode[p][1]]|L[a[0]]|L[a[1]]:continue
            if L[ell]&{p,*c,*linecode[l]}:continue
            pts=L[ell]-{o}; lns=P[o]-{ell}
            need_pts={meet(ell,j) for j in pointcode[p]}
            need_lns={join(o,b) for b in linecode[l]}
            ban_pt=meet(ell,l); ban_ln=join(o,p)
            assert len(need_pts)==len(need_lns)==2
            assert need_pts<=pts-{ban_pt} and need_lns<=lns-{ban_ln}
            pp=[set(x) for x in combinations(pts,k) if need_pts<=set(x) and ban_pt not in x]
            tt=[set(x) for x in combinations(lns,k) if need_lns<=set(x) and ban_ln not in x]
            from math import comb
            assert Fraction(len(pp),comb(q,k))==Fraction(k*(k-1)*(q-k),q*(q-1)*(q-2))
            assert len(tt)==len(pp)
            for P0,T0 in [(rng.choice(pp),rng.choice(tt))]:
                assert all(not(P[i]&T0) for i in P0)
                assert not(P[p]&T0) and not(L[l]&P0) and p not in P0 and l not in T0
                assert all(L[b]&P0 for b in pointcode[p])
                assert all(P[b]&T0 for b in linecode[l])
                events+=1
    assert events
    return events

if __name__=='__main__':
    print('Verified good-background and hypergeometric counts:',sum(check(q) for q in (5,7)))

if __name__=='__main__':
    # When there are a,b growing families, check both one-hole conditional
    # bounds directly on the full hypergeometric population.
    from math import comb
    for q in range(20,90):
        for a in range(1,q//8+1):
            for b in range(1,q//8+1):
                hp=q//(2*(max(a,b)+1));ht=q//(2*(b+1))
                assert 1<=hp<=ht
                for needs,holes in [(a,hp),(b,ht)]:
                    exact=Fraction(comb(q-1-needs,holes-1),comb(q,holes))
                    assert exact>=Fraction(holes,2*q)
    print('Verified asymmetric hole probabilities for all tested coordinate counts.')
