"""Bounded Boolean-quotient degree-two refutation tests after substituting pins.

Static uses original rows with multipliers of formal total degree <=2 after pin
substitution. Iterated additionally multiplies every derived affine row by each
remaining variable, multilinearizing at each step.
"""
from functools import lru_cache
from itertools import combinations
from random import Random
from collections import Counter
import networkx as nx


def insert(echelon,row):
    while row:
        j=row.bit_length()-1
        if j not in echelon:
            echelon[j]=row
            return True
        row^=echelon[j]
    return False


@lru_cache(None)
def coordinates(n):
    terms=[0]+[1<<i for i in range(n)]+[(1<<i)|(1<<j) for i,j in combinations(range(n),2)]
    pos={t:j for j,t in enumerate(terms)}
    mult=[[1<<pos[t|(1<<i)] for t in terms[:n+1]] for i in range(n)]
    return pos,mult


def closures(A,pins):
    free=[v for v in range(len(A)) if v not in pins]
    n=len(free)
    pos,mult=coordinates(n)
    mon={v:1<<j for j,v in enumerate(free)}
    orig=[]
    for i,row in enumerate(A):
        p=0
        for j in range(len(A)):
            if row>>j&1:p^=1<<pos[mon.get(i,0)|mon.get(j,0)]
        if p:orig.append(p)
    E={}
    for p in orig:insert(E,p)
    if 0 in E:return True,True
    def extend(rows):
        for p in rows:
            js=[]
            while p:
                term=p&-p;js.append(term.bit_length()-1);p^=term
            for image in mult:
                multiple=0
                for j in js:multiple^=image[j]
                insert(E,multiple)
    extend([p for p in orig if p.bit_length()<=n+1])
    static=0 in E
    done=set()
    while 0 not in E:
        fresh={p for j,p in E.items() if j<=n}-done
        if not fresh:break
        extend(fresh)
        done.update(fresh)
    return static,0 in E


def truth(A,pins):
    P=sum(1<<i for i in pins)
    f=((1<<len(A))-1)^P
    sub=f
    while True:
        x=P|sub
        if all(not (x>>i&1) or (row&x).bit_count()%2==0 for i,row in enumerate(A)):return True
        if not sub:return False
        sub=(sub-1)&f


def sample():
    stats=Counter();miss=None;upgrade=None
    def check(A,P):
        nonlocal miss,upgrade
        st,it=closures(A,P)
        sat=truth(A,P)
        assert not(st and not it) and not(it and sat)
        stats[len(A),('YES' if sat else 'static' if st else 'iterated' if it else 'miss')]+=1
        item=(len(A),P,[(i,j) for i,j in combinations(range(len(A)),2) if A[i]>>j&1])
        if not sat and not it and miss is None:miss=item
        if it and not st and upgrade is None:upgrade=item
    for G in nx.graph_atlas_g():
        n=len(G)
        if n<3:continue
        A=[sum(1<<j for j in G[i]) for i in range(n)]
        for P in combinations(range(n),3):check(A,P)
    rng=Random(4933)
    for n in range(8,12):
        for _ in range(1800):
            p=rng.choice([0.2,0.4,0.5,0.7,0.85])
            A=[0]*n
            for i,j in combinations(range(n),2):
                if rng.random()<p:A[i]|=1<<j;A[j]|=1<<i
            check(A,tuple(rng.sample(range(n),3)))
    print('per size, (YES, static, iterative-only, unresolved NO)')
    for n in range(3,12):print(n,tuple(stats[n,k] for k in ('YES','static','iterated','miss')))
    print('first iterative-only',upgrade,'first missed NO',miss)


if __name__=='__main__':
    sample()
    from high_connectivity_anchor_check import host
    for t in range(1,4):
        for yes in (False,True):
            _,A,P,_=host(t,yes)
            outcome=closures(A,P)
            print('anchor',t,'YES' if yes else 'NO',outcome)
            assert outcome[1]!=yes

if __name__=='__main__':
    A=[160,1572,10,1796,640,1859,1184,1105,1064,58,490]
    pins=(8,9,10)
    P=sum(1<<i for i in pins)
    assert not truth(A,pins) and closures(A,pins)==(False,False)
    flat=[]
    for t in range(32):
        x=48
        for i,b in enumerate([1,146,4,40,192]):
            if t>>i&1:x^=b
        flat.append(x|P)
    assert set(flat)=={x|P for x in range(256) if
                       all(((x|P)&A[j]).bit_count()%2==0 for j in pins)}
    assert all(any((x>>i&1) and (x&A[i]).bit_count()%2 for i in range(8)) for x in flat)
    full,quadratic={},{}
    for i in range(8):
        vals=[(x>>i&1)*((x&A[i]).bit_count()%2) for x in flat]
        for j in range(5):
            for t in range(32):
                if t>>j&1:vals[t]^=vals[t^(1<<j)]
        assert all(t.bit_count()<=2 or not b for t,b in enumerate(vals))
        insert(full,sum(b<<t for t,b in enumerate(vals)))
        insert(quadratic,sum(b<<t for t,b in enumerate(vals) if t.bit_count()==2))
    assert len(full)==len(quadratic)==7
    print('explicit 11-vertex NO: 32 pin-compatible assignments, residual/leading rank 7/7')
