"""Direct trajectory, binary interlacement and expanded Pfaffian coefficient checks."""
from functools import lru_cache
from random import Random
from itertools import combinations


def orbits(succ):
    label={}
    paths=[]
    for a in range(len(succ)):
        if a in label:continue
        paths.append([])
        while a not in label:
            label[a]=len(paths)-1
            paths[-1].append(a)
            a=succ[a]
    return label,paths


def switch(succ,ab):
    a,b=ab
    succ[a],succ[b]=succ[b],succ[a]


def rank(rows):
    piv={}
    for v in rows:
        while v and v.bit_length() in piv:v^=piv[v.bit_length()]
        if v:piv[v.bit_length()]=v
    return len(piv)


def fixture(n,triples,feedback):
    H=2*len(triples)+1
    succ=[(i+1)*n+j if i+1<H else feedback[j] for i in range(H) for j in range(n)]
    chords=[]
    for i,(a,b,c) in enumerate(triples):
        chords.extend([((2*i)*n+a,(2*i)*n+b),((2*i+1)*n+a,(2*i+1)*n+c)])
    return succ,chords,(H-1)*n


def check(n,triples,feedback):
    succ,chords,last=fixture(n,triples,feedback)
    ref=succ.copy()
    T=0
    for i,ch in enumerate(chords):
        lab,_=orbits(ref)
        if lab[ch[0]]!=lab[ch[1]]:switch(ref,ch);T|=1<<i
    _,paths=orbits(ref)
    if len(paths)!=1:return False
    where={a:i for i,a in enumerate(paths[0])}
    def crosses(ab,cd):
        a,b=sorted(where[i] for i in ab)
        c,d=(where[i] for i in cd)
        return (a<c<b)!=(a<d<b)
    N=len(chords)
    A=[sum(1<<j for j,e in enumerate(chords) if crosses(ch,e)) for ch in chords]
    # Self-interlacement must be zero because neither endpoint is strictly between itself.
    W=[row for row in A]
    tags={}
    for k in range(len(triples)):
        i=2*k;j=i+1
        if ((T>>i)&3) in (0,3):
            tags[i,j]=1<<k
        else:
            a=len(W);W.append(0)
            W[i]|=1<<a;W[a]|=1<<i
            tags[j,a]=1<<k
    @lru_cache(None)
    def pf(mask):
        if not mask:return frozenset([0])
        low=mask&-mask
        i=low.bit_length()-1
        out=set()
        for j in range(i+1,len(W)):
            if not mask>>j&1:continue
            remain=mask^low^(1<<j)
            if W[i]>>j&1:out.symmetric_difference_update(pf(remain))
            if (i,j) in tags:out.symmetric_difference_update(x|tags[i,j] for x in pf(remain))
        return frozenset(out)
    got=pf((1<<len(W))-1)
    expected=set()
    for choice in range(1<<len(triples)):
        S=sum(3<<(2*i) for i in range(len(triples)) if choice>>i&1)
        X=S^T
        trace=succ.copy()
        for i,ch in enumerate(chords):
            if S>>i&1:switch(trace,ch)
        label,cycles=orbits(trace)
        M=[a&X for i,a in enumerate(A) if X>>i&1]
        r=rank(M)
        assert len(cycles)==1+X.bit_count()-r
        if len(cycles)==1:
            term=0
            for k in range(len(triples)):
                pair=(X>>(2*k))&3
                # odd block: auxiliary uses tagged second index when the first remains
                if pair in (0,1):term|=1<<k
            expected.add(term)
        for a,b in combinations(range(n),2):
            roots=(last+a,last+b)
            c=sum(1<<i for i,ch in enumerate(chords) if X>>i&1 and crosses(ch,roots))
            assert (label[roots[0]]==label[roots[1]])==(rank(M+[c])==r)
    assert got==expected
    return True


if __name__=='__main__':
    rng=Random(726)
    checked=0
    for _ in range(280):
        n=rng.randrange(3,8)
        p=rng.sample(range(n),n)
        ops=[rng.sample(range(n),3) for _ in range(rng.randrange(1,6))]
        checked+=check(n,ops,p)
    print(checked,'connected networks: every setting, tagged Pfaffian coefficient, and root pair checked.')
