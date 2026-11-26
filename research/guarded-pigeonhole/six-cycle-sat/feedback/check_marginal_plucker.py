"""Test formal coefficient identities by exhaustive physical switch routing."""
from itertools import combinations
from random import Random
from check_promise_pfaffian import fixture, settings, orbits


def multiply(p, q):
    return {x for x in ()} if not p or not q else parity_sums(p,q)


def parity_sums(p,q):
    out=set()
    for a in p:
        for b in q:
            out.symmetric_difference_update([a+b])
    return out


def run():
    rng=Random(2251)
    cases=pairs=nonconstant=0
    while cases<180:
        n=rng.randrange(3,8)
        m=rng.randrange(1,5)
        p,e,last=fixture(n,[rng.sample(range(n),3) for _ in range(m)],rng.sample(range(n),n))
        states=[orbits(t) for t in settings(p,e)]
        k=len(states[0][1])
        if k<2 or any(len(c)!=k for _,c in states):continue
        anchors=[rng.choice(c) for c in states[0][1]]
        if not all(len({L[v] for v in anchors})==k for L,_ in states):continue
        a,b=rng.choices(range(len(p)),k=2)
        def classes(L):
            named=[L[v] for v in anchors]
            return named.index(L[a]),named.index(L[b])
        observations=[classes(L) for L,_ in states]
        nonconstant+=len(set(observations))>1
        E=set()
        X=[set() for _ in anchors]; Y=[set() for _ in anchors]
        Z={ij:set() for ij in combinations(range(k),2)}
        for mask,(i,j) in enumerate(observations):
            term=sum(3**g for g in range(m) if mask>>g&1)
            E.add(term);X[i].add(term);Y[j].add(term)
            if i!=j:Z[tuple(sorted((i,j)))].add(term)
        for (i,j),z in Z.items():
            if multiply(E,z) != multiply(X[i],Y[j]) ^ multiply(X[j],Y[i]):
                raise ValueError((cases,i,j))
            pairs+=1
        cases+=1
    print(cases,'protected networks,',pairs,'formal identities,',nonconstant,'nonconstant class maps')


if __name__=='__main__':run()
