"""All-output preimage counts for finite rank-one coupled field permutations."""
from itertools import product
from math import prod
from random import Random


def mul(x,y,mod):
    out=0
    while y:
        if y&1:out^=x
        x<<=1
        if x.bit_length()==mod.bit_length():x^=mod
        y>>=1
    return out


def permutation(m,rng):
    mod={3:11,5:37}[m]
    a,b=rng.sample(range(1,1<<m),2)
    c,d=rng.randrange(1<<m),rng.randrange(1<<m)
    table=[]
    for x in range(1<<m):
        z=mul(a,x,mod)^c
        table.append(mul(b,mul(z,mul(z,z,mod),mod),mod)^d)
    assert len(set(table))==1<<m
    return table


def functional(x,mask):
    return (x&mask).bit_count()%2


def check(m,parents,cycles,rng):
    n=len(parents)
    Q=1<<m
    diag=[permutation(m,rng) for _ in parents]
    inv=[[d.index(y) for y in range(Q)] for d in diag]
    # Edge into j uses the direction u[j] and a functional at its source;
    # outgoing tree edges may use different functionals at the same parent.
    u=[rng.randrange(1,Q) for _ in parents]
    ell=[rng.randrange(1,Q) for _ in parents]
    hist=[0]*(Q**n)
    for x in product(range(Q),repeat=n):
        index=0
        for j,p in enumerate(parents):
            y=diag[j][x[j]]
            if p is not None and functional(x[p],ell[j]):y^=u[j]
            index|=y<<(m*j)
        hist[index]+=1
    for index,actual in enumerate(hist):
        predicted=1
        for cycle in cycles:
            factors=[]
            for j,k in zip(cycle,cycle[1:]+cycle[:1]):
                assert parents[k]==j
                y=index>>(m*j)&(Q-1)
                b0=functional(inv[j][y],ell[k])
                b1=functional(inv[j][y^u[j]],ell[k])
                factors.append(b1-b0)
            predicted*=1+prod(factors)
        assert actual==predicted
    return {k:hist.count(k) for k in sorted(set(hist))}


def indegree_two():
    # Three F8 cubes: block 0 receives BOTH leaf bits, both leaves receive
    # the same bit from block 0. Isolated-cycle products can double-count.
    Q=8
    cube=[mul(x,mul(x,x,11),11) for x in range(Q)]
    inv=[cube.index(y) for y in range(Q)]
    hist=[0]*(Q**3)
    for x,a,b in product(range(Q),repeat=3):
        v=cube[x]^(a&1)^(b&1)
        w=cube[a]^(x&1)
        z=cube[b]^(x&1)
        hist[v+8*w+64*z]+=1
    # At y=(0,0,0), each isolated cycle has determinant product +1.
    assert (inv[0]&1,inv[1]&1)==(0,1)
    assert hist[0]==1
    return hist[0],(1+1)**2


if __name__=='__main__':
    rng=Random(2765)
    cases=[(3,[None,0,0,2,2],[]),
           (3,[1,0,0,0,3],[[0,1]]),
           (3,[2,0,1,2,1],[[0,1,2]]),
           (3,[1,0,3,2,2],[[0,1],[2,3]]),
           (3,[0,0,1],[[0]]),
           (5,[1,0],[[0,1]])]
    for m,parents,cycles in cases:
        print(m,parents,check(m,parents,cycles,rng))
    print('indegree-two actual and naive product:',indegree_two())
