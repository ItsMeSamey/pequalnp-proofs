"""Mixed ordinary and normalized bits, with GF(2)[z] encoded by bit masks."""
from collections import defaultdict
from functools import cache, reduce
from itertools import product
from math import prod
from random import Random


def mul(a,b):
    ans=0
    while b:
        if b&1:
            ans ^= a
        b >>= 1
        a <<= 1
    return ans


def graph(rows, ordinary, normalized):
    mono=[row[0] for row in rows]
    neighbors=defaultdict(list)
    def vertex(weight):
        mono.append(weight)
        return len(mono)-1
    def edge(i,j,weight):
        neighbors[i].append((j,weight))
        neighbors[j].append((i,weight))
    for j in range(ordinary+normalized):
        refs=[(i,row[1][j]) for i,row in enumerate(rows) if row[1][j]]
        if j>=ordinary:
            shared=vertex(1)
            for i,a in refs:
                edge(i,shared,a)
        elif not refs:
            return 0
        elif len(refs)==1:
            i,a=refs[0]
            edge(i,vertex(0),a)
        else:
            assert len(refs)==2
            u,v=vertex(1),vertex(1)
            edge(u,v,1)
            for (i,a),t in zip(refs,(u,v)):
                edge(i,t,a)
    @cache
    def visit(S):
        if not S:
            return 1
        i=(S&-S).bit_length()-1
        rest=S^(1<<i)
        ans=mul(mono[i],visit(rest))
        for j,weight in neighbors[i]:
            if rest>>j&1:
                ans ^= mul(weight,visit(rest^(1<<j)))
        return ans
    return visit((1<<len(mono))-1)


def check(rows,b,u):
    terms=[[(None,c)]+[(j,a) for j,a in enumerate(A) if a] for c,A in rows]
    expected=0
    for choices in product(*terms):
        indices=[i for i,_ in choices]
        if all(j in indices for j in range(b)) and all(indices.count(j)<=1 for j in range(b,b+u)):
            expected ^= reduce(mul,(a for _,a in choices),1)
    assert graph(rows,b,u)==expected
    for z in (0,1):
        def value(a):
            return a&1 if z==0 else a.bit_count()%2
        raw=sum(prod(value(c)+sum(value(a)*x*(1 if j<b else 2) for j,(a,x) in enumerate(zip(A,xs))) for c,A in rows)
                for xs in product((0,1),repeat=b+u))
        assert raw%(1<<u)==0 and (raw>>u)&1==value(expected)
    return expected


def fixed_branches():
    # OR ports x,zY; COPY ports x,zY,1. Both x references are ordinary.
    x=(0,[1,0]); y=(0,[0,2]); one=(1,[0,0])
    comp=lambda r:(r[0]^1,r[1])
    total=0
    for a in ([],[comp(x),comp(y)]):
        for b in ([x,y,one],[comp(x),comp(y),comp(one)]):
            total ^= check(a+b,1,1)
    # COPY forces selection of xy and the normalized moment kills its repeat.
    # OR=(x+zY+xzY); combined with COPY=xzY leaves only x²zY.
    assert total==2
    for alpha,beta,gamma,delta in product(range(2),repeat=4):
        if delta:
            sig=(gamma*beta^(alpha^beta*gamma),beta,gamma,1)
            assert sig==(alpha,beta,gamma,delta)


if __name__=='__main__':
    rng=Random(137)
    for _ in range(500):
        b,u,r=[rng.randrange(4) for i in range(3)]
        rows=[(rng.randrange(8),[0]*(b+u)) for i in range(r)]
        for j in range(b+u):
            for i in rng.sample(range(r),rng.randrange(1+min(r,2 if j<b else r))):
                rows[i][1][j]=rng.randrange(1,8)
        check(rows,b,u)
    fixed_branches()
    print('500 polynomial mixed graphs, 1000 integer averages, OR/COPY branches and binary signatures passed')
