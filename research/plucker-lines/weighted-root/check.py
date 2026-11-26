from itertools import combinations
from random import Random
from solver import bits,component,search


def check(adj,s,t,w):
    n=len(adj)
    root=(1<<s)|(1<<t)
    def valid(x,extra):
        if (x & root) != root:
            return False
        c=component(adj,s,x)
        if any((adj[i]&c).bit_count()!=2 for i in bits(c)):
            return False
        return (x^c).bit_count() <= extra
    allpar=set()
    for x in range(1<<n):
        if valid(x,1):
            allpar.add((x&w).bit_count()%2)
    answer=search(adj,s,t,w)
    assert set(answer)==allpar,(adj,s,t,w,answer,allpar)
    assert all(valid(x,1) and (x&w).bit_count()%2==p for p,x in answer.items())


if __name__=='__main__':
    n=5
    edges=[e for e in combinations(range(n),2) if e!=(0,1)]
    for graph in range(1<<len(edges)):
        adj=[2,1]+[0]*(n-2)
        for k,(a,b) in enumerate(edges):
            if graph>>k&1:
                adj[a]|=1<<b
                adj[b]|=1<<a
        for w in range(1<<n):
            check(adj,0,1,w)
    r=Random(946)
    for _ in range(1500):
        n=r.randrange(6,12)
        adj=[0]*n
        for i,j in combinations(range(n),2):
            if (i,j)==(0,1) or r.randrange(4)==0:
                adj[i]|=1<<j
                adj[j]|=1<<i
        check(adj,0,1,r.getrandbits(n))
    # More than one genuine anchor must occur on these long cycles.
    for n in range(8,15):
        adj=[(1<<((i-1)%n))|(1<<((i+1)%n)) for i in range(n)]
        for w in [(1<<n)-1, r.getrandbits(n), 0]:
            check(adj,0,1,w)
    print("Passed 16,384 exhaustive, 1,500 seeded and 21 long-cycle tests.")

    from solver import affine_basis
    for _ in range(400):
        n=r.randrange(4,11)
        adj=[0]*n
        edges=list(combinations(range(n),2))
        r.shuffle(edges)
        for i,j in [(0,1)]+edges:
            if adj[i].bit_count()<3 and adj[j].bit_count()<3 and ((i,j)==(0,1) or r.randrange(2)):
                adj[i]|=1<<j
                adj[j]|=1<<i
        result=affine_basis(adj,0,1)
        supports=[x for x in range(1<<n) if x&3==3 and all((adj[i]&x).bit_count()%2==0 for i in bits(x))]
        assert bool(result)==bool(supports)
        if result:
            assert all(x in supports for x in result)
            span={result[0]}
            for x in result[1:]:
                diff=x^result[0]
                shift={z^diff for z in span}
                assert not span&shift
                span|=shift
            assert set(supports)<=span
    print("Also verified full affine hulls for 400 seeded subcubic graphs.")
