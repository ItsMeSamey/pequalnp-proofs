from itertools import combinations,product
from random import Random
from choice_cover_one_xor import solve,odd_cycle

def instance(groups,resources):
    clauses=list(groups)
    events=[(g,l) for g,G in enumerate(groups) for l in G]
    for (g,l),(h,k) in combinations(events,2):
        if g==h or resources[abs(l)]==resources[abs(k)]:clauses.append((-l,-k))
    return clauses

def check(n,groups,resources,xor,b):
    C=instance(groups,resources)
    def valid(x):
        tr=lambda l:(x>>(abs(l)-1)&1)^(l<0)
        return all(any(map(tr,c)) for c in C) and sum(map(tr,xor))%2==b
    got=solve(n,C,range(len(groups)),xor,b)
    assert (got is not None)==any(valid(x) for x in range(1<<n)),(groups,resources,xor,b)
    if got is not None:assert valid(got)
    return got is not None

if __name__=='__main__':
    cases=sat=0
    for signs in product((-1,1),repeat=4):
        groups=[[signs[0],2*signs[1]],[3*signs[2],4*signs[3]]]
        for pattern in product(range(2),repeat=4):
            resources=dict(enumerate(pattern,1))
            for mask in range(16):
                xor=[v+1 for v in range(4) if mask>>v&1]
                for rhs in (0,1):
                    sat+=check(4,groups,resources,xor,rhs);cases+=1
    rng=Random(7154)
    for _ in range(600):
        groups=[];resources={};v=0
        for g in range(rng.randrange(5)):
            G=[]
            for i in range(rng.randrange(1,4)):
                v+=1;resources[v]=rng.randrange(4);G.append(rng.choice((-v,v)))
            groups.append(G)
        n=v+rng.randrange(2)
        xor=[rng.choice((-1,1))*rng.randint(1,n) for i in range(rng.randrange(8))] if n else []
        sat+=check(n,groups,resources,xor,rng.randrange(2));cases+=1
    # Deliberately force both parity-only and matching-only UNSAT.
    assert not check(1,[[1]],{1:0},[1],0)
    assert not check(2,[[1],[2]],{1:0,2:0},[],0)
    # Group 0 must select another parallel option to achieve odd parity.
    assert check(4,[[1,2],[3,4]],{1:0,2:0,3:0,4:1},[2],1)
    # Artificial residual with a repeated-vertex parity walk and a neutral loop.
    graph=[[(1,0,0)],[(1,0,1),(2,0,2)],[(1,1,3),(0,0,4)]]
    cycle=odd_cycle(graph)
    assert len(set(x for x,_ in cycle))==len(cycle)
    print(cases,'brute-force comparisons:',sat,'SAT,',cases-sat,'UNSAT')
