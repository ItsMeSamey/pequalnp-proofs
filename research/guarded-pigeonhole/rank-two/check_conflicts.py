from itertools import combinations
from random import Random
def par(x):return x.bit_count()%2
def span(vs):
    a={0}
    for v in vs:a|={w^v for w in a}
    return a
rng=Random(77491);tested=branches=deep=0
for it in range(300):
    n=rng.randrange(4,9);edges=list(combinations(range(n),2));rng.shuffle(edges);edges=edges[:min(len(edges),rng.randrange(5,12))]
    labels=[rng.randrange(4) for _ in edges]
    U=span(x^par(x) for x in [rng.randrange(1<<n) for _ in range(3)]);qrank=len(U).bit_length()-1;b=rng.randrange(1<<n)
    cycles=[];eul=[]
    for s in range(1,1<<len(edges)):
        odd=v=z=0
        for i,(a,c) in enumerate(edges):
            if s>>i&1:odd^=(1<<a)^(1<<c);v|=(1<<a)|(1<<c);z^=labels[i]
        if odd:continue
        if not any(t&s==t for t in eul):cycles.append((s,v,z))
        eul.append(s)
    for a0,a1 in combinations((1,2,3),2):
        pairs=[(v0,v1) for _,v0,z0 in cycles for _,v1,z1 in cycles if z0==a0 and z1==a1 and not v0&v1]
        if not pairs:continue
        def fit(v0,v1):
            return any(not col&v0 and col&v1==v1 and all(not par((col^b)&u) for u in U) for col in range(1<<n))
        expect=any(fit(p,q) for p,q in pairs)
        def rec(X,T,depth):
            global deep,branches
            deep=max(deep,depth)
            options=[(p,q) for p,q in pairs if not ((p|q)&X) and all(not par((q^b)&u) for u in T)]
            if not options:return False
            p,q=options[0]
            if fit(p,q):return True
            u=next(u for u in U if not(u&~(p|q)) and par((q^b)&u))
            assert not(u&X) and u not in T and depth<2*qrank
            branches+=1
            return any(rec(X|(1<<i),T,depth+1) for i in range(n) if u>>i&1) or rec(X,span([*T,u]),depth+1)
        assert rec(0,{0},0)==expect
        tested+=1
print(tested,'opposite-color subproblems;',branches,'conflict nodes; max depth',deep)
