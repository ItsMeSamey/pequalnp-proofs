"""Check constant principal-extension parity against independent tree and join oracles."""
from random import Random


def rank(vectors):
    basis={}
    for x in vectors:
        while x and (p:=x.bit_length()-1) in basis:
            x^=basis[p]
        if x:
            basis[x.bit_length()-1]=x
    return len(basis)


def maskbits(bits):
    return sum(1<<i for i in bits)


def run():
    rng=Random(81297)
    cases=choices=yes=0
    for _ in range(420):
        n=rng.randrange(2,8)
        tree=[(i,rng.randrange(i)) for i in range(1,n)]
        k=rng.randrange(1,n)
        edges=tree+[(rng.randrange(n),rng.randrange(n)) for _ in range(rng.randrange(5))]
        d=rng.getrandbits(n)
        d^=d.bit_count()%2
        A=set(range(k+1))
        S=set(A)
        for v in range(n):
            if d>>v&1:S.symmetric_difference_update([v])
        for u,v in edges[:k]:
            S.symmetric_difference_update([u]); S.symmetric_difference_update([v])
        top=[v for v in range(n) if v not in A]
        p=len(top)
        E=edges[k:]
        b=p+n+((k+1)%2)
        M=[0]*(b+2*len(E))
        def put(i,j):
            M[i]^=1<<j; M[j]^=1<<i
        clique=[p+i for i in S]+([b-1] if (k+1)%2 else [])
        for j,v in enumerate(clique):
            for w in clique[:j]:put(v,w)
        for j,(u,v) in enumerate(E):
            for i in (u,v):
                if i in top:put(top.index(i),b+2*j)
                put(p+i,b+2*j+1)
        feasible=False
        incidence=[(1<<u)^(1<<v) for u,v in edges]
        for F in range(1<<len(E)):
            P=list(range(b))+[b+2*j+a for j in range(len(E)) if F>>j&1 for a in (0,1)]
            pm=maskbits(P)
            actual=rank(M[i]&pm for i in P)==len(P)
            expected=False
            if F.bit_count()==p:
                ids=list(range(k))+[k+j for j in range(len(E)) if F>>j&1]
                if rank(incidence[i] for i in ids)==n-1:
                    target=d
                    for x in incidence[:k]:target^=x
                    # Direct inclusion Δ in incidence span of F, checked by row rank.
                    ff=[incidence[k+j] for j in range(len(E)) if F>>j&1]
                    expected=rank(ff+[target])==rank(ff)
            assert actual==expected
            choices+=1
            feasible |= actual
        direct=False
        for raw in range(1<<len(E)):
            ids=list(range(k))+[k+j for j in range(len(E)) if raw>>j&1]
            demand=0
            for i in ids:demand^=incidence[i]
            if demand==d and rank(incidence[i] for i in ids)==len(ids):
                direct=True;break
        assert direct==feasible
        cases+=1;yes+=direct
    print(cases,'connected-R systems;',choices,'complete principal extensions;',yes,'positive')
if __name__=='__main__':
    run()
