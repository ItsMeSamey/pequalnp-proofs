"""Single-call private-guard uniformization, checked by enumerating guard strata."""
from itertools import combinations,product

def verify(n,clauses):
    w = sum(m.bit_count() for m,b in clauses)
    pools = []
    start = 0
    for m,b in clauses:
        k = m.bit_count()
        pools.append(((1<<k)-1)<<start)
        start += k
    assert all((m.bit_count()+w-p.bit_count())==w for (m,b),p in zip(clauses,pools))
    base = sum(all(x&m!=b for m,b in clauses) for x in range(1<<n))
    total = sum(all(x&m!=b or g&~p for (m,b),p in zip(clauses,pools))
                for g,x in product(range(1<<w),range(1<<n)))
    known = sum((2**m.bit_count()-1)*2**(n-m.bit_count()) for m,b in clauses)
    assert base == total-(1<<(n+w))+(1<<n)+known

if __name__=='__main__':
    cases = 0
    for n,kmax in ((0,1),(1,3),(2,3),(3,2)):
        cubes=[(m,b) for m,b in product(range(1<<n),repeat=2) if m&b==b]
        for k in range(kmax+1):
            for clauses in combinations(cubes,k):
                verify(n,clauses)
                cases+=1
    print(cases,'guard-pool reductions passed')
