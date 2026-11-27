"""Literal checks for the sparse cubic image reduction with a full-cube union domain."""
from itertools import product
from random import Random
from frontier import solve

def violation(clause):
    terms={0}
    for variable,positive in clause:
        variable=1<<variable
        replacements=set()
        for monomial in terms:
            replacements.symmetric_difference_update((variable|monomial,))
            if positive:
                replacements.symmetric_difference_update((monomial,))
        terms=replacements
    return terms

def encode(n,clauses):
    clauses=list(clauses)
    if not clauses: raise ValueError("use a nonempty formula")
    while len(clauses)<max(2,n): clauses.append(clauses[0])
    m=len(clauses)
    dimension=m+n
    sites=[(1<<i,0,0) for i in range(m)]+[((1<<m)-1,0,1),(0,0,2)]
    sites.extend((1<<(m+i),tag,0) for i in range(n) for tag in range(4))
    encoder=[violation(clause) for clause in clauses]+[{1<<i} for i in range(n)]+[set() for _ in range(dimension)]
    return sites,dimension,encoder

def check():
    rng=Random(5825)
    for n in (1,2,3):
        for case in range(12):
            clauses=[[(rng.randrange(n),rng.choice((True,False))) for _ in range(3)] for _ in range(4)]
            if case%3==0: clauses.extend([[(0,True)],[(0,False)]])
            cols,d,encoder=encode(n,clauses)
            found,_=solve(cols,d,n,encoder)
            sat=lambda b: all(any(bool(b>>i&1)==sign for i,sign in c) for c in clauses)
            assert (found is not None)==any(sat(b) for b in range(1<<n))
            if found: assert sat(found[0])
    print('36 full-cube union-domain 3CNF reductions passed')
if __name__=='__main__': check()
