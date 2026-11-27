"""Contract the emitted zero-based CNF using independent clause inclusion-exclusion."""
from itertools import product
from math import prod
from check_read_two_prime_frontend import evaluate as contract_physical
from read_two_ring_nonzero import compile_nonzero


def value(raw,modulus):
    # Reindex physical variables only. The contraction uses no division.
    return contract_physical(dict(clauses=[tuple(i+1 for i in c) for c in raw['clauses']],
                                  weights=[x%modulus for x in raw['point']]),modulus)


def main():
    for n,clauses,selectors in [(0,[()],{}),(0,[],{}),(1,[(1,)],{}),
                               (1,[],{1:-1}),(1,[(1,)],{1:-1}),
                               (1,[(1,),(-1,)],{}),(1,[(1,-1)],{1:0})]:
        raw=compile_nonzero(n,clauses,selectors=selectors)
        e,k=raw['expanded_edges'],raw['k']
        assert k==e+n+1 and raw['point'][raw['normalization_index']]==1
        witnesses=[x for x in product(range(2),repeat=n)
                   if all(any(x[abs(l)-1]==(l>0) for l in c) for c in clauses)]
        z=sum(prod(weight for j,weight in selectors.items() if x[j-1]) for x in witnesses)
        m=3**k
        residue=value(raw,m)
        assert residue==pow(-15,e,m)*z%m and (residue!=0)==(z!=0)
        if not selectors:
            assert bool(residue)==bool(witnesses)
        if abs(z)==1:
            # The first nonzero precision is e+1; valuation there is k_small-1.
            assert residue % 3**e==0 and residue % 3**(e+1)!=0
            assert value(raw,3**(e+1))==residue%3**(e+1)
        if witnesses and not clauses and selectors=={1:-1}:
            assert z==0
    print('Seven physical ring reductions, signed cancellations and precision boundaries passed.')


if __name__=='__main__':
    main()
