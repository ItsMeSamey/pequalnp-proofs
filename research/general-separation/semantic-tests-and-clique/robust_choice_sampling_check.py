"""Exhaust the disjoint-support two-feature construction on eight random tapes."""
from fractions import Fraction
from itertools import product

for mask in range(256):
    passes=mask.bit_count()
    for side,b in product(range(2),repeat=2):
        # First coordinate is designated. Rows on each support have constant label,
        # so free coefficients 0 and 1 include a Hamming minimizer over all reals.
        def miss(other):
            w=(b,other)
            rows=((t,((1-t,t*((mask>>i)&1))[::(-1 if side else 1)])) for i,t in product(range(8),range(2)))
            return sum(sum(a*c for a,c in zip(row,w))!=target for target,row in rows)
        dist=Fraction(min(miss(0),miss(1)),16)
        assert dist==(Fraction(8-passes,16) if side==b else Fraction(1,2) if side else Fraction(16-passes,16))
        assert (dist==0)==(side==b and passes==8)
for n in range(1,9):
    for samples in (1,4,16):
        rare=Fraction(1,2**n)
        assert (1-rare)**samples>=1-samples*rare
print('1024 pair-distance checks and 24 sparse sampling bounds passed')
