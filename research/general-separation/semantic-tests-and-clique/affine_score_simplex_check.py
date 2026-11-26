"""Check signed clause moments under affine restrictions and disjoint simplex blocks."""
from itertools import product
from math import prod
from random import Random

def solutions(n,eqs):
    basis={}
    for mask,bit in eqs:
        while mask:
            p=mask.bit_length()-1
            if p not in basis:
                basis[p]=(mask,bit)
                break
            a,b=basis[p]
            mask^=a
            bit^=b
        else:
            if bit:
                return 0
    return 1<<(n-len(basis))

rng=Random(481)
for case in range(55):
    n=rng.randrange(1,7)
    affine=[(rng.randrange(1<<n),rng.randrange(2)) for _ in range(rng.randrange(4))]
    # Clause falsity means all of its queried affine literals have the specified bits.
    terms=[(rng.randrange(-3,4),[(rng.randrange(1<<n),rng.randrange(2))
             for _ in range(rng.randrange(4))]) for _ in range(rng.randrange(5))]
    def sat(x,eqs):
        return all((x&m).bit_count()%2==b for m,b in eqs)
    scores=[sum(w for w,c in terms if sat(x,c)) for x in range(1<<n) if sat(x,affine)]
    for j in range(5):
        via=sum(prod(w for w,c in tup)*solutions(n,affine+[e for w,c in tup for e in c])
                for tup in product(terms,repeat=j))
        assert via==sum(s**j for s in scores)

cases=0
for n in range(1,9):
    for splits in range(1<<(n-1)):
        ends=[0]+[j+1 for j in range(n-1) if splits>>j&1]+[n]
        blocks=[{m<<i for m in range(1,1<<(j-i))} for i,j in zip(ends,ends[1:])]
        # Integer normalization permits unequal block lengths.
        scores=[sum((128//((len(b)+1)//2))*sum((x&m).bit_count()%2 for m in b)
                    for b in blocks) for x in range(1<<n)]
        assert set(scores)=={128*j for j in range(len(blocks)+1)}
        zeros=[x for x,s in enumerate(scores) if s==0]
        assert zeros==[0]
        masks={0}
        for b in blocks:
            masks={a^v for a in masks for v in b|{0}}
        assert len(masks)==1<<n
        assert all(sum((-1)**((x&m).bit_count()%2) for x in zeros)==1 for m in masks)
        cases+=1
print('55 affine tuple cases; all',cases,'ordered contiguous partitions through n=8 passed')
