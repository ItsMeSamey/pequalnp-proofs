"""Enumerate all two-planes by their three nonzero binary vectors."""
from itertools import combinations

def basis(words):
    pivots={}
    for w in words:
        while w:
            i=w.bit_length()
            if i not in pivots:
                pivots[i]=w
                break
            w ^= pivots[i]
    return tuple(pivots.values())

planes = sorted({tuple(sorted((a,b,a^b))) for a,b in combinations(range(1,16),2)})
full = (1<<len(planes))-1
plucker = []
for i,j in combinations(range(4),2):
    bits=0
    for k,(a,b,_) in enumerate(planes):
        val=((a>>i)&(b>>j))^((a>>j)&(b>>i))
        bits |= (val&1)<<k
    plucker.append(bits)

def feasible(plane,target):
    A=[v for v in [0,*plane] if v<4]
    P=[v>>2 for v in [0,*plane]]
    Q=[w for w in range(4) if all((w&p).bit_count()%2==0 for p in P)]
    return any((a&1) and (b&1) and ((a>>1)^(b>>1))==target for a in A for b in Q)

lin = list(plucker)
quad = lin+[a&b for a,b in combinations(lin,2)]
assert len(basis(quad))==20
assert len(basis(quad+[full]))==21
disjoint = [sum(1<<i for i,line in enumerate(planes) if not set(line)&set(template))
            for template in planes]

for s in (0,1):
    good=sum(1<<i for i,p in enumerate(planes) if feasible(p,s))
    bad=full^good
    assert good.bit_count()==5 and bad.bit_count()==30
    assert len(basis(q&bad for q in quad))==20
    assert len(basis(q&bad for q in quad+[full]))==21
    covered=0
    for a,b,c in combinations(disjoint,3):
        mask=a&b&c
        if mask&bad==0:covered |= mask
    assert covered==good
print('Both targets: 5 good lines, 30 bad; ranks 20 homogeneous and 21 affine on all and on bad; cubic cover complete.')
