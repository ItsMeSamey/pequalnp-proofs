"""Construct a distinct-scope UNSAT formula whose orbit affine hull passes all pins."""
from itertools import combinations
from orbit_subcube import encode,labels,state

def fixture(n=8):
    remaining=set(range(1<<n));clauses=[]
    for S in combinations(range(n),3):
        cells=[{x for x in remaining if all((x>>v&1)==(a>>j&1) for j,v in enumerate(S))} for a in range(8)]
        pattern=max(range(8),key=lambda i:len(cells[i]))
        clauses.append(tuple((-1 if pattern>>j&1 else 1)*(v+1) for j,v in enumerate(S)))
        remaining-=cells[pattern]
        if not remaining:return clauses
    raise AssertionError("failed to cover assignment cube")
c=fixture()
g=encode(8,c)
assert all(state(8,x)&g.zero for x in range(256))
# Find an odd XOR of complete original states satisfying every zero pin.
basis={}
for x in range(256):
    row=((state(8,x)&g.zero)<<1)|1;comb=1<<x
    while row and row.bit_length() in basis:
        a,b=basis[row.bit_length()];row^=a;comb^=b
    if row:basis[row.bit_length()]=row,comb
r=1;w=0
while r:
    u,v=basis[r.bit_length()];r^=u;w^=v
assert w.bit_count()%2
relax=0
for x in range(256):
    if w>>x&1:relax^=state(8,x)
assert not relax&g.zero
print('variables, dimensions, unique scopes, odd affine support',8,g.dimension,len(c),w.bit_count())
print(c)
