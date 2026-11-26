from itertools import combinations
from functools import reduce
from operator import xor
pairs=list(combinations(range(4),2))
def wedge(a,b):
    return sum(((((a>>i)&1)*((b>>j)&1))^(((a>>j)&1)*((b>>i)&1)))<<k for k,(i,j) in enumerate(pairs))
P=sorted({wedge(a,b) for a in range(1,16) for b in range(a+1,16)})
assert len(P)==35
def bit(x):return x.bit_count()&1
def isolates(S):return all(all(bit(p&q) for q in S)==(p==1) for p in [0]+P)
assert isolates((1,3,17,45))
L=[p for p in P if p&1]
for k in range(1,5):
    assert sum(isolates(T) for T in combinations(L,k))==(584 if k==4 else 0)
for X,ranklist,targetlist in [(P,[7,21,35,35],[False,False,True,True]),([0]+P,[7,21,35,36],[False,False,False,True])]:
    for d in range(1,5):
        basis={}
        def rem(z):
            while z and z.bit_length() in basis:z^=basis[z.bit_length()]
            return z
        for m in range(64):
            if m.bit_count()>d:continue
            z=rem(sum(int(p&m==m)<<i for i,p in enumerate(X)))
            if z:basis[z.bit_length()]=z
        assert len(basis)==ranklist[d-1] and (rem(1<<X.index(1))==0)==targetlist[d-1]
print('35 nonzero Klein points, 584 quartets, and all eight evaluation-space ranks verified')
