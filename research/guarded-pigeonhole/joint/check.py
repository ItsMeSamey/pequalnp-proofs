"""Directly enumerate split graphs, affine planes, and restrictions."""
from itertools import combinations
from functools import reduce
G=[112,56,120,6,7,7,5]
L=[1,3,2,2,4,4,4]
def feas(A,x):return all(not(x>>i&1) or (row&x).bit_count()%2==0 for i,row in enumerate(A))
def score(x):return reduce(int.__xor__,[l for i,l in enumerate(L) if x>>i&1],0)
def joint(N,remain=127):
    A=G.copy()+[0]*4
    def edge(i,j):A[i]|=1<<j;A[j]|=1<<i
    for i in range(7):
        if N>>i&1:edge(i,7+int(i>=3))
    edge(7,9);edge(9,10);edge(10,8)
    return {score(x)+8*((x>>7)&3) for x in range(1<<11) if not(x&127&~remain) and feas(A,x)}
planes={frozenset([a,b,c,a^b^c]) for a,b,c in combinations(range(32),3)}
assert len(planes)==1240
for N,expected in [(54,False),(86,True)]:
    J=joint(N)
    print('hood',N,'holes',sorted(set(range(32))-J))
    assert all(J&p for p in planes)
    assert [sum(1<<(x&7) for x in J if x>>3==i) for i in range(4)]==[223,127,223,255 if expected else 223]
    O=[r|((N>>i&1)<<7) for i,r in enumerate(G)]+[N]
    matches=[x for x in range(256) if feas(O,x) and score(x)==5]
    assert matches==([166] if expected else [])
    T={29,25,15,11}
    assert frozenset(T) in planes and joint(N,38)&T==({29} if expected else set())
print('all 1,240 planes verified, and mask-38 restriction distinguishes')
