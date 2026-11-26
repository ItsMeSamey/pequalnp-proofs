"""Check the Grassmannian inverse and original-column basis coefficients."""
from itertools import combinations
from random import Random

def span(cols):
    s={0}
    for v in cols:
        s|={v^x for x in s}
    return frozenset(s)

P=sorted({span(p) for p in combinations(range(1,16),2)},key=sorted)
K=[[int(len(p&q)==1) for q in P] for p in P]
def invert(row,i):
    return sum(y*(2*K[i][j]+4*(i==j)-1) for j,y in enumerate(row))
for i in range(35):
    for j in range(35):
        assert invert(K[j],i)==16*(i==j)
rng=Random(401)
for r in range(4,8):
    for _ in range(100):
        E=[rng.randrange(1<<r) for _ in range(r-2)]
        J=span(E)
        bits=[len(span(E+list(q)))==1<<r for q in P]
        for i,p in enumerate(P):
            assert invert(bits,i)==16*(len(J)==1<<(r-2) and J&set(range(16))==p)
print('1225 inverse entries and 14000 physical coefficients passed')
