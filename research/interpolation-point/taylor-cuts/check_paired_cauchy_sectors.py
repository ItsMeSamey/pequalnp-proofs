from fractions import Fraction as F
from itertools import combinations, permutations, product
from math import prod

def perm(a):
    return sum(prod(r[j] for r,j in zip(a,p)) for p in permutations(range(len(a))))

def det(a):
    return sum((-1)**sum(p[i]>p[j] for i in range(len(p)) for j in range(i+1,len(p)))*prod(r[j] for r,j in zip(a,p)) for p in permutations(range(len(a))))

count=0
for n in range(1,6):
    for A,B in [(1,0),(2,1),(-1,2*n)]:
        for cut in range(n+1):
            x=[53+2*i if i<cut else 79+2*i for i in range(n)]
            nodes=[F(37+x[i]) if i<cut else F(37+x[i]-B,A) for i in range(n)]
            if len(set(nodes))<n:continue
            rowf=[F(1) if i<cut else F(1,A) for i in range(n)]
            C=[[1/(v-j) for j in range(n)] for v in nodes]
            E=[[F(1,37+x[i]-(j if i<cut else A*j+B)) for j in range(n)] for i in range(n)]
            expected=perm(E)
            total=0
            for left in combinations(range(n),cut):
                right=[j for j in range(n) if j not in left]
                total+=perm([[r[j] for j in left] for r in E[:cut]])*perm([[r[j] for j in right] for r in E[cut:]])
            assert expected==total==prod(rowf)*det([[z*z for z in r] for r in C])/det(C)
            count+=1
print(count,'affine paired-column permanent identities checked')
