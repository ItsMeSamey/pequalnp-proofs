from itertools import product, combinations_with_replacement
from math import factorial, prod
from sympy import Matrix, Rational

count = 0
for m in range(1,5):
 for r in range(1,5):
  for S in range(1<<m):
   size = S.bit_count()
   vals = Matrix(r,m,lambda i,j: Rational(1,7+i-j))
   direct = sum((-1)**((x&S).bit_count())*prod(sum(vals[i,j] for j in range(m) if x>>j&1) for i in range(r)) for x in range(1<<m))
   by_occ = 0
   if size<=r:
    for extra in combinations_with_replacement(range(m),r-size):
     mu=[(S>>j&1)+extra.count(j) for j in range(m)]
     cols=[(j,d) for j in range(m) for d in range(mu[j])]
     A=Matrix(r,r,lambda i,k: vals[i,cols[k][0]]**(cols[k][1]+1))
     B=Matrix(r,r,lambda i,k: (cols[k][1]+1)*vals[i,cols[k][0]]**(cols[k][1]+2))
     by_occ+=(-1)**size*2**(m-sum(t>0 for t in mu))*B.det()/A.det()/prod(factorial(t) for t in mu)
   assert direct==by_occ,(m,r,S,direct,by_occ)
   count+=1
print(count,'Walsh sectors verified')
