from fractions import Fraction as F
from itertools import combinations,product
from math import prod
def val(x):return (abs(x)&-abs(x)).bit_length()-1
def run(L,cols,ids):
 T=2*L-1;h=F(prod(T-l for l in range(-L,L)),prod(-l for l in range(-L,L) if l))
 assert val(h.numerator)-val(h.denominator)==L.bit_length()
 rows=list(range(0,L,2));d=len(cols);N=max(ids)+1
 def coeff(x,I,j):
  y=cols[j]
  return F(prod(T+x-z for z in cols)*prod(T+s-y for s in I if s!=x),prod(s-x for s in I if s!=x)*prod(y-z for z in cols if z!=y))/h
 for bits in product((0,1),repeat=N):
  Q={x:sum(h*bits[e]/(T+x-y) for e,y in zip(ids,cols)) for x in rows}
  for I in combinations(rows,d):
   for j in range(d):assert sum(coeff(x,I,j)*Q[x] for x in I)==bits[ids[j]]
  def lift(target,old):
   if not target:return 1
   I=[r for r in rows if r not in old][:d];assert len(I)==d
   return sum(coeff(x,I,ids.index(target[0]))*Q[x]*lift(target[1:],old+[x]) for x in I)
  for k in range(N+1):
   for S in combinations(range(N),k):assert lift(S,[])==prod(bits[j] for j in S)
for args in [(8,[0,4],[0,1]),(16,[0,2,6],[0,1,2]),(16,[0,4,8],[0,1,0])]:run(*args)
print('All small exact Cauchy inverses and distinct-row products passed, including repeated logical bits')
