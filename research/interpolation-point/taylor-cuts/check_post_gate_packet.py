from fractions import Fraction as F
from itertools import product
from math import prod
def test(q):
 L=16;mod=2**120;T=1+2*L;h=F(prod(T-r for r in range(-L,L)),prod(-r for r in range(-L,L) if r))
 def red(a):return a.numerator*pow(a.denominator,-1,mod)%mod
 W=[[red(h/(T+i-y)) for y in range(L)] for i in range(L)]
 J=[q,q+2];I=[q+2*i for i in range(4)];guard={y-1 for y in J if y}
 def resp(s,v):
  a=[1]*L
  for i,b in zip(s,v):a[i]=b
  return [sum(c*d for c,d in zip(row,a))%mod for row in W]
 def lit(x,i):return x[i] if i<L-1 else 1-x[i]
 def OR(a,b):return (a+b-a*b)%mod
 fixed=resp([],[]);masks=list(product((0,1),repeat=4));X=list(product((0,1),repeat=2));aug=[]
 for z in masks:
  Q=resp([i+1 for i in I],z);assert tuple(Q[i]%2 for i in I)==z
  UA=prod(lit(Q,i) for i in range(L) if i not in I);assert UA%2
  line=[prod(1-Q[i] if b else Q[i] for i,b in zip(I,s))%mod for s in masks]
  for x in X:
   P=resp(J,x);UB=prod(lit(P,i) for i in range(L) if i not in I and i not in guard)
   UB*=prod(OR(P[i],fixed[i]) for i in guard)*prod(lit(fixed,i) for i in range(L) if i not in guard)
   assert UB%2
   G=UA*UB*prod(OR(P[i],Q[i]) for i in I)%mod
   line.append(G*pow(UA*UB,-1,mod)%mod)
  aug.append(line)
 for j in range(16):
  t=next(i for i in range(j,16) if aug[i][j]%2);aug[j],aug[t]=aug[t],aug[j]
  cinv=pow(aug[j][j],-1,mod);aug[j]=[b*cinv%mod for b in aug[j]]
  for i in range(16):
   if i!=j:
    u=aug[i][j];aug[i]=[(a-u*b)%mod for a,b in zip(aug[i],aug[j])]
 for s,line in zip(masks,aug):
  for val,x in zip(line[16:],X):
   P=resp(J,x);assert val==prod(P[i] for i,b in zip(I,s) if b)%mod
for q in (0,1):test(q)
print('Both orientations, all control masks, actual OR2 inversion mod 2^120')
