from itertools import combinations,product
import numpy as np
from scipy.optimize import linprog
C=np.array([[(-1 if i==j else 1 if (i-j)%5 in (1,4) else 0) for j in range(5)] for i in range(5)])
for k in range(1,6):
 for a in combinations(range(5),k):
  for b in combinations(range(5),k):assert abs(round(np.linalg.det(C[np.ix_(a,b)])))<=1
D=np.c_[np.eye(5,dtype=int),C]; rng=np.random.default_rng(951)
for trial in range(120):
 perm=rng.permutation(10);p=int(rng.integers(1,5));n=10-p
 H,J=D[:,perm[:n]],D[:,perm[n:]];w=rng.integers(1,15,size=n);best=float('inf')
 for tail in product((-1,1),repeat=p-1):
  e=np.array((1,)+tail)
  res=linprog(np.r_[w,w],A_eq=np.c_[H,-H],b_eq=-J@e,bounds=[(0,1)]*(2*n),method='highs')
  if res.success:
   v=np.rint(res.x[:n]-res.x[n:]).astype(int)%2
   assert np.all((H@v-J.sum(axis=1))%2==0);best=min(best,int(w@v))
 expect=min((sum(w*np.array(v)) for v in product((0,1),repeat=n) if np.all((H@v-J.sum(axis=1))%2==0)),default=float('inf'))
 assert best==expect
bits=list(product((0,1),repeat=4));energy=[]
for x in bits:
 z=np.zeros((3,3),dtype=int);z[:2,:2]=np.reshape(x,(2,2))
 z[:2,2]=(1+z[:2,:2].sum(axis=1))%2;z[2,:2]=(1+z[:2,:2].sum(axis=0))%2
 z[2,2]=(1+z[2,:2].sum())%2;assert np.all(z.sum(axis=0)%2==1)
 v=np.count_nonzero(z.sum(axis=0)==3)+np.count_nonzero(z.sum(axis=1)==3)
 assert v==z.sum()-3;energy.append(v)
cf=[sum(v*(-1)**(sum(a*b for a,b in zip(x,u))%2) for x,v in zip(bits,energy)) for u in bits]
assert sum(a!=0 for a in cf[1:])==9 and energy.count(0)==6
print('120 marked LP comparisons; R10 minors; K3,3 energy checked on 16 seeds, six models')
from itertools import permutations
edges=[(1<<i)^((1<<(3+j)) if j<2 else 0) for i in range(3) for j in range(3)]
target=set(edges+[31])
for basis in permutations(target,5):
 generated={0}
 for v in basis:generated|={u^v for u in generated}
 if len(generated)==32 and set(basis)|{basis[(i-1)%5]^basis[i]^basis[(i+1)%5] for i in range(5)}==target:break
else:raise AssertionError('Not the stated extension')
print('explicit R10 isomorphism, basis images',basis)
