import itertools as it, collections, math
from functools import reduce
import numpy as np
def fullrank(S):
 basis={}
 for row in S.tolist():
  for j,b in sorted(basis.items()):
   if row[j]:
    row=[b[j]*x-row[j]*t for x,t in zip(row,b)]
    g=math.gcd(*row)
    if g:row=[x//g for x in row]
  j=next((j for j,x in enumerate(row) if x),None)
  if j is not None:basis[j]=row
  if len(basis)==S.shape[1]:return True
 return False

def candidates():
 for r,cap in [(1,1),(2,1),(3,1),(4,2),(5,3),(6,6)]:
  signs=np.array([(1,)+xs for xs in it.product((1,-1),repeat=r-1)],int)
  for D in range(1,cap+1):
   if D>cap:continue
   for a in it.combinations_with_replacement(range(1,cap+1),r):
    if math.gcd(D,*a)>1:continue
    z=signs@a
    ok=abs(z)==D
    S=signs[ok]
    if len(S)<r or not fullrank(S): continue
    yield r,D,a,S,z[ok]//D
if __name__=='__main__':
 c=collections.Counter((r,D) for r,D,*_ in candidates()); print(c)
def lattice(M,rhs,m):
 M=M.copy()%m;rhs=rhs.copy()%m
 while m>1 and len(rhs):
  loc=np.argwhere(M%2)
  if len(loc)==0:
   if any(rhs%2):return False
   M//=2;rhs//=2;m//=2;continue
  i,j=loc[0]
  M[[0,i]]=M[[i,0]];rhs[[0,i]]=rhs[[i,0]]
  M[:,[0,j]]=M[:,[j,0]]
  b=M[1:,0]*pow(int(M[0,0]),-1,m)%m
  rhs=(rhs[1:]-b*rhs[0])%m
  M=(M[1:,1:]-b[:,None]*M[0,1:])%m
 return True
if __name__=='__main__':
 survivors=[]
 for r,D,a,S,y in candidates():
  M=np.array([np.prod(S[:,[i for i in range(1,r) if b>>(i-1)&1]],axis=1,dtype=int) for b in range(1<<(r-1))]).T
  if not lattice(M,2*y,1<<(r-1)):survivors.append((r,D,a,len(y)))
 print('survivors:',len(survivors));print(*survivors,sep='\n')
