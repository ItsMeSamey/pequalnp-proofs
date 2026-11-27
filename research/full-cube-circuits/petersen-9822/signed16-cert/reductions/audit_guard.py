"""Direct 1024-row partial-proof replay for every candidate surviving the general cuts."""
from itertools import product
from pathlib import Path
edges=[(1,2),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(6,9),(6,8),(5,8)]
truth=tuple(any(((m>>x)&1) and ((m>>y)&1) for x,y in edges) for m in range(1024))
def sub(m):
 return [a for a in range(1024) if a&m==a]
def obstruction(S,T,U,i):
 svals=sub(S);ts=sub(T);ws=sub(U)
 for t in ts:
  before={}
  for s in svals:
   view=tuple(truth[s|t|w] for w in ws)
   pivot=next((w for w in ws if not w&i and truth[s|t|w]!=truth[s|t|w|i]),None)
   if pivot is not None:
    for row,(old,wold) in before.items():
     if row!=view:
      sep=next(w for w in ws if truth[s|t|w]!=truth[old|t|w])
      return t,old,s,wold,pivot,sep
    before[view]=s,pivot
 return None
def main():
 num=0
 for row in Path('three_bins.log').read_text().splitlines():
  if not row.startswith('survivor '):continue
  _,r,a,b,q,o,orders=row.split();R,*bs=map(int,(r,a,b,q,o))
  for order in orders.split(','):
   pred=R
   for j in map(int,order):
    s=bs[j];u=1023^(pred|s)
    cert=obstruction(s,pred,u,2<<j) if j<2 else None
    if cert:break
    pred|=s
   assert cert is not None
   print(R,*bs,order,j,*cert);num+=1
 print('direct witnesses',num)
if __name__=='__main__':main()
