from pysat.formula import IDPool
from pysat.solvers import Cadical195
from itertools import combinations
from pathlib import Path
def check(p,g,r):
 edges=[(1<<i)|(1<<j) for i in range(p) for j in range(i) if g>>(i*(i-1)//2+j)&1]
 cases=[(w,False) for w in edges]+[(w,True) for w in sorted({u|v for u,v in combinations(edges,2)})]
 ids=IDPool(); s=Cadical195()
 def andterm(slot,t,test,prev):
  z=ids.id(('z',slot,t)); penalties=[]
  for k in range(p+len(prev)):
   use=ids.id(('u',slot,k))
   if k<p:
    if not (test>>k&1):penalties.append(use)
   else:
    x=prev[k-p]
    bad=ids.id(('b',slot,t,k))
    s.add_clause([-bad,use]);s.add_clause([-bad,-x]);s.add_clause([bad,-use,x]); penalties.append(bad)
  for b in penalties:s.add_clause([-z,-b])
  s.add_clause([z]+penalties)
  return z
 for t,(v,target) in enumerate(cases):
  prev=[]
  for i in range(r):
   a=andterm(2*i,t,v,prev); b=andterm(2*i+1,t,v,prev)
   y=ids.id(('y',i,t));s.add_clause([-a,y]);s.add_clause([-b,y]);s.add_clause([a,b,-y]);prev.append(y)
  out=andterm(2*r,t,v,prev);s.add_clause([out if target else -out])
 ok=s.solve();s.delete();return ok
if __name__=='__main__':
 import sys
 for line in Path(sys.argv[1]).read_text().splitlines():
  p,g,r=map(int,line.split());print(p,g,r,int(check(p,g,r)),flush=True)
