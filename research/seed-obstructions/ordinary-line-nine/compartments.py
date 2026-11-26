from edge import *
from pysat.solvers import Solver
from pysat.card import CardEnc
from pysat.formula import IDPool
from itertools import product
from functools import lru_cache
def test(a,b,t,u,loc,detail=False,threshold=6,no_or=False):
 ids=IDPool(); clauses=[]; sets=[{}, {}, {}]
 def new(x):return ids.id(x)
 def conn(kind,vs):
  v=new((kind,*vs))
  if kind=='&':
   clauses.extend([[-v,x] for x in vs]+[[v,*[-x for x in vs]]])
  else:
   clauses.extend([[v,-x] for x in vs]+[[-v,*vs]])
  return v
 def query(region,p,l,flag,endpoint=0):
  rr=[1<<t,1<<u,127^((1<<t)|(1<<u))]
  argument=p|((l&rr[region])<<13)|((flag&sum(1<<j for j in range(2) if loc[j]==region))<<20)|(endpoint<<22)
  return sets[region].setdefault(argument,new((region,argument)))
 def pattern(l):return bool(l&a)+2*bool(l&b)
 def root(p,l,flag):
  g=query(0,p,l,flag);h=query(1,p,l,flag)
  k0=query(2,p,l,flag);k1=query(2,p,l,flag,1)
  return conn('|',(k0,conn('&',(g,h,k1))))
 neg=set(ns);neg={ (p,l) for p,l in neg if not any((p,l)!=(q,m) and p&~q==0 and l&~m==0 for q,m in neg)}
 for p,l in neg:clauses.append([-root(p,l,pattern(l))])
 for j in range(7):
  for x in inside(ss[j]):clauses.append([root(1<<x,1<<j,pattern(1<<j))])
 # Degree-one root all's output false => j pivotal on this singleton.
 out=[]
 for j in range(7):
  if j in (t,u):continue
  for x in inside(ss[j]):out.append(root(1<<x,0,pattern(1<<j)))
 targets=[]
 for j,r in ((t,1),(u,0)):
  f=[query(r,1<<x,0,pattern(1<<j)) for x in range(13)]
  bad=conn('|',[f[x] for x in inside(8191^ss[j])]);fail=[-f[x] for x in inside(ss[j])]
  targets.append((bad,fail))
  for k in (1,2,3):
   several=conn('|',[conn('&',v) for v in combinations(fail,k)])
   out.append(conn('|',(bad,several)))
 if no_or:
  for p in range(13):
   for f in range(4): clauses.append([-query(2,1<<p,0,f,0)])
 for d in sets:
  for i,vi in d.items():
   for j,vj in d.items():
    if i!=j and not i&~j:clauses.append([-vi,vj])
 clauses.extend(CardEnc.atleast(out,threshold,vpool=ids).clauses)
 with Solver(name='cadical195',bootstrap_with=clauses) as s:
  sat=s.solve()
  if sat and detail:
   v=set(s.get_model());print('outer',sum(x in v for x in out[:-6]),'inner',[(b in v,sum(x in v for x in f)) for b,f in targets])
 return sat
if __name__=='__main__':
 a,b=3,13;t,u=failures(a,b)[0]
 for loc in product(range(3),repeat=2):print(loc,test(a,b,t,u,loc,True),flush=True)
