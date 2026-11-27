"""Fixed activation profiles, exact chronological reverse OR budget."""
import json,sys
from pathlib import Path
from pysat.solvers import Cadical195
from itertools import combinations
from projected import E,N,fixture
def model(U,h):
 a=len(U);w=1<<a;F=(1<<w)-1
 rules=[];varno=0
 def var():
  nonlocal varno
  varno+=1;return varno
 def clause(*vs):rules.append(vs)
 t=var();clause(t)
 def fixed(u):return [t if u>>p&1 else -t for p in range(w)]
 time={(i,j):var() for i,j in combinations(range(a+h),2)}
 def before(i,j):return time[i,j] if i<j else -time[j,i]
 for i,j,k in combinations(range(a+h),3):
  x,y,v=before(i,j),before(j,k),before(i,k)
  clause(-x,-y,v);clause(x,y,-v)
 for i in range(a,a+h-1):clause(before(i,i+1))
 half=[sum(1<<p for p in range(w) if p>>j&1) for j in range(a)]
 B=[v for j,u in enumerate(U) for v in (u&(F^half[j]),u&half[j])]
 joins=[[var() for _ in range(w)] for j in range(h)]
 vals=[fixed(q) for q in [F]+B]+joins
 def prod(k):return (k-1)//2 if k<=2*a else k-1-a
 def pull(at,ks,out):
  opt={}
  for k in ks:
   q=var();opt[k]=q
   if at is not None and k:clause(-q,before(prod(k),at))
   for x,y in zip(out,vals[k]):
    if x!=y:clause(-q,-x,y);clause(-q,x,-y)
  clause(*opt.values());return opt
 for j,u in enumerate(U):
  if u!=F:pull(j,[k+1 for k,b in enumerate(B) if b==u and k//2!=j]+list(range(2*a+1,len(vals))),fixed(u))
 P=[]
 for j,J in enumerate(joins):
  arms=[[var() for _ in range(w)] for _ in range(2)]
  P.append([pull(a+j,range(1+2*a+j),X) for X in arms])
  for x,y,o in zip(*arms,J):clause(-x,o);clause(-y,o);clause(x,y,-o)
 raw=[[var() for _ in range(w)] for i in range(10)]
 Q=[pull(None,range(1,len(vals)),v) for v in raw]
 for i,j in E:
  for x,y in zip(raw[i],raw[j]):clause(x,y)
 for I in N:
  opts=[]
  for p in range(w):
   q=var();opts.append(q)
   for i,r in enumerate(raw):clause(-q,-r[p] if I>>i&1 else r[p])
  clause(*opts)
 return Cadical195(bootstrap_with=rules),P,Q
def control():
 g=fixture();n=6;w=1<<n;F=(1<<w)-1
 half=[sum(1<<p for p in range(w) if p>>j&1) for j in range(n)]
 uses=[[] for i in range(10+len(g))];uses[-1]=[0];vals=[F]+[0]*(2*n);U=[];joins=[];raw=[0]*10
 for i in reversed(range(len(uses))):
  k,*rest=uses[i]
  for t in rest:
   joins.append((k,t));vals.append(vals[k]|vals[t]);k=len(vals)-1
  if i<10:raw[i]=k;continue
  op,x,y=g[i-10]
  if op=='or':uses[x].append(k);uses[y].append(k)
  else:
   j=len(U);U.append(vals[k]);s=2*j+1;vals[s]=vals[k]&~half[j];vals[s+1]=vals[k]&half[j];uses[x].append(s);uses[y].append(s+1)
 assert len(joins)==9
 M,P,Q=model(U,9)
 assumptions=[v[k] for p,j in zip(P,joins) for v,k in zip(p,j)]+[v[k] for v,k in zip(Q,raw)]
 assert M.solve(assumptions=assumptions);M.delete()
 print('18-gate control six switches/nine joins accepted')
if __name__=='__main__':
 if len(sys.argv)==1:control()
 else:
  T=Path('/workspace/scratch/crown18264/algebra/reverse/canonfive.out').read_text().splitlines()
  for i in map(int,sys.argv[2:]):
   U=list(map(int,T[i].split()));S,P,Q=model(U,8);S.conf_budget(int(sys.argv[1]));status=S.solve_limited();print(i,status,S.accum_stats()['conflicts'],flush=True)
   if status is True:
    m=set(S.get_model());pick=lambda d:next(k for k,v in d.items() if v in m)
    Path(f'sat{i}.json').write_text(json.dumps([U,[[pick(d) for d in p] for p in P],[pick(d) for d in Q]]))
   S.delete()
