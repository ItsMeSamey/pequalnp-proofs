from pathlib import Path
from pysat.solvers import Solver
from pysat.card import CardEnc,EncType
from pysat.formula import IDPool
import argparse
a=argparse.ArgumentParser();a.add_argument('k',type=int);a.add_argument('width',type=int);a.add_argument('--budget',type=int,default=100000);x=a.parse_args()
from relations import constraints as rows
free={1<<i for i in range(13)}
for j in range(6):
 a=(1<<j)|(1<<(j+1));b=(1<<(j+3))|(1<<((j+9)%13));free.update((a,b,a|b))
free=sorted(free);pool=IDPool();new=pool.id;s=Solver(name='cadical195');add=s.add_clause
def atmost(v,k):
 for c in CardEnc.atmost(v,k,vpool=pool,encoding=EncType.seqcounter).clauses:add(c)
def choice(n):
 v=[new() for _ in range(n)];add(v);atmost(v,1);return v
def neg(y):return not y if type(y)is bool else -y
def clause(c):
 if not any(y is True for y in c):add([y for y in c if y is not False])
v=[[bool(m>>d&1) for d in range(13)] for m in free];gates=[]
for i in range(x.k):
 a=choice(len(v));b=choice(len(v));op=new()
 for j in range(len(v)):add([-a[j]]+b[j+1:])
 out=[]
 for d in range(13):
  t,w,z=new(),new(),new()
  for sel,mux in [(a,t),(b,w)]:
   for ind,row in zip(sel,v):u=row[d];clause([-ind,-mux,u]);clause([-ind,mux,neg(u)])
  for c in [[-op,-z,t],[-op,-z,w],[-op,z,-t,-w],[op,z,-t],[op,z,-w],[op,-z,t,w]]:add(c)
  out.append(z)
 v.append(out);gates.append((op,a,b))
used=[new() for _ in v];atmost(used,x.width)
if x.width==12 and x.k==4:
 for j in range(4):
  idx=len(free)+j;add([used[idx]])
  for m in free+[0]:add([(-q if m>>d&1 else q) for d,q in enumerate(v[idx])])
  if j:
   # Greedy lexicographic topological ordering: adjacent inversions require a direct edge.
   dep=[gates[j][1][idx-1],gates[j][2][idx-1]];old=v[idx-1];cur=v[idx];eq=[]
   for d in range(12,-1,-1):
    add(dep+[-q for q in eq]+[-old[d],cur[d]])
    same=new();add([-same,-old[d],cur[d]]);add([-same,old[d],-cur[d]]);add([same,old[d],cur[d]]);add([same,-old[d],-cur[d]]);eq.append(same)
 for i in range(4):
  for j in range(i):
   dif=[]
   for a,b in zip(v[31+i],v[31+j]):
    z=new();add([-z,a,b]);add([-z,-a,-b]);dif.append(z)
   add(dif)
for p,n in rows:
 cls=[used[i] for i,m in enumerate(free) if m&p and not m&n]
 for i in range(x.k):
  c=new();idx=i+len(free);add([-c,used[idx]]);add([-c,v[idx][p.bit_length()-1]])
  for j in range(13):
   if n>>j&1:add([-c,-v[idx][j]])
  cls.append(c)
 add(cls)
r=s.solve();print('width',x.width,'gates',x.k,'verdict',r,s.accum_stats(),flush=True)
if r:
 m=set(s.get_model());vals=free[:];net=[]
 for op,a,b in gates:
  l=next(i for i,g in enumerate(a) if g in m);r=next(i for i,g in enumerate(b) if g in m)
  vals.append(vals[l]&vals[r] if op in m else vals[l]|vals[r]);net.append((int(op in m),l,r))
 basis=[q for i,q in enumerate(vals) if used[i] in m];assert len(basis)<=x.width and all(any(z&p and not z&n for z in basis) for p,n in rows)
 print(basis,net)

assert r is False
