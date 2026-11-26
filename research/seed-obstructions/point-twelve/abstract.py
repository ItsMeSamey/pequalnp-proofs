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
 v.append([new() for _ in range(13)])
 if i:add([-v[-2][-1],v[-1][-1]])
used=[new() for _ in v];atmost(used,x.width)
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
 m=set(s.get_model());vals=free+[sum((z in m)<<j for j,z in enumerate(row)) for row in v[len(free):]]
 basis=[q for i,q in enumerate(vals) if used[i] in m];assert len(basis)<=x.width and all(any(z&p and not z&n for z in basis) for p,n in rows);print(basis)

assert r is False
