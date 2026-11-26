from itertools import combinations
from pathlib import Path
from pysat.formula import CNF,IDPool
from pysat.card import CardEnc,EncType
from pysat.solvers import Solver
import sys
root=Path(__file__).parent
packings=[list(map(int,l.split())) for l in (root/'fourbit-packings.txt').read_text().splitlines()]
def solve(words,limit,budget):
 f=CNF();ids=IDPool()
 full=[sum(1<<(2*j+((w>>j)&1)) for j in range(4)) for w in words]
 pool=sorted({s for w in full for s in range(1,256) if not s&~w},key=int.bit_count)
 single={s for s in pool if s.bit_count()==1};g={s:ids.id(('gate',s)) for s in pool if s not in single}
 for s,t in g.items():
  decomps=[]
  for a,b in combinations([w for w in pool if w!=s and not w&~s],2):
   if a|b!=s:continue
   z=ids.id(('decomp',s,a,b));decomps.append(z)
   for w in (a,b):
    if w in g:f.append([-z,g[w]])
  f.append([-t]+decomps)
 f.extend(CardEnc.atmost(list(g.values()),bound=limit,vpool=ids,encoding=EncType.totalizer).clauses)
 cand=[]
 for i,word in enumerate(words):
  force=sum(1<<(2*j+((word>>j)&1)) for j in range(4) if (word^(1<<j)) in words)
  cand.append([s for s in pool if s&full[i]==s and s&force==force])
 ms={}
 for i in range(len(words)):
  for port in range(2):
   opts=[]
   for s in cand[i]:
    z=ids.id(('port',i,port,s));ms[i,port,s]=z;opts.append(z)
    if s in g:f.append([-z,g[s]])
   f.append(opts)
   for a,b in combinations(opts,2):f.append([-a,-b])
 for i in range(len(words)):
  for j in range(len(words)):
   for a in cand[i]:
    for b in cand[j]:
     if i==j:ok=(a|b)==full[i]
     else:ok=bool(a&(((b&85)<<1)|((b&170)>>1)))
     if not ok:f.append([-ms[i,0,a],-ms[j,1,b]])
 with Solver(name='cadical195',bootstrap_with=f.clauses) as solver:
  solver.conf_budget(budget)
  r=solver.solve_limited();model=set(solver.get_model() or []) if r else set()
  return r,solver.accum_stats()['conflicts'],[s for s,t in g.items() if t in model]
if __name__=='__main__':
 p=int(sys.argv[1]);lim=int(sys.argv[2]);budget=int(sys.argv[3]);seen=set()
 for i,P in enumerate(packings):
  words=sorted(m.bit_length()-1 for m in P if m.bit_count()==1)
  if len(words)!=p or tuple(words) in seen:continue
  seen.add(tuple(words));r,c,ms=solve(words,lim,budget);print(i,len(words),lim,r,c,ms,flush=True)
