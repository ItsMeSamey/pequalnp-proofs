"""Two sound projected relaxations; CNF output uses gate-pin multiplexers."""
from itertools import combinations
from pathlib import Path
import argparse,json
E=[(1,2),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(6,9),(6,8),(5,8)]
P=[(1<<i)|(1<<j) for i,j in E]
def value(x):return any(x&e==e for e in P)
N=[s for s in range(1024) if not value(s) and all(value(s|1<<i) for i in range(10) if not(s>>i&1))]
assert (len(P),len(N))==(13,16)
assert all(value(s)==(not any(s&~z==0 for z in N)) for s in range(1024))
def fixture():
 C=min((set(range(10))-set(i for i in range(10) if m>>i&1) for m in N),key=len)
 stars={i:[] for i in sorted(C)}
 for i,j in E:
  center=i if i in C else j;stars[center].append(i+j-center)
 g=[]
 def add(op,a,b):g.append((op,a,b));return 9+len(g)
 def merge(xs):
  a,*q=xs
  for b in q:a=add('or',a,b)
  return a
 out=merge([add('and',i,merge(neighbors)) for i,neighbors in stars.items() if neighbors])
 for s in range(1024):
  v=[bool(s>>i&1) for i in range(10)]
  for op,a,b in g:v.append((v[a] and v[b]) if op=='and' else (v[a] or v[b]))
  assert v[out]==value(s)
 assert len(g)==18
 return g
class CNF:
 def __init__(self):self.vars=0;self.cl=[]
 def new(self):self.vars+=1;return self.vars
 def clause(self,*args):self.cl.append(args)
def encode(k,rows,signed):
 c=CNF();true=c.new();c.clause(true);ws=[[(true if s>>i&1 else -true) for s in rows] for i in range(10)]
 # Input 10 is the constant-false wire; a complemented signed edge allows true as well.
 ws.append([-true]*len(rows))
 for g in range(k):
  ports=[]
  for p in range(2):
   z=[c.new() for _ in rows];sel=[]
   for vec in ws:
    for sign in ((1,-1) if signed else (1,)):
     t=c.new();sel.append(t)
     for u,v in zip(z,vec):
      v=sign*v;c.clause(-t,-u,v);c.clause(-t,u,-v)
   c.clause(*sel);ports.append(z)
  out=[c.new() for _ in rows];op=None if signed else c.new()
  for a,b,v in zip(*ports,out):
   guards=[] if signed else [-op]
   c.clause(*guards,-v,a);c.clause(*guards,-v,b);c.clause(*guards,v,-a,-b)
   if not signed:c.clause(op,v,-a);c.clause(op,v,-b);c.clause(op,-v,a,b)
  ws.append(out)
 # Padding AND(x,x) permits exactly k gates; signed output sign is free.
 sign=c.new() if signed else None
 for w,s in zip(ws[-1],rows):
  lit=w if value(s) else -w
  if signed:c.clause(-sign,lit);c.clause(sign,-lit)
  else:c.clause(lit)
 return c
if __name__=='__main__':
 parser=argparse.ArgumentParser();parser.add_argument('--write',action='store_true');opt=parser.parse_args()
 Path('upper18.json').write_text(json.dumps(fixture())+'\n')
 for signed in (False,True):
  probe=P+N
  if signed:probe=list(dict.fromkeys(probe+[0,1023]+[1<<i for i in range(10)]))
  c=encode(16 if signed else 17,probe,signed)
  print('signed',signed,'probes',len(probe),'variables',c.vars,'clauses',len(c.cl))
  if opt.write:Path('signed.cnf' if signed else 'mono.cnf').write_text(f'p cnf {c.vars} {len(c.cl)}\n'+''.join(' '.join(map(str,l))+' 0\n' for l in c.cl))
