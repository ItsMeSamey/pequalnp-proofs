"""Check partner capacities on the seven-pure-group thirteen-input candidate."""
from collections import defaultdict
from itertools import permutations
from pathlib import Path
import subprocess,tempfile
here=Path(__file__).resolve().parent
def build(name,d):
 exe=d/name
 subprocess.run(['c++','-std=c++20','-O3',here/(name+'.cpp'),'-o',exe],check=True)
 return exe
def patterns(models):
 classes=defaultdict(set)
 for line in models:
  p,g,clean,branch,quart,dirty=map(int,line.split())
  assert p==7 and 1<=dirty.bit_count()<=2
  edges=[(1<<i)|(1<<j) for i in range(p) for j in range(i) if g>>(i*(i-1)//2+j)&1]
  internal=edges.copy()
  for i in range(p):
   degree=sum((e>>i)&1 for e in internal)
   edges+=[1<<i]*(3+(quart>>i&1)-degree)
  assert len(edges)<=13
  edges += [0]*(13-len(edges))
  priv=[i for i in range(p) if not branch>>i&1]
  s=len(priv)
  assert 2<=s<=4
  if dirty.bit_count()==1:
   u=dirty.bit_length()-1
   for v in priv:
    if v==u:continue
    choices=[[u,v,*rest] for rest in permutations([x for x in priv if x not in [u,v]])]
    classes[s,1,0].add(min(signature(edges,branch,order) for order in choices))
  else:
   assert s in (2,3)
   for order in permutations(priv):
    d=sum(((dirty>>a)&1)<<i for i,a in enumerate(order))
    if s==2 or d in (3,5):classes[s,d,0].add(signature(edges,branch,order))
    if s==3 and d==3:classes[s,d,1].add(signature(edges,branch,order))
 return classes
def signature(edges,branch,order):
 return tuple(sorted((sum(((e>>i)&1)<<k for k,i in enumerate(order))<<2)|(e&branch).bit_count() for e in edges))
if __name__=='__main__':
 with tempfile.TemporaryDirectory() as path:
  d=Path(path)
  generator=build('quartet_models',d);check=build('double_kraft',d)
  result=subprocess.run([generator,'7','7'],capture_output=True,check=True)
  classes=patterns(result.stderr.decode().splitlines())
  for key,bank in sorted(classes.items()):
   data=''.join(' '.join(map(str,row))+'\n' for row in sorted(bank))
   proc=subprocess.run([check,*map(str,key)],input=data,capture_output=True,text=True,check=True)
   rows=[tuple(map(int,line.split())) for line in proc.stdout.splitlines()]
   assert [r[0] for r in rows]==list(range(len(bank))) and all(r[2]==0 for r in rows)
   print(*key,len(bank),sum(r[1] for r in rows),flush=True)
