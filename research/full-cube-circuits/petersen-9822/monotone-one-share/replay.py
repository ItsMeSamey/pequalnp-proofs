"""Enumerate inner formulas, then certify an exterior leaf lower bound for every survivor."""
import hashlib,json,tempfile,os,sys
from pathlib import Path
from collections import Counter
from functools import lru_cache
from pareto_help import main as generate
from pareto_filter import eligible
import outer_conflicts
from graph import E,Z,F
raw=[sum(1<<v for v in range(1024) if v>>i&1) for i in range(10)]
def signature(expr):
 def parse(i):
  if expr[i].isdigit():return raw[int(expr[i])],i+1
  assert expr[i]=='('
  a,j=parse(i+1);b,k=parse(j+1);assert expr[k]==')' and expr[j] in '&|'
  return (a&b if expr[j]=='&' else a|b),k+1
 h,end=parse(0);assert end==len(expr)
 code=sum(1<<i for i,e in enumerate(E) if h>>e&1)|sum(1<<(13+i) for i,z in enumerate(Z) if not h>>z&1)
 rawneed=0
 for b in (1<<i for i in range(10)):
  if any(not v&b and F[v]!=F[v|b] and h>>v&1==h>>(v|b)&1 for v in range(1024)):rawneed|=b
 return code,rawneed,h
def main():
 @lru_cache(None)
 def vertexcover(edges):
  if not edges:return 0
  return 1+min(vertexcover(tuple(q for q in edges if i not in q)) for i in edges[0])
 outer_conflicts.cover=lambda edges:vertexcover(tuple(edges))
 digest=hashlib.sha256()
 with tempfile.TemporaryDirectory() as d:
  os.chdir(d);generate()
  for k,front,left in ((6,3806,348),(7,6975,1048)):
   assert len(json.loads(Path(f'pareto-{k}.json').read_text()))==front
   es=eligible(k);assert len(es)==left
   ct=Counter()
   for code,(leaves,expr) in sorted(es.items()):
    c,need,h=signature(expr);assert c==code
    assert all(not(h>>(1<<i)&1) for i in range(10))
    lo=outer_conflicts.price(code,need)
    assert lo>19-leaves
    ct[lo]+=1;digest.update(f'{k} {code} {leaves} {need} {lo}\n'.encode())
   print('cost',k-1,'outer bounds',dict(sorted(ct.items())))
 print('sorted interface receipt',digest.hexdigest())
if __name__=='__main__':main()
