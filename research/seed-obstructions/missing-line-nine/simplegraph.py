from inputs import *
from itertools import combinations,permutations
from functools import reduce
from operator import and_
from pathlib import Path
import sys
def select(t,us):
 ordinary=list(us)+[x for x in range(7) if x not in {t,*us}]
 line=[1<<x for x in ordinary]+[(1<<t)|(1<<x) for x in us]
 pair={ij:1<<k for k,ij in enumerate(combinations(range(9),2))}
 e=lambda i,j:pair[tuple(sorted((i,j)))]
 def sig(raw):return sum(bool(l&raw)<<i for i,l in enumerate(line))
 def clique(h):return sum(edge for (i,j),edge in pair.items() if h>>i&h>>j&1)
 clauses=set()
 for n in N:
  touched=sum(bool(stars[l]&n)<<i for i,l in enumerate(ordinary));wrong=sig(n>>13)
  H=[]
  if not n&stars[t]:H.append(touched)
  for i in range(3):H.append((touched&~(1<<i))|(1<<(6+i)))
  opts=tuple(sorted({clique(h) for h in H if not h&wrong}))
  assert opts;clauses.add(opts)
 # Graph bit = AND. Each clause needs no AND edge in some allowed maxterm.
 forced_or=0;forced_and=clique(448)
 for opts in clauses:forced_or|=reduce(and_,opts)
 assert not forced_or&forced_and
 unknown=((1<<36)-1)^(forced_or|forced_and)
 forbidden=[]
 for a,b,c,d in permutations(range(9),4):
  if a>d:continue
  yes=e(a,b)|e(b,c)|e(c,d);no=e(a,c)|e(a,d)|e(b,d)
  if not yes&forced_or and not no&forced_and:forbidden.append((yes,no))
 print('unknown',unknown.bit_count(),'p4',len(forbidden),flush=True)
 survivors=[];bits=unknown
 while True:
  x=bits|forced_and
  if all(any(not x&r for r in cs) for cs in clauses) and not any(x&yes==yes and not x&no for yes,no in forbidden):survivors.append(x)
  if not bits:break
  bits=(bits-1)&unknown
 print('graphs',len(survivors),flush=True)
 return sorted(survivors)
if __name__=='__main__':
 t=int(sys.argv[1]);g=select(t,list(map(int,sys.argv[2:5])));Path(f'simple-{t}.txt').write_text(''.join(f'{v}\n' for v in g))
