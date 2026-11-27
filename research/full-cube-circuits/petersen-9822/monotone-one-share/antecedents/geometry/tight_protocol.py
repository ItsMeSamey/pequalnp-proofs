import json
from fractions import Fraction
from functools import cache
from pathlib import Path
E=[6,24,17,33,66,132,264,528,160,640,576,320,288]
Z=[50,77,108,116,139,201,208,276,387,402,523,525,554,556,771,773]
raw_weights=list(map(Fraction,json.loads(Path('kw-exact.json').read_text())['w']))
assert len(raw_weights)==208 and sum(raw_weights)==18 and all((2*x).denominator==1 for x in raw_weights)
w=[int(2*x) for x in raw_weights]
independent=lambda s: all(s&e!=e for e in E)
assert Z==[s for s in range(1024) if independent(s) and all(not independent(s|1<<v) for v in range(10) if not(s>>v&1))]
def bits(m):
 while m:
  b=m&-m;yield b;m^=b
def subs(m):
 t=m
 while t:
  yield t;t=(t-1)&m
def idx(b):return b.bit_length()-1
G=[]
for v in range(10):
 rows=sum(1<<j for j,e in enumerate(E) if e>>v&1)
 for r in subs(rows):
  cs=[sum(w[16*idx(b)+j] for b in bits(r)) if not z>>v&1 else -99 for j,z in enumerate(Z)]
  assert sum(max(x,0) for x in cs)<=2
  if sum(max(x,0) for x in cs)==2:
   G.append((r,sum(1<<j for j,c in enumerate(cs) if c>0),sum(1<<j for j,c in enumerate(cs) if c>=0)))
leaves=[[g for g in G if g[0]>>i&1 and g[2]>>j&1] for i in range(13) for j in range(16)]
def glue(blocks,m):
 if not m&(m-1):return
 more=[k for k in blocks if k&m]
 for k in more:blocks.remove(k);m|=k
 blocks.append(m)
def splits(groups):
 opts=[0]
 for g in groups[1:]:opts += [x|g for x in opts]
 return opts[1:]
checks=0
@cache
def solve(r,c):
 global checks
 checks+=1
 if any(R==r and not must&~c and not c&~C for R,must,C in G):return True
 rb=list(bits(r));cb=list(bits(c))
 for x in bits(r):
  for y in bits(c):
   rr,cc=r,c;found=False
   for R,must,C in leaves[16*idx(x)+idx(y)]:
    if not R&~r and not must&~c:
     rr&=R;cc&=must;found=True
   if not found:return False
   glue(rb,rr|x);glue(cb,cc|y)
 for side,groups in sorted([(0,rb),(1,cb)],key=lambda t:len(t[1])):
  for K in splits(groups):
   if side==0:
    if solve(K,c) and solve(r^K,c):return True
   else:
    if solve(r,K) and solve(r,c^K):return True
 return False
assert all(solve(r,c) for r,c,_ in G)
# Real two-leaf controls formed from disjoint row blocks with shared columns.
controls=0
for r1,m1,c1 in G:
 for r2,m2,c2 in G:
  c=m1|m2
  if not(r1&r2) and not(c&~(c1&c2)):
   assert solve(r1|r2,c)
   controls+=1
assert controls
print('two-leaf controls',controls)
solve.cache_clear();checks=0
print('templates',len(G),'weight',sum(w)/2,'18-leaf protocol',solve(8191,65535),'states',checks,flush=True)
