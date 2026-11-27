"""Reconstruct and test a graph circuit from a reverse union/split witness."""
import json,sys
from projected import value,fixture
def forward(U,joins,receivers):
 n=len(U);w=1<<n;F=(1<<w)-1
 H=[sum(1<<p for p in range(w) if p>>j&1) for j in range(n)]
 vals={0:F};ops=[];todoS=set(range(n));todoJ=set(range(len(joins)))
 while todoS or todoJ:
  changed=False
  for j in sorted(todoS):
   k=next((k for k,m in vals.items() if m==U[j]),None)
   if k is None:continue
   a=2*j+1;b=a+1;ops.append(('split',k,a,b));vals[a]=U[j]&~H[j];vals[b]=U[j]&H[j];todoS.remove(j);changed=True
  for j in sorted(todoJ):
   a,b=joins[j]
   if a not in vals or b not in vals:continue
   k=1+2*n+j;ops.append(('union',k,a,b));vals[k]=vals[a]|vals[b];todoJ.remove(j);changed=True
  assert changed
 use={k:[] for k in vals};g=[]
 for i,k in enumerate(receivers):use[k].append(i)
 def gate(op,a,b):
  if a==b:return a
  if a is None:return b if op=='or' else None
  if b is None:return a if op=='or' else None
  g.append((op,a,b));return 9+len(g)
 def get(k):
  x=None
  for t in use[k]:x=gate('or',x,t)
  return x
 for op,k,a,b in reversed(ops):
  if op=='split':use[k].append(gate('and',get(a),get(b)))
  else:
   x=get(k);use[a].append(x);use[b].append(x)
 out=get(0);live={out}
 for i in reversed(range(10,10+len(g))):
  if i in live:live.update(g[i-10][1:])
 v={i:i for i in range(10)};ng=[]
 for i,(op,a,b) in enumerate(g,10):
  if i in live:v[i]=10+len(ng);ng.append((op,v[a],v[b]))
 for s in range(1024):
  x=[bool(s>>i&1) for i in range(10)]
  for op,a,b in ng:x.append(x[a] or x[b] if op=='or' else x[a] and x[b])
  assert x[v[out]]==value(s)
 return ng
def fixture_reverse():
 g=fixture();w=64;F=2**64-1;H=[sum(1<<p for p in range(w) if p>>j&1)for j in range(6)]
 uses=[[] for _ in range(28)];uses[-1]=[0];vals=[F]+[0]*12;U=[];joins=[];raw=[0]*10
 for i in reversed(range(28)):
  k,*rest=uses[i]
  for t in rest:joins.append((k,t));vals.append(vals[k]|vals[t]);k=len(vals)-1
  if i<10:raw[i]=k;continue
  op,a,b=g[i-10]
  if op=='or':uses[a].append(k);uses[b].append(k)
  else:
   j=len(U);U.append(vals[k]);s=2*j+1;vals[s]=vals[k]&~H[j];vals[s+1]=vals[k]&H[j];uses[a].append(s);uses[b].append(s+1)
 return U,joins,raw,[vals[x] for x in raw]
if __name__=='__main__':
 if len(sys.argv)>1:print(json.dumps(forward(*json.load(open(sys.argv[1])))))
 else:
  u,j,r,raw=fixture_reverse();assert len(forward(u,j,r))==18
  # All switches in this fixture have full activation; compressed and full masks coincide.
  from priced_masks import price
  rr=price(u,raw,9);assert rr and len(forward(*rr))==18
  print('18-gate reverse price and forward full-table control pass')
