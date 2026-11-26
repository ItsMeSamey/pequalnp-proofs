"""Lift a public ten-input 24-gate witness and export its exact raw/helper masks."""
from collections import defaultdict
from pathlib import Path
import json
from sys import argv
p=json.loads(Path(argv[1]).read_text())
g=[('OR',0,10)];remap={i:i for i in range(10)};remap[0]=11
for j,(op,a,b) in enumerate(p['gates']):
 g.append((op,remap[a],remap[b]));remap[10+j]=10+len(g)
g.append(('AND',0,10));g.append(('OR',remap[p['output']],10+len(g)))
out=10+len(g)
assert len(g)==27
for v in range(2048):
 w=[bool(v>>i&1) for i in range(11)]
 for op,a,b in g:w.append(w[a] and w[b] if op=='AND' else w[a] or w[b])
 assert w[out]==(v.bit_count()>=2)
ands=[11+j for j,(op,a,b) in enumerate(g) if op=='AND']
taps=defaultdict(list)
for j,v in enumerate(ands):
 _,a,b=g[v-11];taps[a].append(1<<(2*j));taps[b].append(2<<(2*j))
taps[out].append(1<<(2*len(ands)));signals={};joins={}
for v in reversed(range(11+len(g))):
 m,*tail=taps[v]
 for nxt in tail:
  z=m|nxt
  if z!=m and z!=nxt:joins.setdefault(z,(m,nxt))
  m=z
 if v>=11 and g[v-11][0]=='OR':
  _,a,b=g[v-11];taps[a].append(m);taps[b].append(m)
 else:signals[v]=m
assert all(signals[v]==1<<(2*len(ands)) for v in ands)
raw=[signals[i] for i in range(11)]
helper=sorted(set(joins)-set(raw),key=lambda x:(x.bit_count(),x))
assert len(set(raw))==11 and len(ands)<=7 and len(helper)<=6
print(len(ands),len(helper),*helper,*raw)
