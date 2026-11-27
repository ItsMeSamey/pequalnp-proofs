import json,gzip,re
from pathlib import Path
from collections import defaultdict,Counter
from pysat.card import CardEnc,EncType
from graphlib import TopologicalSorter,CycleError
D=Path('/dev/shm/team04-relaxed170-wide'); m=json.loads((D/'meta.json').read_bytes())
F=(1<<1024)-1; raw=[sum(1<<k for k in range(1024) if i in (k//32,32+k%32)) for i in range(64)]
v=raw[:]; op=lambda o,a,b:a&b if o=='and' else a|b if o=='or' else F^a
markers=[]
for i,g in enumerate(m['fixed'],64):
 a=g['inputs']; assert max(a)<i
 if g['op']=='not' and a[0]>=64:markers.append(i)
 v.append(op(g['op'],v[a[0]],v[a[-1]]))
assert markers[0]==m['marker'] and sum(((v[markers[0]]>>(33*i))&1)<<i for i in range(6))==53
assert {int(k,16):n for k,n in m['ports'].items()}=={x:i for i,x in enumerate(v)}
goal=int(m['goal'],16)
s=json.load(open('/tmp/pnp-official-20579-public.json'))['gap']['statement'];assert goal==sum(int(w,16)<<(32*i) for i,w in enumerate(re.findall(r'0x[0-9a-fA-F]+',s)))
S={int(t):(int(z,16),o,tuple(int(a,16) for a in aa)) for t,(z,o,aa) in m['selectors'].items()}; vals=sorted({z for z,o,aa in S.values()}); ids={z:i+1 for i,z in enumerate(vals)}; A=defaultdict(list); B=defaultdict(list); adj=defaultdict(set); by=defaultdict(list); cl=[[ids[goal]]]
for t,(z,o,aa) in S.items():
 assert op(o,aa[0],aa[-1])==z; A[z].append(t);cl.append([-t,ids[z]])
 for a in set(aa)-set(v):cl.append([-t,ids[a]]);B[a].append(t);adj[z].add(a);by[a,z].append(t)
for z in vals:
 cl.append([-ids[z],*A[z]])
 if z!=goal:cl.append([-ids[z],*B[z]])
norm=lambda c:Counter(tuple(sorted(q)) for q in c)
cy=set()
for z in vals:
 for a in adj[z]:
  for b in adj[a]:
   if b==z:
    for t in by[a,z]:
     for u in by[b,a]:cy.add(tuple(sorted((-t,-u))))
   elif z in adj[b]:
    for t in by[a,z]:
     for u in by[b,a]:
      for h in by[z,b]:cy.add(tuple(sorted((-t,-u,-h))))
r={'proved_static_cycles':[list(q) for q in cy], 'atmost':[(a,1) for z,a in sorted(A.items()) if len(a)>1]+[(list(ids.values()),139)]}

assert Counter((tuple(sorted(aa)),b) for aa,b in r['atmost'])==Counter([(tuple(sorted(a)),1) for a in A.values() if len(a)>1]+[(tuple(ids.values()),139)])
for q in r['proved_static_cycles']:
 ts=TopologicalSorter()
 for neg in q:
  assert neg<0;z,o,aa=S[-neg];ts.add(z,*aa)
 try:ts.prepare()
 except CycleError:pass
 else:raise ValueError(q)
cl+=r['proved_static_cycles'];top=max(S);reach={}
for z in vals:
 todo=[z]; seen=set()
 while todo:
  n=todo.pop()
  if n not in seen:seen.add(n);todo.extend(adj[n])
 reach[z]=seen
left=set(vals)
for z in vals:
 if z not in left:continue
 comp=sorted(y for y in reach[z] if z in reach[y]);left.difference_update(comp)
 if len(comp)==1:continue
 w=(len(comp)-1).bit_length();bits={}
 for n in comp:bits[n]=list(range(top+1,top+w+1));top+=w
 for n in comp:
  for a in sorted(adj[n]&set(comp)):
   wit=[]
   for k in range(w):
    top+=1;wit.append(top);cl.extend([[-top,-bits[a][k]],[-top,bits[n][k]]])
    for x,y in zip(bits[a][k+1:],bits[n][k+1:]):cl.extend([[-top,-x,y],[-top,x,-y]])
   for t in by[a,n]:cl.append([-t,*wit])
old=json.load(open('/dev/shm/team04-relaxed170-scc/meta.json')); ov=raw[:];neg=[]
for g in old['fixed']:
 aa=tuple(sorted(ov[i] for i in g['inputs']));z=op(g['op'],aa[0],aa[-1]);ov.append(z)
 if z not in v:neg.append(-next(t for t,r0 in S.items() if r0==(z,g['op'],aa)))
assert set(v)<=set(ov) and len(neg)==53
cl.append([ids[v[25]|v[36]],*neg])
for aa,b in r['atmost']:
 enc=CardEnc.atmost(aa,b,top_id=top,encoding=EncType.cardnetwrk);top=max(top,enc.nv);cl.extend(enc.clauses)
rows=(D/'branch-0000.cnf').read_text().splitlines();assert rows[0]==f'p cnf {top} {len(cl)}'
assert norm(cl)==norm([list(map(int,l.split()))[:-1] for l in rows[1:]])
print('full CNF clause multiset, physical fixed prefix and target verified',len(vals),len(S),len(cl),top)
d=json.load(gzip.open('/dev/shm/04-merged-terms/joint181-pool-plus-near180.json.gz')); truth=[int(s,16) for s in d['truth']]
assert truth[d['target']]==goal
recipes=defaultdict(set)
def add(z,o,aa):
 assert op(o,aa[0],aa[-1])==z
 if z not in v and z not in aa:recipes[z].add((o,tuple(sorted(aa))))
for i,o,*ii in d['recipes']:add(truth[i],o,[truth[j] for j in ii])
x=v[25]|v[36];add(x,'or',[v[25],v[36]])
for y in truth:
 for o in ('and','or'):
  z=op(o,x,y)
  if z in truth:add(z,o,[x,y])
if F^x in truth:add(F^x,'not',[x])
todo=[goal]; live=set()
while todo:
 z=todo.pop()
 if z in v or z in live:continue
 live.add(z)
 for o,aa in recipes[z]:todo.extend(aa)
assert set(S.values())=={(z,o,aa) for z in live for o,aa in recipes[z]}
print('archive recipes + one optional prefix reproduce exact selector set')
oldrecipes={(int(z,16),o,tuple(int(i,16) for i in aa)) for z,o,aa in old['selectors'].values()}
wideprefix=v[25]|v[36]
todo=[goal]; reachable=set()
while todo:
 z=todo.pop()
 if z in ov or z in reachable:continue
 reachable.add(z)
 for dst,o,aa in S.values():
  if dst!=z or wideprefix in aa or dst==wideprefix:continue
  assert (dst,o,aa) in oldrecipes
  todo.extend(aa)
assert len(set(ov)-set(v))==53
print('guard complement goal closure maps into fixed84 after prepaying 53 distinct released producers')
