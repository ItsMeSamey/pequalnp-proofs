import collections,gzip,hashlib,json,sys
from pathlib import Path
from pysat.card import CardEnc, EncType
from pysat.formula import CNF
D=Path('/dev/shm/team04-relaxed170-wide')
env={'__name__':'stage'};sys.argv=['wide','--cap','170']
exec((D/'wide.py').read_text().split('if not args.solve:sys.exit()')[0],env)
N,sel,owners,m,P,goal,plans,truth,prefix=[env[x] for x in ('N','sel','owners','m','P','goal','plans','truth','prefix')]
old=json.loads(Path('/dev/shm/team04-relaxed170-scc/meta.json').read_bytes())['fixed']
ow,_=env['evalnet'](old)
change=[N[int(prefix['truth'],16)]]
for i,g in enumerate(old,64):
    z=ow[i]
    if z in P:continue
    op=g['op'];ins=tuple(sorted(ow[j] for j in g['inputs']))
    change.append(-owners[z,op,ins])
assert len(change)==54 and len(m['fixed_gates'])==31
adjsets=collections.defaultdict(list)
for t,(z,op,ins) in sel.items():
    for a in set(ins)&N.keys():adjsets[z].append((a,t))
cycles=set()
for z,arcs in list(adjsets.items()):
    for a,t in arcs:
        for b,u in adjsets[a]:
            if b==z:cycles.add(tuple(sorted((-t,-u))))
            elif b!=a:
                for c,v in adjsets[b]:
                    if c==z:cycles.add(tuple(sorted((-t,-u,-v))))
r=dict(clauses=env['cl'],proved_static_cycles=sorted(cycles),atmost=[[g,1] for g in env['atmost']]+[[list(N.values()),139]])
cl=list(r['clauses'])+r['proved_static_cycles'];top=max(abs(j) for row in cl for j in row)
adj={z:set() for z in N}
uses=collections.defaultdict(list)
for t,(z,op,ins) in sel.items():
 for a in set(ins)&N.keys():adj[z].add(a);uses[a,z].append(t)
# SCC membership computed via mutual reachability on this small fixed graph.
def reach(z):
 seen={z};stack=[z]
 while stack:
  x=stack.pop()
  for a in adj[x]-seen:seen.add(a);stack.append(a)
 return seen
reachable={z:reach(z) for z in N};taken=set();comps=[]
for z in sorted(N):
 if z in taken:continue
 comp=sorted(a for a in reachable[z] if z in reachable[a]);taken.update(comp)
 if len(comp)>1:comps.append(comp)
bits={};witness={};edges=0
for comp in comps:
 width=(len(comp)-1).bit_length();cs=set(comp)
 for z in comp:
  bits[z]=list(range(top+1,top+width+1));top+=width
 for z in comp:
  for a in sorted(adj[z]&cs):
   edges+=1;key=a,z;ws=[]
   # Witness k: a_k=0, z_k=1, and all more-significant bits agree.
   for k in range(width):
    top+=1;t=top;ws.append(t)
    cl.extend(([-t,-bits[a][k]],[-t,bits[z][k]]))
    for i in range(k+1,width):
     x,y=bits[a][i],bits[z][i];cl.extend(([-t,-x,y],[-t,x,-y]))
   for selector in uses[key]:cl.append([-selector,*ws])
   witness[key]=ws
# Independently transfer all four physically valid warm plans into SCC-order bits.
for plan,oldphase in zip(plans,env['phase']):
 active=set(oldphase);order={}
 def visit(z):
  if z in order or z in P:return
  for a in plan[z][1]:visit(a)
  order[z]=len(order)
 visit(goal)
 rank={}
 for c in comps:
  live=sorted((z for z in c if z in order),key=order.get)
  for i,z in enumerate(live):
   rank[z]=i;active.update(b for k,b in enumerate(bits[z]) if i>>k&1)
 for (a,z),ws in witness.items():
  if not any(j in active for j in uses[a,z]):continue
  assert rank[a]<rank[z];k=(rank[a]^rank[z]).bit_length()-1;active.add(ws[k])
 assert all(any((abs(x) in active)==(x>0) for x in row) for row in cl)
assert any((abs(i) in active)==(i>0) for i in change)
cl.append(change)
ph=list(sorted(active))
for lits,bound in r['atmost']:
 if len(lits)<=bound:continue
 enc=CardEnc.atmost(lits=lits,bound=bound,encoding=EncType.cardnetwrk,top_id=top)
 top=max(top,enc.nv);cl.extend(enc.clauses)
cnf=D/'base.cnf';CNF(from_clauses=cl).to_file(str(cnf));digest=hashlib.sha256(cnf.read_bytes()).hexdigest()
data=dict(model=digest,phase=ph,split=[N[int(prefix['truth'],16)],N[truth[328]],*sorted(N.values(),key=lambda i:-sum(abs(i) in row for row in r['clauses']))],
          marker=m['marker'],fixed=m['fixed_gates'],target=m['target'],ports={hex(z):i for z,i in P.items()},goal=hex(goal),
          selectors={t:[hex(z),op,[hex(a) for a in ins]] for t,(z,op,ins) in sel.items()})
(D/'meta.json').write_text(json.dumps(data))
summary=dict(fixed=len(m['fixed_gates']),budget=139,cap=170,scc_sizes=sorted(map(len,comps),reverse=True),internal_edges=edges,cnf_sha256=digest,clauses=len(cl),variables=top,static_cycle_clauses=len(cycles),change_guard=len(change),warm_verified=len(plans))
(D/'stage.json').write_text(json.dumps(summary));print(summary)
