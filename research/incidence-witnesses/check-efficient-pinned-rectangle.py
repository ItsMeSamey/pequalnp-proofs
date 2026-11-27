"""Explicit PG(2,7) pin with r=4. Bit-parallel test of every physical gate resolution."""
from itertools import combinations
q=7
rows=(1,2,3,4)
points=[(x,y) for x in rows for y in range(q)]
lines=[(7,x) for x in rows]+[(m,c) for m in range(q) for c in range(q)]
P={p:i for i,p in enumerate(points)}; L={l:i+len(P) for i,l in enumerate(lines)}
def inc(p,l):return p[0]==l[1] if l[0]==7 else (p[1]-l[0]*p[0]-l[1])%q==0
def join(p,z):return next(l for l in lines if inc(p,l) and inc(z,l))
edges={(p,l) for p in points for l in lines if inc(p,l)}
n=len(points)+len(lines); gates=[]
def add(op,u,v):
 gates.append((op,u,v));return n+len(gates)-1
def collect(op,ls):
 it=iter(ls);u=next(it)
 for v in it:u=add(op,u,v)
 return u
A=collect('o',P.values());U=collect('o',L.values());B=add('a',A,U)
T=[(7,x) for x in rows];J=(7,1);t0=(7,2);m=(0,0);s=(2,0)
a=(2,4);b=(1,0);Jstar=[p for p in points if p[0]==1 or (p[0]!=1 and p[1]==p[0])]
reserved={(a,t0),(b,m)};ext=[];hl=[L[t0]];hp=[P[b]]
def own(terms):
 for e in terms:assert e in edges and e not in reserved;reserved.add(e)
for t in T:
 if t==t0:continue
 x=t[1];j=(x,2*x%q);d=(x,3*x%q)
 Z=add('o',P[a],L[t]);hl.append(Z); G=add('o',L[t],L[s])
 ext += [add('a',add('a',P[d],Z),G),add('a',P[j],G)]
 own([(d,t),(j,t),(j,s)])
for p in Jstar:
 if p==b: continue
 z=(3,0) if p[0]==1 else (4,0)
 g=join(p,z); own([(p,g),(z,g)])
 l=next(l for l in lines if inc(p,l) and l!=g and (p,l) not in reserved)
 own([(p,l)])
 V=add('o',L[m],P[p]);hp.append(V);G=add('o',P[p],P[z])
 ext += [add('a',add('a',L[l],V),G),add('a',L[g],G)]
terms=[collect('a',hl),collect('a',hp)]+ext
for p in points:
 rest=[L[l] for l in lines if (p,l) in edges-reserved]
 if rest:terms.append(add('a',P[p],collect('o',rest)))
out=add('a',B,collect('o',terms))
def mask(ps,ls):return sum(1<<P[p] for p in ps)+sum(1<<L[l] for l in ls)
positives={mask([p],[l]) for p,l in edges}
negatives={mask([],T),mask(Jstar,[])}
for p in points:
 off=[l for l in lines if (p,l) not in edges]; negatives.update(mask([p],ys) for k in (1,2) for ys in combinations(off,k))
for l in lines:
 off=[p for p in points if (p,l) not in edges];negatives.update(mask(xs,[l]) for xs in combinations(off,2))
for t in T:negatives.add(mask([next(p for p in points if inc(p,t))],[l for l in T if l!=t]))
for p in Jstar:
 l=next(l for l in lines if inc(p,l) and not any(inc(z,l) for z in Jstar if z!=p))
 negatives.add(mask([z for z in Jstar if z!=p],[l]))
tests=list(positives)+list(negatives);expected=(1<<len(positives))-1
raw=[]
for i in range(n):
 v=bytearray((len(tests)+7)//8)
 for j,w in enumerate(tests):
  if w>>i&1:v[j//8]|=1<<(j%8)
 raw.append(int.from_bytes(v,'little'))
def evaluate(gate=-1,side=0):
 vals=raw.copy()
 for i,(op,u,v) in enumerate(gates):
  vals.append(vals[(u,v)[side]] if gate==i else vals[u]&vals[v] if op=='a' else vals[u]|vals[v])
 return vals[out]
assert evaluate()==expected
for i in range(len(gates)):
 for side in (0,1):assert evaluate(i,side)!=expected,(i,side,gates[i])
print(len(points),len(lines),len(edges),len(gates),len(tests),2*len(gates))
