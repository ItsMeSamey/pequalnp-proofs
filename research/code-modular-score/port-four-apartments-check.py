from itertools import combinations,combinations_with_replacement
planes=sorted({1|(1<<a)|(1<<b)|(1<<(a^b)) for a in range(1,16) for b in range(1,a)})
u=planes[0]; complements=[x for x in planes if x&u==1]
pairs=list(combinations_with_replacement(complements,2))
obs=[sum(1<<i for i,(v,w) in enumerate(pairs) if p&v==p&w==1) for p in planes if p!=u]
allbits=(1<<len(pairs))-1
P=[z for z in planes if z!=u]
def ort(x):
 return sum(1<<v for v in range(16) if all((v&j).bit_count()%2==0 for j in range(16) if x>>j&1))
def projection(x,p):
 return frozenset(min(v,v^p) for v in range(16) if x>>v&1)
for dual in (False,True):
 targets=[ort(x) if dual else x for x in [u]+P]
 a=targets[0]
 for p in range(1,16):
  if a>>p&1:continue
  pat=projection(a,p)
  for i,z in enumerate(targets[1:]):
   if projection(z,p)==pat:obs[i]|=1<<len(pairs)
  pairs.append(None)
allbits=(1<<len(pairs))-1

import itertools,sys
aps=set()
for b in itertools.combinations(range(1,16),4):
 vals={0}
 for x in b: vals|={v^x for v in vals}
 if len(vals)==16:
  aps.add(frozenset(1|(1<<x)|(1<<y)|(1<<(x^y)) for x,y in itertools.combinations(b,2)))
def valid(s):
 return set().union(*(a for a in aps if a<=s))==s
aU=[a for a in aps if u in a]
def rec(left,can,used,k):
 if not left:
  s={P[i] for i in used}|{u}
  if valid(s):print('FOUND',sorted(s),flush=True);return True
  if not k:return False
  opts=can
 else:
  if not k:return False
  if sum(sorted(((obs[i]&left).bit_count() for i in can),reverse=True)[:k])<left.bit_count():return False
  opts=min(([i for i in can if obs[i]>>j&1] for j in range(len(pairs)) if left>>j&1),key=len)
 banned=set()
 for i in opts:
  if rec(left&~obs[i],[z for z in can if z!=i and z not in banned],used+[i],k-1):return True
  banned.add(i)
 return False
# stabilizer transitive on apartments through U, fix one.
ap=aU[0]; ids=[P.index(z) for z in ap if z!=u]; left=allbits
for i in ids:left&=~obs[i]
for k in range(10,15):
 found=rec(left,[i for i in range(34) if i not in ids],ids,k-5)
 print("rivals",k,found)
 assert found == (k==14)

import collections,itertools
res=set()
def rec(left,can,used):
 if not left:
  res.add(tuple(sorted(used)));return
 slots=10-len(used)
 if slots==0:return
 can=[i for i in can if obs[i]&left]
 if sum(sorted(((obs[i]&left).bit_count() for i in can),reverse=True)[:slots])<left.bit_count():return
 bits=[j for j in range(len(pairs)) if left>>j&1]
 opts=min(([i for i in can if obs[i]>>j&1] for j in bits),key=len)
 banned=set()
 for i in opts:
  rec(left&~obs[i],[z for z in can if z!=i and z not in banned],used+[i])
  banned.add(i)
rec(allbits,list(range(34)),[])
print('sets',len(res),flush=True)
perms=[]
for b in itertools.permutations(range(1,16),4):
 a=[0]
 for x in b:a.extend([v^x for v in a])
 if len(set(a))<16:continue
 def mp(s):return sum(1<<a[j] for j in range(16) if s>>j&1)
 if mp(u)!=u:continue
 perms.append([P.index(mp(s)) for s in P])
print('stabilizer',len(perms))
orbits=[]
while res:
 s=min(res); orb={tuple(sorted(pi[i] for i in s)) for pi in perms}
 print('orbit',len(orb),s)
 assert not (orb-res)
 res-=orb;orbits.append((s,len(orb)))

def con(f):
 for l in [u]+P:
  c={z for z in f if (l&z)==1}
  if not c:continue
  seen={next(iter(c))}
  while True:
   grow=seen|{x for x in c if any((x&y).bit_count()>=2 for y in seen)}
   if grow==seen:break
   seen=grow
  if seen!=c:return False
 return True
for s,m in orbits:
 f={P[i] for i in s}
 print(m,con(f),con(f|{u}),sum(con(f|{z}) for z in P if z not in f),sum(z&u==1 for z in f))
