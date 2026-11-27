"""Independent numeric subroutines for q=8. Site false bit = rep bit XOR sign."""
from itertools import combinations
from random import Random
q=8
def lift(bits,sites):
 return [((bits>>i)&1)^s for i,s in sites]
def valid(bits,sites,pins):
 f=lift(bits,sites)
 return sum(f)==q and not any(f[i] for i in pins) and not any(f[a] and f[q+b] and f[2*q+(a^b)] for a in range(q) for b in range(q))
def fixed(sites,pins,allowed):
 opts={}
 for j,(r,s) in enumerate(sites):
  opts.setdefault(r,[0,0])
  for b in (0,1):
   w=b^s
   if w and (j in pins or not allowed[j]):opts[r][b]=None
   elif opts[r][b] is not None:opts[r][b]+=w
 dp={0:0}
 for r,ws in opts.items():
  dp={z+w:bits|(b<<r) for z,bits in dp.items() for b,w in enumerate(ws) if w is not None and z+w<=q}
 return dp.get(q)
def holes(sites,pins,dom,h):
 n=max(r for r,s in sites)+1
 constant=n+q
 for hole in combinations(range(3*q),h):
  eq=[]
  for j,((r,s),(t,u)) in enumerate(zip(sites,dom)):
   a=n+t if t is not None else constant
   if j in hole:eq.extend(((r,constant,s),(a,constant,u^1)))
   else:eq.append((r,a,s^u))
   if j in pins:eq.append((r,constant,s))
  # Eliminate binary equations with the special node interpreted as zero.
  rows={};consistent=True
  for r,a,v in eq:
   m=((1<<r)^(1<<a))&((1<<constant)-1)
   while m and m.bit_length() in rows:
    k,b=rows[m.bit_length()];m^=k;v^=b
   if m:rows[m.bit_length()]=(m,v)
   elif v:consistent=False;break
  if consistent:
   bits=0
   for k,(m,v) in sorted(rows.items()):
    if (bits&m).bit_count()%2!=v:bits|=1<<(k-1)
   return bits&((1<<n)-1)
def domains(h):
 return [(None,int(j<h)) if rail==0 else (j//h,rail-1) for rail in range(3) for j in range(q)]
def evaluate(dom,bits):
 return [s if t is None else (bits>>t&1)^s for t,s in dom]
rng=Random(143)
counts=[0,0]
for k in range(50):
 sites=[(rng.randrange(6),rng.randrange(2)) for _ in range(3*q)]
 pins={j for j in range(3*q) if rng.randrange(15)==0}
 if k%5==0: # planted Latin-safe nonempty-rail exact assignment
  f=[int(i in (0,9,10,11,20,21,22,23)) for i in range(24)]
  sites=[(j%6,s) for j,s in enumerate(f)]
  pins=set()
 truth=[b for b in range(64) if valid(b,sites,pins)]
 for h in (1,2):
  d=domains(h)
  allvals=[evaluate(d,s) for s in range(1<<(q//h))]
  expect=any(all(not v or allow for v,allow in zip(lift(b,sites),a)) for b in truth for a in allvals)
  got=holes(sites,pins,d,h)
  assert (got is not None)==expect and (got is None or got in truth)
  counts[int(expect)]+=1
 for allowed in ([0]*q+[1]*(2*q),evaluate(domains(4),1)):
  expect=any(all(not v or allow for v,allow in zip(lift(b,sites),allowed)) for b in truth)
  got=fixed(sites,pins,allowed)
  assert (got is not None)==expect and (got is None or got in truth)
  counts[int(expect)]+=1
# Only feasible model has mass 16, with third rail empty.
sites=[(0,int(i>=16)) for i in range(24)]
assert fixed(sites,{16},[1]*16+[0]*8) is None
# Identical signed component pinned to opposite truth values.
assert fixed([(0,0),(0,1)]*12,{0,1},[1]*24) is None
print('scoped NO/YES:',counts,'plus unattainable exact-mass and incompatible-pin controls')
