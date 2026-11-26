from pathlib import Path
from collections import defaultdict,Counter
import gzip,json
P=Path(__file__).resolve().parent
F=(1<<64)-1;H=[sum(1<<i for i in range(64) if i>>j&1) for j in range(6)]
def read(f):return [list(map(int,x.split())) for x in (P/f).read_text().splitlines() if x.strip()]
def forest(us):
 b=[];par=[]
 for j,u in enumerate(us):
  par.append(-1 if u==F else b.index(u));b.extend([u&H[j],u&~H[j]])
 def rec(j):
  cs=[[],[]]
  for k,v in enumerate(par):
   if v>=0 and v//2==j:cs[v%2].append(rec(k))
  return '('+'/'.join(sorted(''.join(sorted(c)) for c in cs))+')'
 return ''.join(sorted(rec(j) for j,v in enumerate(par) if v<0))
allrows=defaultdict(set);hard=defaultdict(set);forestmap={};atomsizes={}
with gzip.open(P/'ten-canon.txt.gz','rt') as stream:
 for i,line in enumerate(stream):
  U=list(map(int,line.split()));bs=[u&h for j,u in enumerate(U) for h in (H[j],F^H[j])]
  atoms=[F]
  for b in bs:atoms=[s for a in atoms for s in (a&b,a&~b) if s]
  if len(atoms)<11:continue
  q=5-len(set(U)-set(bs)-{F});allrows[q].add(i);atomsizes[i]=len(atoms)
  if any(sum(not (a&u) for a in atoms)<=2 for u in set(U)-{F}):continue
  hard[q].add(i)
  if q==5:forestmap[forest(U)]=i
assert i+1==41719 and sum(map(len,allrows.values()))==41565
assert [len(allrows[q]) for q in range(1,6)]==[16118,18089,6314,964,80]
assert [len(hard[q]) for q in range(1,6)]==[4080,4482,1613,277,40]
r=read('all-1.tsv')
assert len(r)==len(allrows[1]) and {z[0] for z in r}==allrows[1] and all(z[1]==0 and z[2]==4 for z in r) and sum(z[3] for z in r)==1182449
for q,vis in [(1,311165),(2,3677096),(3,18472938),(4,53193416),(5,69188813)]:
 r=read(f'full-{q}.tsv')
 assert len(r)==len(hard[q]) and {z[0] for z in r}==hard[q]
 if q==1:
  assert not any(z[1] for z in r) and sum(z[3] for z in r)==vis
  continue
 assert all(z[1]==atomsizes[z[0]] for z in r) and sum(z[2] for z in r)==vis
 hits={z[0] for z in r if z[3]}
 assert len(hits)=={2:2,3:5,4:0,5:0}[q]
 if hits:
  rr=read(f'refined-{q}.tsv')
  assert len(rr)==len(hits) and {z[0] for z in rr}==hits and all(z[1]==0 and z[2]==5-q for z in rr)
orig=json.loads((P/'forest-original-order.json').read_text())
old=read('q5-late.tsv');new=read('q5-late-ids.tsv')
assert len(old)==len(new)==24
for x,y in zip(old,new):assert y==[forestmap[forest(list(map(int,orig[x[0]])))],*x[1:]]
print('41,719 original, 41,565 eleven-input orbits; all five ledger strata verified')
