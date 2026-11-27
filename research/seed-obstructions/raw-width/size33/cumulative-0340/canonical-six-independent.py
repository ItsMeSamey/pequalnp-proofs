from sample import samples
from pathlib import Path
import json
W,seed,target=samples(Path('L-meta-18968.json'))
P=[x for j,x in enumerate(W) if ((target&~seed)>>j)&1]
N=[x for j,x in enumerate(W) if not ((target>>j)&1)]
def extrema(v,maximal):
 s=set(v)
 return [x for x in s if not any(x!=y and ((x|y)==(y if maximal else x)) for y in s)]
for id,t,E,R,C in map(json.loads,open('remaining.jsonl')):
 if id not in (0,7,110,115):continue
 comps=[3<<i for i in range(6)]+[(1<<(3+i))|(1<<((9+i)%13)) for i in range(6)]
 comps+= [a|b for a,b in zip(comps[:6],comps[6:])]
 bank=list(range(20))+[20+comps.index(c) for c in C]
 def vec(row,bank):return sum(((row>>k)&1)<<j for j,k in enumerate(bank))
 oldP=extrema([vec(x,bank) for x in P],False);oldN=extrema([vec(x,bank) for x in N],True)
 def ok(row,fs,lo):
  v=vec(row,fs)
  return any((a&v)==(a if lo else v) for a in (oldP if lo else oldN))
 steps=[]
 for ix,k in enumerate(bank):
  for h in range(45):
   size=lambda j: 1 if j<13 else comps[j-20].bit_count() if 20<=j<38 else 0
   if h not in bank and size(h)>=size(k):continue
   if h==k:continue
   fs=bank[:];fs[ix]=h
   if all(ok(x,fs,False) for x in N) and all(ok(x,fs,True) for x in P):steps.append((ix,h))
 print(id,steps)
