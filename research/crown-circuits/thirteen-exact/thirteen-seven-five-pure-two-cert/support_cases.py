from itertools import permutations,product
from collections import Counter
from pathlib import Path
def cases():
 for l in Path('types.tsv').read_text().splitlines():
  row,q,d,*E=map(int,l.split());I=E.copy()
  for v in (0,1,3,4,5):I += [1<<v]*(3+(q>>v&1)-sum(bool(e>>v&1) for e in E))
  I += [0]*(13-len(I)); assert len(I)==13
  B=[(m&7)|((1<<(3+i)) if m.bit_count()<2 else 0) for i,m in enumerate(I)]
  U=[m>>3 for m in I]
  opts=[[i for i in range(13) if U[i]>>j&1] if d>>(j+3)&1 else [-1] for j in range(3)]
  for hot in product(*opts):
   G=[sum((i==h)<<j for j,h in enumerate(hot)) for i in range(13)]
   T=[b|(g<<16) for b,g in zip(B,G)]
   if len(set(T))<13:continue
   req=[0]*13;disj=[]
   good=True
   for i in range(13):
    for j in range(13):
     if i==j or T[i]&~T[j]:continue
     m=(U[i]&~G[i])&~U[j]
     if not m:good=False;break
     if m.bit_count()==1:req[j]|=m
     else:disj.append((j,m))
    if not good:break
   if good:
    yield row,q,d,tuple(I),tuple(B),tuple(U),hot,tuple(G),tuple(req),tuple(disj)
if __name__=='__main__':
 C=Counter();R=set()
 for row,q,d,I,B,U,H,G,req,disj in cases():C[d.bit_count()]+=1;R.add(row)
 print(len(R),sum(C.values()),C)
